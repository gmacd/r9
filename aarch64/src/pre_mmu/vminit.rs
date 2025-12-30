#![allow(non_upper_case_globals)]

use core::{panic, ptr::write_volatile};

/// Recursive page table implementation for aarch64.
/// Note that currently there are a lot of assumptions that we're dealing with
/// 4KiB tables here, although it supports various sizes of pages.
use crate::{
    pagealloc::{self},
    param::KZERO,
    pre_mmu::util::putstr,
    vm::{
        Entry, PageAllocator, PageSize, PhysPage4K, RootPageTable, RootPageTableType, Table,
        VaMapping, VmTrait,
    },
};
use port::{
    fdt::DeviceTree,
    mem::{PhysAddr, PhysRange},
    pagealloc::PageAllocError,
};

#[cfg(not(test))]
use port::println;

// These map to definitions in kernel.ld.
// In pre-MMU state, these will all map to physical addresses on aarch64.
unsafe extern "C" {
    static eboottext: [u64; 0];
    static text: [u64; 0];
    static etext: [u64; 0];
    static rodata: [u64; 0];
    static erodata: [u64; 0];
    static data: [u64; 0];
    static edata: [u64; 0];
    static bss: [u64; 0];
    static ebss: [u64; 0];
    // static end: [u64; 0];
    static early_pagetables: [u64; 0];
    static eearly_pagetables: [u64; 0];
}

fn base_physaddr() -> PhysAddr {
    PhysAddr::new(0)
}

fn eboottext_physaddr() -> PhysAddr {
    unsafe { PhysAddr::new(eboottext.as_ptr().addr() as u64) }
}

fn text_physaddr() -> PhysAddr {
    unsafe { PhysAddr::new(text.as_ptr().addr() as u64) }
}

fn etext_physaddr() -> PhysAddr {
    unsafe { PhysAddr::new(etext.as_ptr().addr() as u64) }
}

fn rodata_physaddr() -> PhysAddr {
    unsafe { PhysAddr::new(rodata.as_ptr().addr() as u64) }
}

fn erodata_physaddr() -> PhysAddr {
    unsafe { PhysAddr::new(erodata.as_ptr().addr() as u64) }
}

fn data_physaddr() -> PhysAddr {
    unsafe { PhysAddr::new(data.as_ptr().addr() as u64) }
}

fn edata_physaddr() -> PhysAddr {
    unsafe { PhysAddr::new(edata.as_ptr().addr() as u64) }
}

fn bss_physaddr() -> PhysAddr {
    unsafe { PhysAddr::new(bss.as_ptr().addr() as u64) }
}

fn ebss_physaddr() -> PhysAddr {
    unsafe { PhysAddr::new(ebss.as_ptr().addr() as u64) }
}

fn early_pagetables_physaddr() -> PhysAddr {
    unsafe { PhysAddr::new(early_pagetables.as_ptr().addr() as u64) }
}

fn eearly_pagetables_physaddr() -> PhysAddr {
    unsafe { PhysAddr::new(eearly_pagetables.as_ptr().addr() as u64) }
}

fn boottext_physrange() -> PhysRange {
    PhysRange(base_physaddr()..eboottext_physaddr())
}

fn text_physrange() -> PhysRange {
    PhysRange(text_physaddr()..etext_physaddr())
}

fn rodata_physrange() -> PhysRange {
    PhysRange(rodata_physaddr()..erodata_physaddr())
}

fn data_physrange() -> PhysRange {
    PhysRange(data_physaddr()..edata_physaddr())
}

fn bss_physrange() -> PhysRange {
    PhysRange(bss_physaddr()..ebss_physaddr())
}

pub fn early_pages_physrange() -> PhysRange {
    PhysRange::new(early_pagetables_physaddr(), eearly_pagetables_physaddr())
}

#[unsafe(no_mangle)]
pub extern "C" fn init_vm(dtb_pa: u64) {
    // Parse the DTB before we set up memory so we can correctly map it
    let dt = unsafe { DeviceTree::from_usize(dtb_pa as usize).unwrap() };
    let dtb_physrange = PhysRange::with_pa_len(PhysAddr::new(dtb_pa), dt.size());

    putstr("\nvm init: calling init_kernel_page_tables\n");
    unsafe { init_kernel_page_tables(&dt, dtb_physrange) };
    putstr("vm init: init_kernel_page_tables complete\n");
    // vm::switch(vm::kernel_pagetable(), RootPageTableType::Kernel);

    putstr("vm init: calling init_user_page_tables\n");
    // unsafe { init_user_page_tables() };
    // init_early_uart_putstr("vm init: init_user_page_tables complete\n");
    // vm::switch(vm::user_pagetable(), RootPageTableType::User);

    putstr("vm init: complete\n");
}

pub unsafe fn init_kernel_page_tables(dt: &DeviceTree, dtb_physrange: PhysRange) {
    // We only use the first memory range for now.
    // TODO Handle multiple memory ranges
    let available_mem = dt
        .find_device_type("memory")
        .flat_map(|memory| dt.property_translated_reg_iter(memory).flat_map(|r| r.regblock()))
        .map(|memory| PhysRange::from(&memory))
        .next();
    let available_mem = match available_mem {
        Some(m) => m,
        None => {
            putstr("error:vminit:init_kernel_page_tables:No memory range found in device tree");
            panic!();
        }
    };

    //.expect("No memory range found in device tree");
    putstr("Physical Memory\n");

    // TODO leave the first page unmapped to catch null pointer dereferences in unsafe code
    let custom_map = {
        // The DTB range might not end on a page boundary, so round up.
        let dtb_page_size = PageSize::Page4K;
        let dtb_physrange = dtb_physrange.round(dtb_page_size.size());
        let text_physrange = boottext_physrange().add(&text_physrange());
        putstr("4\n");
        let ro_data_physrange = rodata_physrange();
        putstr("5\n");
        let data_physrange = data_physrange().add(&bss_physrange());
        putstr("6\n");

        let mut map = [
            ("DTB", dtb_physrange, Entry::ro_kernel_data(), dtb_page_size),
            ("Kernel Text", text_physrange, Entry::ro_kernel_text(), PageSize::Page2M),
            ("Kernel RO Data", ro_data_physrange, Entry::ro_kernel_data(), PageSize::Page2M),
            ("Kernel Data", data_physrange, Entry::rw_kernel_data(), PageSize::Page2M),
        ];
        map.sort_by_key(|a| a.1.start());
        map
    };

    putstr("Memory map ranges\n");

    let mut physpage_allocator = EarlyPageAllocator::new();
    let mut vm_guts = EarlyVmGuts {};
    putstr("7\n");

    // Create root pagetables
    let kernel_root_page_table = match physpage_allocator.alloc_physpage() {
        Ok(pa) => unsafe { &mut *(pa.addr() as *mut RootPageTable) },
        Err(_) => {
            putstr("error:vminit:init_kernel_page_tables:Couldn't allocate kernel root page table");
            panic!();
        }
    };
    putstr("8\n");

    let user_root_page_table = match physpage_allocator.alloc_physpage() {
        Ok(p) => p,
        Err(_) => {
            putstr("error:vminit:init_kernel_page_tables:Couldn't allocate user root page table");
            panic!();
        }
    };

    // We use recursive page tables, but we have to be careful in the init call,
    // since the kpage_table is not currently pointed to by ttbr1_el1.  Any
    // recursive addressing of (511, 511, 511, 511) always points to the
    // physical address of the root page table, which isn't what we want here
    // because kpage_table hasn't been switched to yet.
    init_empty_root_page_table(kernel_root_page_table);
    putstr("9\n");

    for (name, range, flags, page_size) in custom_map.iter() {
        let mapped_virtrange = kernel_root_page_table.map_phys_range(
            &mut physpage_allocator,
            &mut vm_guts,
            name,
            range,
            VaMapping::Offset(KZERO),
            *flags,
            *page_size,
            RootPageTableType::Kernel,
        );
        if mapped_virtrange.is_err() {
            putstr("error:vminit:init_kernel_page_tables:Mapping failed");
            panic!();
        }
    }

    putstr("Memory map details\n");

    if let Err(_) =
        pagealloc::free_unused_ranges(available_mem, custom_map.into_iter().map(|m| m.1.clone()))
    {
        putstr("error:vminit:init_kernel_page_tables:Couldn't mark unused pages as free");
        panic!();
    }
}

// pub unsafe fn init_user_page_tables() {
//     unsafe { init_empty_root_page_table(user_pagetable()) };
// }

/// Given an empty, statically allocated page table.  We need to write a
/// recursive entry in the last entry.  To do this, we need to know the physical
/// address, but all we have is the virtual address
pub fn init_empty_root_page_table(root_page_table: &mut RootPageTable) {
    unsafe {
        let entry = Entry::rw_kernel_data()
            .with_phys_addr(PhysAddr::new(root_page_table as *const _ as u64))
            .with_page_or_table(true);
        write_volatile(&mut root_page_table.entries[511], entry);
    }
}

struct EarlyPageAllocator {
    pages_pa: *mut PhysPage4K,
    num_pages: usize,
    next_page_idx: usize,
}

impl EarlyPageAllocator {
    fn new() -> Self {
        let early_pages_physrange = early_pages_physrange();
        let pages_start = early_pages_physrange.start().addr();
        let pages_pa = pages_start as *mut PhysPage4K;
        let num_pages = early_pages_physrange.size() / core::mem::size_of::<PhysPage4K>();
        for i in 0..num_pages {
            unsafe { (*pages_pa.add(i)).clear() };
        }

        Self { pages_pa, num_pages, next_page_idx: 0 }
    }
}

impl PageAllocator for EarlyPageAllocator {
    fn alloc_physpage(&mut self) -> Result<PhysAddr, PageAllocError> {
        if self.next_page_idx < self.num_pages {
            let next_page = unsafe { self.pages_pa.add(self.next_page_idx) };
            self.next_page_idx += 1;
            Ok(PhysAddr::new(next_page as u64))
        } else {
            putstr("error:alloc_physpage:Out of space");
            Err(PageAllocError::OutOfSpace)
        }
    }
}

#[derive(Clone, Copy)]
pub struct EarlyVmGuts {}

impl VmTrait for EarlyVmGuts {
    fn write_entry(&self, dest_entry: &mut Entry, entry: Entry) {
        unsafe { write_volatile(dest_entry, entry) };
    }

    fn replace_recursive_entry(&mut self, pgtype: RootPageTableType, entry: Entry) -> Entry {
        // let old_recursive_entry = root_page_table(pgtype).entries[511];
        // self.write_recursive_entry(pgtype, entry);
        // old_recursive_entry
        entry
    }

    fn write_recursive_entry(&mut self, pgtype: RootPageTableType, entry: Entry) {
        // let page_table = root_page_table(pgtype);
        // // Return the recursive entry to its original state
        // unsafe { write_volatile(&mut page_table.entries[511], entry) };
    }

    fn generate_temp_recursive_address(&self, table: &Table) -> Entry {
        Entry::rw_kernel_data()
            .with_phys_addr(PhysAddr::new(table as *const _ as u64))
            .with_page_or_table(true)
    }
}
