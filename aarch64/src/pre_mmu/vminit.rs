use aarch64_cpu::{
    asm::barrier::{self, dsb},
    registers::*,
};
use port::{
    fdt::DeviceTree,
    mem::{PhysAddr, PhysRange},
    pagealloc::PageAllocError,
};

use crate::{
    kmem::{
        boottext_physrange, earlyvm_pages_physrange, rodata_physrange, rwdata_physrange,
        text_physrange,
    },
    param::KZERO,
    pre_mmu::util::{putstr, putu64h},
    vm::{
        AccessPermission, Entry, IdentityVmTrait, Mair, PageAllocator, PageSize, PageTableError,
        PhysPage4K, RootPageTable, RootPageTableType, Shareable, Table, VaMapping,
    },
};

#[unsafe(no_mangle)]
pub extern "C" fn init_vm(dtb_pa: u64) {
    // Parse the DTB before we set up memory so we can correctly map it
    let dt = unsafe { DeviceTree::from_usize(dtb_pa as usize).unwrap() };
    let dtb_physrange = PhysRange::with_pa_len(PhysAddr::new(dtb_pa), dt.size());

    putstr("\nvminit:init_vm: calling init_kernel_page_tables\n");

    // TODO leave the first page unmapped to catch null pointer dereferences in unsafe code
    let custom_map = {
        // The DTB range might not end on a page boundary, so round up.
        let dtb_page_size = PageSize::Page4K;
        let dtb_physrange = dtb_physrange.round(dtb_page_size.size());

        let text_physrange = boottext_physrange().span_with(text_physrange());
        let ro_data_physrange = rodata_physrange();
        let data_physrange = rwdata_physrange();

        let mut map = [
            ("DTB", dtb_physrange, Entry::ro_kernel_data(), dtb_page_size),
            ("Kernel Text", text_physrange, Entry::ro_kernel_text(), PageSize::Page2M),
            ("Kernel RO Data", ro_data_physrange, Entry::ro_kernel_data(), PageSize::Page2M),
            ("Kernel Data", data_physrange, Entry::rw_kernel_data(), PageSize::Page2M),
        ];
        map.sort_by_key(|a| a.1.start);
        map
    };

    let mut physpage_allocator = EarlyPageAllocator::new();

    let (root_page_table_pa, root_page_table) =
        if let Ok(page_pa) = physpage_allocator.alloc_physpage() {
            (page_pa, unsafe { &mut *(page_pa.0 as *mut RootPageTable) })
        } else {
            putstr("error:vminit:init_vm: failed to alloc root_kernelpt4\n");
            panic!();
        };
    root_page_table.entries[511] = Entry::empty()
        .with_phys_addr(root_page_table_pa)
        .with_accessed(true)
        .with_valid(true)
        .with_page_or_table(true);

    let mut vmtrait_impl = IdentityVmTrait::default();

    for (name, range, flags, page_size) in custom_map.iter() {
        putstr(name);
        putstr(" ");
        putu64h(range.start.addr());
        putstr("..");
        putu64h(range.end.addr());
        putstr(" -> ");

        match root_page_table.map_phys_range(
            &mut physpage_allocator,
            &mut vmtrait_impl,
            *range,
            VaMapping::Offset(KZERO),
            *flags,
            *page_size,
            RootPageTableType::Kernel,
        ) {
            Ok(mapped_virtrange) => {
                putu64h(mapped_virtrange.start as u64);
                putstr("..");
                putu64h(mapped_virtrange.end as u64);
                putstr("\n");
            }
            Err(err) => {
                putstr("error:vminit:init_vm: map_phys_range failed: ");
                putpagetableerror(&err);
                putstr("\n");
                panic!();
            }
        };
    }
    // puttable(&root_page_table);
    // let page_table1: &Table =
    //     unsafe { &*(root_page_table.entries[256].phys_addr().addr() as *const Table) };
    // puttable(page_table1);

    // let page_table2: &Table =
    //     unsafe { &*(page_table1.entries[0].phys_addr().addr() as *const Table) };
    // puttable(page_table2);

    // Early page tables for identity mapping the kernel physical addresses.
    // Once we've jumped to the higher half, this will no longer be used.

    let (physicalpt3_pa, physicalpt3) = if let Ok(page_pa) = physpage_allocator.alloc_physpage() {
        (page_pa, unsafe { &mut *(page_pa.0 as *mut Table) })
    } else {
        putstr("error:vminit:init_vm: failed to alloc physicalpt3\n");
        panic!();
    };
    //.quad	(0*2*GiB)
    // + (PT_BLOCK|PT_AF|PT_AP_KERNEL_RW|PT_ISH|PT_UXN|PT_MAIR_NORMAL)	// [0] (for kernel)
    physicalpt3.entries[0] = Entry::empty()
        .with_phys_addr(PhysAddr::new(0))
        .with_valid(true)
        .with_page_or_table(false)
        .with_accessed(true)
        .with_access_permission(AccessPermission::PrivRw)
        .with_shareable(Shareable::Inner)
        .with_uxn(true)
        .with_mair_index(Mair::Normal);

    let (physicalpt4_pa, physicalpt4) = if let Ok(page_pa) = physpage_allocator.alloc_physpage() {
        (page_pa, unsafe { &mut *(page_pa.0 as *mut RootPageTable) })
    } else {
        putstr("error:vminit:init_vm: failed to alloc physicalpt4\n");
        panic!();
    };
    //.quad	(physicalpt3)
    // + (PT_AF|PT_PAGE)	// [0] (for kernel)
    physicalpt4.entries[0] =
        Entry::empty().with_phys_addr(physicalpt3_pa).with_valid(true).with_page_or_table(true);

    // AArch64 memory management examples
    //  https://developer.arm.com/documentation/102416/0100

    // AArch64 Address Translation
    //  https://developer.arm.com/documentation/100940/0101

    // The kernel has been loaded at the entrypoint, but the
    // addresses used in the elf are virtual addresses in the higher half.
    // If we try to access them, the CPU will trap, so the next step is to
    // enable the MMU and identity map the kernel virtual addresses to the
    // physical addresses that the kernel was loaded into.

    // The Aarch64 is super flexible.  We can have page tables (granules)
    // of 4, 16, or 64KiB.  If we assume 4KiB granules, we would have:
    //  [47-39] Index into L4 table, used to get address of the L3 table
    //  [38-30] Index into L3 table, used to get address of the L2 table
    //  [29-21] Index into L2 table, used to get address of the L1 table
    //  [20-12] Index into L1 table, used to get address of physical page
    //  [11-0]  Offset into physical page corresponding to virtual address
    // L4-L1 simply refers to the page table with L1 always being the last
    // to be translated, giving the address of the physical page.
    // With a 4KiB granule, each index is 9 bits, so there are 512 (2^9)
    // entries in each table.  In this example the physical page would
    // also be 4KiB.

    // If we reduce the number of page tables from 4 to 3 (L3 to L1),
    // we have 21 bits [20-0] for the physical page offset, giving 2MiB
    // pages.  If we reduce to 2 tables, we have 30 bits [29-0], giving
    // 1GiB pages.

    // If we use 16KiB granules, the virtual address is split as follows:
    //  [46-36] Index into L3 table, used to get address of the L2 table
    //  [35-25] Index into L2 table, used to get address of the L1 table
    //  [24-14] Index into L1 table, used to get address of physical page
    //  [13-0]  Offset into physical page corresponding to virtual address
    // The 14 bits in the offset results in 16KiB pages.  Each table is
    // 16KiB, consisting of 2048 entries, so requiring 11 bits per index.
    // If we instead use only 2 levels, that gives us bits [24-0] for the
    // offset into the physical page, which gives us 32MiB page size.

    // Finally, if we use 64KiB granules, the virtual address is split as
    // follows:
    //  [41-29] Index into L2 table, used to get address of the L1 table
    //  [28-16] Index into L1 table, used to get address of physical page
    //  [15-0]  Offset into physical page corresponding to virtual address
    // The 16 bits in the offset results in 64KiB pages.  Each table is
    // 64KiB, consisting of 8192 entries, so requiring 13 bits per index.
    // If we instead use only 1 level, that gives us bits [28-0] for the
    // offset into the physical page, which gives us 512MiB page size.

    // The address of the top level table is stored in the translation table
    // base registers.  ttbr0_el1 stores the address for the user space,
    // ttbr1_el1 stores the address for the kernel, both for EL1.
    // By default, ttbr1_el1 is used when the virtual address bit 55 is 1
    // otherwise ttbr0_el1 is used.

    // Memory attributes are set per page table entry, and are hierarchical,
    // so settings at a higher page affect those they reference.

    // Set up root tables for lower (ttbr0_el1) and higher (ttbr1_el1)
    // addresses.  kernelpt4 is the root of the page hierarchy for addresses
    // of the form 0xffff800000000000 (KZERO and above), while physicalpt4
    // handles 0x0000000000000000 until KZERO.  Although what we really
    // want is to move to virtual higher half addresses, we need to have
    // ttbr0_el1 identity mapped during the transition until the PC is also
    // in the higher half.  This is because the PC is still in the lower
    // half immediately after the MMU is enabled.  Once we enter rust-land,
    // we can define a new set of tables.

    putstr("vminit:init_vm: switching\n");

    TTBR1_EL1.set(root_page_table_pa.addr());
    TTBR0_EL1.set(physicalpt4_pa.addr());

    TCR_EL1.write(
        TCR_EL1::IPS::Bits_44
            + TCR_EL1::TG1::KiB_4
            + TCR_EL1::SH1::Inner
            + TCR_EL1::ORGN1::WriteBack_ReadAlloc_WriteAlloc_Cacheable
            + TCR_EL1::IRGN1::WriteBack_ReadAlloc_WriteAlloc_Cacheable
            // + TCR_EL1::EPD1::SET
            + TCR_EL1::T1SZ.val(16)
            + TCR_EL1::TG0::KiB_4
            + TCR_EL1::SH0::Inner
            + TCR_EL1::ORGN0::WriteBack_ReadAlloc_WriteAlloc_Cacheable
            + TCR_EL1::IRGN0::WriteBack_ReadAlloc_WriteAlloc_Cacheable
            + TCR_EL1::T0SZ.val(16),
    );

    // Preset memory attributes.  This register stores 8 8-bit presets that are
    // referenced by index in the page table entries:
    //  [0] 0xff - Normal
    //  [1] 0x00 - Device (Non-gathering, non-reordering, no early write acknowledgement (most restrictive))
    MAIR_EL1.set(0x00ff);

    // https://forum.osdev.org/viewtopic.php?t=36412&p=303237
    #[cfg(not(test))]
    unsafe {
        // invalidate all TLB entries
        core::arch::asm!("tlbi vmalle1is")
    };

    dsb(barrier::ISH);

    putstr("vminit:init_vm: complete\n");
}

/// Print a PageTableError.  println! can't be used before the MMU is on.
fn putpagetableerror(err: &PageTableError) {
    match err {
        PageTableError::AllocationFailed(_) => putstr("out of early page table pages"),
        PageTableError::EntryIsNotTable(entry) => {
            putstr("entry is not a table: ");
            putu64h(entry.0);
        }
        PageTableError::PhysRangeIsZero => putstr("range is empty"),
        PageTableError::PhysRangeIsNotOnPageBoundary(_, page_size) => {
            putstr("range not aligned to page size ");
            putu64h(page_size.size() as u64);
        }
        PageTableError::MappingRecursiveIndex => putstr("va uses the recursive index"),
    }
}

struct EarlyPageAllocator {
    pages_pa: *mut PhysPage4K,
    num_pages: usize,
    next_page_idx: usize,
}

impl EarlyPageAllocator {
    fn new() -> Self {
        let earlyvm_pages_physrange = earlyvm_pages_physrange();
        let pages_start = earlyvm_pages_physrange.start.addr();
        let pages_pa = pages_start as *mut PhysPage4K;
        let num_pages = earlyvm_pages_physrange.size() / core::mem::size_of::<PhysPage4K>();

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
            let pa = PhysAddr::new(next_page as u64);
            Ok(pa)
        } else {
            putstr("error:vminit:alloc_physpage:Out of space");
            Err(PageAllocError::OutOfSpace)
        }
    }
}
