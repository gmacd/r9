#![allow(non_upper_case_globals)]

/// Recursive page table implementation for aarch64.
/// Note that currently there are a lot of assumptions that we're dealing with
/// 4KiB tables here, although it supports various sizes of pages.
use crate::{
    kmem::{boottext_range, bss_range, data_range, rodata_range, text_range},
    pagealloc::{self},
    param::KZERO,
    vm::{
        Entry, PageSize, PhysPageAllocator, RootPageTableType, VaMapping,
        init_empty_root_page_table, kernel_pagetable, user_pagetable,
    },
};
use port::{fdt::DeviceTree, mem::PhysRange};

#[cfg(not(test))]
use port::println;

pub unsafe fn init_kernel_page_tables(dt: &DeviceTree, dtb_physrange: PhysRange) {
    // We only use the first memory range for now.
    // TODO Handle multiple memory ranges
    let available_mem = dt
        .find_device_type("memory")
        .flat_map(|memory| dt.property_translated_reg_iter(memory).flat_map(|r| r.regblock()))
        .map(|memory| PhysRange::from(&memory))
        .next()
        .expect("No memory range found in device tree");
    println!("Physical Memory:");
    println!("  {}", &available_mem);

    // TODO leave the first page unmapped to catch null pointer dereferences in unsafe code
    let custom_map = {
        // The DTB range might not end on a page boundary, so round up.
        let dtb_page_size = PageSize::Page4K;
        let dtb_physrange = dtb_physrange.round(dtb_page_size.size());

        let text_physrange = boottext_range().add(&text_range());
        let ro_data_physrange = rodata_range();
        let data_physrange = data_range().add(&bss_range());

        let mut map = [
            ("DTB", dtb_physrange, Entry::ro_kernel_data(), dtb_page_size),
            ("Kernel Text", text_physrange, Entry::ro_kernel_text(), PageSize::Page2M),
            ("Kernel RO Data", ro_data_physrange, Entry::ro_kernel_data(), PageSize::Page2M),
            ("Kernel Data", data_physrange, Entry::rw_kernel_data(), PageSize::Page2M),
        ];
        map.sort_by_key(|a| a.1.start());
        map
    };

    println!("Memory map ranges:");

    let mut physpage_allocator = PhysPageAllocator {};

    // We use recursive page tables, but we have to be careful in the init call,
    // since the kpage_table is not currently pointed to by ttbr1_el1.  Any
    // recursive addressing of (511, 511, 511, 511) always points to the
    // physical address of the root page table, which isn't what we want here
    // because kpage_table hasn't been switched to yet.
    unsafe { init_empty_root_page_table(kernel_pagetable()) };

    for (name, range, flags, page_size) in custom_map.iter() {
        let mapped_virtrange = kernel_pagetable()
            .map_phys_range(
                &mut physpage_allocator,
                name,
                range,
                VaMapping::Offset(KZERO),
                *flags,
                *page_size,
                RootPageTableType::Kernel,
            )
            .expect("error:init:mapping failed");

        println!("  {:16}{} to {}", name, range, mapped_virtrange);
    }

    println!("Memory map details:");
    for (name, _, flags, page_size) in custom_map.iter() {
        println!("  {:16}flags: {:?} page_size: {:?}", name, flags, page_size);
    }

    if let Err(err) =
        pagealloc::free_unused_ranges(available_mem, custom_map.into_iter().map(|m| m.1.clone()))
    {
        panic!("error:Couldn't mark unused pages as free: err: {:?}", err);
    }
}

pub unsafe fn init_user_page_tables() {
    unsafe { init_empty_root_page_table(user_pagetable()) };
}
