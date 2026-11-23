use port::Result;
use port::mem::{PhysRange, VirtRange};

use crate::vm::{PhysPageAllocator, VmTraitImpl};
use crate::{pagealloc, vm};

#[cfg(not(test))]
use port::println;

/// Map a device register to device memory
/// TODO Maybe make this a macro and wrap the error reporting?
pub fn map_device_register(physrange: PhysRange, page_size: vm::PageSize) -> Result<VirtRange> {
    let page_physrange = physrange.round(page_size.size());

    let mut physpage_allocator = PhysPageAllocator {};
    let mut vmtrait_impl = VmTraitImpl {};

    match vm::kernel_pagetable().map_phys_range(
        &mut physpage_allocator,
        &mut vmtrait_impl,
        page_physrange,
        vm::next_free_device_page4k(),
        vm::Entry::rw_device(),
        page_size,
        vm::RootPageTableType::Kernel,
    ) {
        Ok(virtrange) => {
            let offset = virtrange.start - page_physrange.start.addr() as usize;
            Ok(VirtRange::from_physrange(physrange, offset))
        }
        Err(err) => {
            println!("error:deviceutil:map_device_register:{page_physrange} {err:?}");
            Err("failed to map device register")
        }
    }
}

/// Map a buffer to device memory
/// TODO Maybe make this a macro and wrap the error reporting?
pub fn alloc_device_page(page_size: vm::PageSize) -> Result<(VirtRange, PhysRange)> {
    let page_pa = pagealloc::allocate_physpage().expect("couldn't allocate page");
    let page_physrange = PhysRange::with_pa_len(page_pa, page_size.size());

    let mut physpage_allocator = PhysPageAllocator {};
    let mut vmtrait_impl = VmTraitImpl {};

    match vm::kernel_pagetable().map_phys_range(
        &mut physpage_allocator,
        &mut vmtrait_impl,
        page_physrange,
        vm::next_free_device_page4k(),
        vm::Entry::rw_device(),
        page_size,
        vm::RootPageTableType::Kernel,
    ) {
        Ok(virtrange) => Ok((virtrange, page_physrange)),
        Err(err) => {
            println!("error:deviceutil:alloc_device_page:{page_physrange} {err:?}");
            Err("failed to map device buffer")
        }
    }
}
