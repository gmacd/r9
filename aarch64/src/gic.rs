use core::cell::SyncUnsafeCell;

use crate::deviceutil::map_device_register;
use crate::io::{read_reg, write_reg};
use crate::vm;
use port::fdt::DeviceTree;
use port::mem::{PhysRange, VirtRange};

#[cfg(not(test))]
use port::println;

// GICD (Distributor) register offsets
const GICD_CTLR: usize = 0x000;
const GICD_ISENABLER: usize = 0x100;
const GICD_IPRIORITYR: usize = 0x400;

// GICC (CPU Interface) register offsets
const GICC_CTLR: usize = 0x000;
const GICC_PMR: usize = 0x004;
const GICC_IAR: usize = 0x00C;
const GICC_EOIR: usize = 0x010;

// Non-secure EL1 Physical Timer PPI: DTS id=14 => GIC INTID = 16+14 = 30
pub const TIMER_IRQ: u32 = 30;

static GICC: SyncUnsafeCell<Option<VirtRange>> = SyncUnsafeCell::new(None);

pub fn init(dt: &DeviceTree) {
    let (gicd_phys, gicc_phys) = match find_gic_physranges(dt) {
        Ok(ranges) => ranges,
        Err(msg) => {
            println!("gic: can't find GIC in device tree: {msg:?}");
            return;
        }
    };

    let gicd_virt = match map_device_register("gicd", gicd_phys, vm::PageSize::Page4K) {
        Ok(vr) => vr,
        Err(msg) => {
            println!("gic: can't map GICD: {msg:?}");
            return;
        }
    };

    let gicc_virt = match map_device_register("gicc", gicc_phys, vm::PageSize::Page4K) {
        Ok(vr) => vr,
        Err(msg) => {
            println!("gic: can't map GICC: {msg:?}");
            return;
        }
    };

    init_distributor(&gicd_virt);
    init_cpu_interface(&gicc_virt);
    enable_interrupt(&gicd_virt, TIMER_IRQ);

    unsafe {
        *GICC.get() = Some(gicc_virt);
    }

    println!("gic: initialised, timer IRQ {TIMER_IRQ} enabled");
}

fn find_gic_physranges(dt: &DeviceTree) -> port::Result<(PhysRange, PhysRange)> {
    let node = dt.find_compatible("arm,gic-400").next().ok_or("can't find arm,gic-400")?;
    let mut regs = dt.property_translated_reg_iter(node);

    let gicd_reg = regs.next().and_then(|r| r.regblock()).ok_or("can't find GICD reg")?;
    let gicc_reg = regs.next().and_then(|r| r.regblock()).ok_or("can't find GICC reg")?;

    Ok((PhysRange::from(&gicd_reg), PhysRange::from(&gicc_reg)))
}

fn init_distributor(gicd: &VirtRange) {
    // Disable distributor while configuring
    write_reg(gicd, GICD_CTLR, 0);

    // Set priority for timer interrupt to 0 (highest)
    let reg_offset = GICD_IPRIORITYR + (TIMER_IRQ as usize / 4) * 4;
    let shift = (TIMER_IRQ % 4) * 8;
    let val = read_reg(gicd, reg_offset);
    write_reg(gicd, reg_offset, val & !(0xFF << shift));

    // Enable distributor
    write_reg(gicd, GICD_CTLR, 1);
}

fn init_cpu_interface(gicc: &VirtRange) {
    // Set priority mask to allow all priorities
    write_reg(gicc, GICC_PMR, 0xFF);

    // Enable CPU interface
    write_reg(gicc, GICC_CTLR, 1);
}

fn enable_interrupt(gicd: &VirtRange, irq: u32) {
    let reg_offset = GICD_ISENABLER + (irq as usize / 32) * 4;
    let bit = 1u32 << (irq % 32);
    write_reg(gicd, reg_offset, bit);
}

/// Read the Interrupt Acknowledge Register to get the pending interrupt ID.
/// Returns None for spurious interrupts (ID 1023).
pub fn acknowledge_interrupt() -> Option<u32> {
    let gicc = unsafe { &*GICC.get() }.as_ref()?;
    let iar = read_reg(gicc, GICC_IAR);
    let irq_id = iar & 0x3FF;
    if irq_id == 1023 { None } else { Some(irq_id) }
}

/// Signal End of Interrupt to the GIC.
pub fn end_of_interrupt(irq_id: u32) {
    if let Some(gicc) = unsafe { &*GICC.get() }.as_ref() {
        write_reg(gicc, GICC_EOIR, irq_id);
    }
}
