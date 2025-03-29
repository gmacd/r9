//! GIC - Glocal Interrupt Controller

#![allow(static_mut_refs)]

use core::arch::asm;
use core::ops::Range;

use crate::deviceutil::map_device_register;
use crate::io::{read_reg, write_reg};
use crate::vm;
use bitflags::bitflags;
use bitstruct::bitstruct;
use port::fdt::DeviceTree;
use port::mem::{PhysRange, VirtRange};
use port::println;

pub const GENERIC_TIMER_IRQ: u32 = 30;

static mut GICD_VIRTRANGE: VirtRange = VirtRange::empty();
static mut GICC_VIRTRANGE: VirtRange = VirtRange::empty();

enum GicdOffset {
    Controller = 0x0,   // GICD_CTLR
    TypeRegister = 0x4, // GICD_TYPER
    InterruptSetEnable = 0x100,
    InterruptClearPending = 0x280,
    InterruptPriority = 0x400,
    InterruptProcessorTargets = 0x800,
    InterruptConfiguration = 0xc00,
}

enum GiccOffset {
    Controller = 0x0,
    PriorityMaskRegister = 0x4,
    BinaryPointRegister = 0x8,
    InterruptAcknowledge = 0xc,
}

bitstruct! {
    #[derive(Copy, Clone, PartialEq)]
    #[repr(transparent)]
    pub struct CbarEl1(pub u64) {
        pub periphbase: u64 = 0..43;
    }
}

bitstruct! {
    #[derive(Copy, Clone, Debug, PartialEq)]
    #[repr(transparent)]
    pub struct GicdTypeR(pub u32) {
        pub it_lines_number: u8 = 0..5;
        pub cpu_number: u8 = 5..8;
        pub espi: bool = 8;
        res: bool = 9;
        pub security_extn: bool = 10;
        pub num_lpis:u8 = 11..16;
        pub mbis: bool = 16;
        pub lpis: bool = 17;
        pub dvis: bool = 18;
        pub id_bits: u8 = 19..24;
        pub a3v: bool = 24;
        pub no_1n: bool = 25;
        pub rss: bool = 26;
        pub espi_range: u8 = 27..32;
    }
}

bitflags! {
    pub struct GicdInterruptConfigurationRegister: u8 {
        const EDGE = 1;
    }
}

bitstruct! {
    #[derive(Copy, Clone, PartialEq)]
    #[repr(transparent)]
    pub struct GiccIar(pub u32) {
        pub int_id: u32 = 0..24;
        res: u64 = 24..32;
    }
}

pub fn init(dt: &DeviceTree) {
    let mut regs = dt
        .find_compatible("arm,gic-400")
        .map(|prop| dt.property_translated_reg_iter(prop))
        .flatten()
        .map(|r| r.regblock())
        .flatten()
        .map(|r| PhysRange::from(&r));
    let gicd_physrange = regs.next().expect("Couldn't find GICD");
    let gicc_physrange = regs.next().expect("Couldn't find GICC");

    unsafe {
        GICD_VIRTRANGE = match map_device_register("gicd", gicd_physrange, vm::PageSize::Page4K) {
            Ok(gicd_virtrange) => gicd_virtrange,
            Err(msg) => {
                println!("can't map gicd {:?}", msg);
                return;
            }
        };
        GICC_VIRTRANGE = match map_device_register("gicc", gicc_physrange, vm::PageSize::Page4K) {
            Ok(gicc_virtrange) => gicc_virtrange,
            Err(msg) => {
                println!("can't map gicc {:?}", msg);
                return;
            }
        };
    }

    let spi_range = spi_range();
    let espi_range = espi_range();
    println!("spi interrupt range: {:?}", spi_range);
    println!("espi interrupt range: {:?}", espi_range);

    let typer = read_gicd_typer();
    println!("gicd_typer: {:?}", typer);

    write_dist(GicdOffset::Controller, 1);
    write_cpu(GiccOffset::Controller, 1);
    write_cpu(GiccOffset::PriorityMaskRegister, 0xff);
    write_cpu(GiccOffset::BinaryPointRegister, 0);
}

pub fn init_timer_test() {
    println!("cntpct_el0:{}", cntpct_el0());
    println!("cntfrq_el0:{}", cntfrq_el0());
    println!("cntp_cval_el0:{}", cntp_cval_el0());
    println!("cntp_tval_el0:{}", cntp_tval_el0());
    set_cntp_tval_el0(111111);
}

fn write_dist(offset: GicdOffset, val: u32) {
    unsafe { write_reg(GICD_VIRTRANGE.clone(), offset as usize, val) };
}

fn write_cpu(offset: GiccOffset, val: u32) {
    unsafe { write_reg(GICD_VIRTRANGE.clone(), offset as usize, val) };
}

fn read_gicd_typer() -> GicdTypeR {
    unsafe { GicdTypeR(read_reg(GICD_VIRTRANGE.clone(), GicdOffset::TypeRegister as usize)) }
}

pub fn read_gicc_iar() -> GiccIar {
    unsafe { GiccIar(read_reg(GICC_VIRTRANGE.clone(), GiccOffset::InterruptAcknowledge as usize)) }
}

fn spi_range() -> Range<u32> {
    let typer = read_gicd_typer();
    let it_lines_number = typer.it_lines_number() as u32;
    if it_lines_number == 0 {
        0..0
    } else {
        let max_int_id = 32 * (it_lines_number + 1) - 1;
        32..max_int_id
    }
}

fn espi_range() -> Range<u32> {
    let typer = read_gicd_typer();
    if !typer.espi() {
        0..0
    } else {
        let espi_range = typer.espi_range() as u32;
        if espi_range == 0 {
            0..0
        } else {
            let max_int_id = 32 * (espi_range + 1) + 4095;
            32..max_int_id
        }
    }
}

fn set_config(interrupt_id: u32, config: GicdInterruptConfigurationRegister) {
    const GICD_ICFGR_SIZE: u32 = 16;
    const GICD_ICFGR_BITS: u32 = 2;
    let shift = (interrupt_id % GICD_ICFGR_SIZE) * GICD_ICFGR_BITS;
    let regnum = interrupt_id / GICD_ICFGR_SIZE as u32;
    let regoffset = GicdOffset::InterruptConfiguration as usize + (regnum as usize * 8);

    unsafe {
        let mut value = read_reg(GICD_VIRTRANGE.clone(), regoffset);
        value &= !(0x03 << shift);
        value |= (config.bits() as u32) << shift;
        write_reg(GICD_VIRTRANGE.clone(), regoffset, value);
    }
}

fn set_priority(interrupt_id: u32, priority: u8) {
    const GICD_IPRIORITYR_SIZE: u32 = 4;
    const GICD_IPRIORITYR_BITS: u32 = 8;
    let shift = (interrupt_id % GICD_IPRIORITYR_SIZE) * GICD_IPRIORITYR_BITS;
    let regnum = interrupt_id / GICD_IPRIORITYR_SIZE as u32;
    let regoffset = GicdOffset::InterruptPriority as usize + (regnum as usize * 8);

    unsafe {
        let mut value = read_reg(GICD_VIRTRANGE.clone(), regoffset);
        value &= !(0xff << shift);
        value |= (priority as u32) << shift;
        write_reg(GICD_VIRTRANGE.clone(), regoffset, value);
    }
}

fn set_core(interrupt_id: u32, core: u32) {
    const GICD_ITARGETSR_SIZE: u32 = 4;
    const GICD_ITARGETSR_BITS: u32 = 8;
    let shift = (interrupt_id % GICD_ITARGETSR_SIZE) * GICD_ITARGETSR_BITS;
    let regnum = interrupt_id / GICD_ITARGETSR_SIZE as u32;
    let regoffset = GicdOffset::InterruptProcessorTargets as usize + (regnum as usize * 8);

    unsafe {
        let mut value = read_reg(GICD_VIRTRANGE.clone(), regoffset);
        value &= !(0xff << shift);
        value |= core << shift;
        write_reg(GICD_VIRTRANGE.clone(), regoffset, value);
    }
}

fn enable(interrupt_id: u32) {
    const GICD_ISENABLER_SIZE: u32 = 32;
    let regnum = interrupt_id / GICD_ISENABLER_SIZE as u32;
    let regoffset = GicdOffset::InterruptSetEnable as usize + (regnum as usize * 8);
    let id_bit = 1 << (interrupt_id % GICD_ISENABLER_SIZE);
    unsafe { write_reg(GICD_VIRTRANGE.clone(), regoffset, id_bit) };
}

pub fn clear(interrupt_id: u32) {
    const GICD_IPRIORITY_SIZE: u32 = 4;
    let regnum = interrupt_id / GICD_IPRIORITY_SIZE as u32;
    let regoffset = GicdOffset::InterruptClearPending as usize + (regnum as usize * 8);
    let id_bit = 1 << (interrupt_id % GICD_IPRIORITY_SIZE);
    unsafe { write_reg(GICD_VIRTRANGE.clone(), regoffset, id_bit) };
}

pub fn setup_irq(irq: u32, priority: u32, cores: u32) {
    set_config(irq, GicdInterruptConfigurationRegister::EDGE);
    set_priority(priority, 0);
    set_core(irq, cores);
    clear(irq);
    enable(irq);
}

fn cntpct_el0() -> u64 {
    #[cfg(not(test))]
    {
        let mut value: u64;
        unsafe { asm!("mrs {value}, cntpct_el0", value = out(reg) value) };
        value
    }
    #[cfg(test)]
    0
}

fn cntfrq_el0() -> u64 {
    #[cfg(not(test))]
    {
        let mut value: u64;
        unsafe { asm!("mrs {value}, cntfrq_el0", value = out(reg) value) };
        value
    }
    #[cfg(test)]
    0
}

fn cntp_cval_el0() -> u64 {
    #[cfg(not(test))]
    {
        let mut value: u64;
        unsafe { asm!("mrs {value}, cntp_cval_el0", value = out(reg) value) };
        value
    }
    #[cfg(test)]
    0
}

fn cntp_tval_el0() -> u64 {
    #[cfg(not(test))]
    {
        let mut value: u64;
        unsafe { asm!("mrs {value}, cntp_tval_el0", value = out(reg) value) };
        value
    }
    #[cfg(test)]
    0
}

fn set_cntp_tval_el0(value: u32) {
    #[cfg(not(test))]
    {
        unsafe {
            let value: u64 = value as u64;
            asm!("msr cntp_tval_el0, {value}", value = in(reg) value);
        }
    }
    #[cfg(test)]
    let _ = value;
}
