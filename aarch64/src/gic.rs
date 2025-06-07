//! GIC - Glocal Interrupt Controller

use core::arch::asm;
use core::ops::Range;

use crate::deviceutil::map_device_register;
use crate::io::{read_reg, write_reg};
use crate::vm;
use bitflags::bitflags;
use bitstruct::bitstruct;
use port::Result;
use port::fdt::DeviceTree;
use port::mcslock::{Lock, LockNode};
use port::mem::{PhysRange, VirtRange};
use port::println;

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
    //IntSetEnableReg = 0x100,
}

bitstruct! {
    #[derive(Copy, Clone, PartialEq)]
    #[repr(transparent)]
    pub struct CbarEl1(pub u64) {
        //pub reserved0: u32 = 0..18;
        pub periphbase: u64 = 0..43;
        //        pub reserved1: Mair = 40..;
    }
}

bitstruct! {
    #[derive(Copy, Clone, PartialEq)]
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

// GiccIar is to be used to ack a GIC2 interrupt, and get the ID.
bitstruct! {
    #[derive(Copy, Clone, PartialEq)]
    #[repr(transparent)]
    pub struct GiccIar(pub u32) {
        pub int_id: u32 = 0..24;
        res: u64 = 24..32;
    }
}

static GIC: Lock<Option<Gic>> = Lock::new("gic", None);

pub fn init(dt: &DeviceTree) {
    match Gic::new(dt) {
        Ok(gic) => {
            println!("gicd: {}", gic.gicd_virtrange);
            println!("spi interrupt range: {:?}", gic.spi_range);
            println!("espi interrupt range: {:?}", gic.espi_range);

            {
                // Enable distributor and CPU interface controllers
                gic.write_dist(GicdOffset::Controller, 1);
                gic.write_cpu(GiccOffset::Controller, 1);

                gic.write_cpu(GiccOffset::PriorityMaskRegister, 0xff);
                gic.write_cpu(GiccOffset::BinaryPointRegister, 0);

                const TIMER_IRQ: u32 = 30; // TODO how to pick board independent value?
                gic.set_config(TIMER_IRQ, GicdInterruptConfigurationRegister::EDGE);
                gic.set_priority(TIMER_IRQ, 0);
                gic.set_core(TIMER_IRQ, 0x01); // Only sent to cpu 1
                gic.clear(TIMER_IRQ);
                gic.enable(TIMER_IRQ);

                unsafe {
                    asm!("mrs x1, CNTFRQ_EL0");
                    asm!("msr CNTP_TVAL_EL0, x1");
                    asm!("mov x0, 1");
                    asm!("msr CNTP_CTL_EL0, x0");
                }
            }

            let node = LockNode::new();
            let mut gic_guard = GIC.lock(&node);
            *gic_guard = Some(gic);
        }
        Err(msg) => {
            println!("can't initialise gic: {:?}", msg);
        }
    }

    // let node = LockNode::new();
    // let mut gic = GIC.lock(&node);
    // *gic = Some({
    //     // TODO can this be nicer if we assume we have a global allocator?
    //     static MAYBE_GIC: SyncUnsafeCell<MaybeUninit<Gic>> =
    //         SyncUnsafeCell::new(MaybeUninit::uninit());
    //     let gic = unsafe {
    //         let maybe_gic = &mut *MAYBE_GIC.get();
    //         maybe_gic.write(Gic::new(dt, KZERO));
    //         maybe_gic.assume_init_mut()
    //     };

    //     let cbar = cbar_el1();
    //     println!("cbar: {:018x}", cbar.periphbase());
    //     println!("gicd: {:018x}..{:018x}", gic.gicd_range.0.start, gic.gicd_range.0.end);
    //     //gic.write_dist(GicdOffset::Controller, 1);
    //     //gic.write_cpu(GiccOffset::Controller, 1);
    //     gic
    // });
}

struct Gic {
    gicd_virtrange: VirtRange,
    gicc_virtrange: VirtRange,
    spi_range: Range<u32>,
    espi_range: Range<u32>,
}

impl Gic {
    fn new(dt: &DeviceTree) -> Result<Self> {
        let mut regs = dt
            .find_compatible("arm,gic-400")
            .map(|prop| dt.property_translated_reg_iter(prop))
            .flatten()
            .map(|r| r.regblock())
            .flatten()
            .map(|r| PhysRange::from(&r));
        // We expect 2 - the first is GICD (distributor), second is GICC (CPU)
        let gicd_physrange = regs.next().expect("Couldn't find GICD");
        let gicc_physrange = regs.next().expect("Couldn't find GICC");

        let gicd_virtrange = match map_device_register("gicd", gicd_physrange, vm::PageSize::Page4K)
        {
            Ok(gicd_virtrange) => gicd_virtrange,
            Err(msg) => {
                println!("can't map gicd {:?}", msg);
                return Err("can't create gicd");
            }
        };
        let gicc_virtrange = match map_device_register("gicc", gicc_physrange, vm::PageSize::Page4K)
        {
            Ok(gicc_virtrange) => gicc_virtrange,
            Err(msg) => {
                println!("can't map gicc {:?}", msg);
                return Err("can't create gicc");
            }
        };

        let spi_range = Self::spi_range(&gicd_virtrange);
        let espi_range = Self::espi_range(&gicd_virtrange);

        Ok(Gic { gicd_virtrange, gicc_virtrange, spi_range, espi_range })
    }

    fn read_dist(&self, offset: GicdOffset) -> u32 {
        read_reg(&self.gicd_virtrange, offset as usize)
    }

    fn write_dist(&self, offset: GicdOffset, val: u32) {
        write_reg(&self.gicd_virtrange, offset as usize, val);
    }

    fn read_cpu(&self, offset: GiccOffset) -> u32 {
        read_reg(&self.gicc_virtrange, offset as usize)
    }

    fn write_cpu(&self, offset: GiccOffset, val: u32) {
        write_reg(&self.gicc_virtrange, offset as usize, val);
    }

    fn read_gicd_typer(gicd_virtrange: &VirtRange) -> GicdTypeR {
        GicdTypeR(read_reg(gicd_virtrange, GicdOffset::TypeRegister as usize))
    }

    fn read_gicc_iar(gicc_virtrange: &VirtRange) -> GiccIar {
        GiccIar(read_reg(gicc_virtrange, GiccOffset::InterruptAcknowledge as usize))
    }

    fn spi_range(gicd_virtrange: &VirtRange) -> Range<u32> {
        let typer = Self::read_gicd_typer(gicd_virtrange);
        let it_lines_number = typer.it_lines_number() as u32;
        if it_lines_number == 0 {
            0..0
        } else {
            let max_int_id = 32 * (it_lines_number + 1) - 1;
            32..max_int_id
        }
    }

    fn espi_range(gicd_virtrange: &VirtRange) -> Range<u32> {
        let typer = Self::read_gicd_typer(gicd_virtrange);
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

    fn set_config(&self, interrupt_id: u32, config: GicdInterruptConfigurationRegister) {
        const GICD_ICFGR_SIZE: u32 = 16;
        const GICD_ICFGR_BITS: u32 = 2;
        let shift = (interrupt_id % GICD_ICFGR_SIZE) * GICD_ICFGR_BITS;
        let regnum = interrupt_id / GICD_ICFGR_SIZE as u32;
        let regoffset = GicdOffset::InterruptConfiguration as usize + (regnum as usize * 8);

        // Set the configuration in the appropriate interrupt slot (2 bits per interrupt)
        let mut value = read_reg(&self.gicd_virtrange, regoffset);
        value &= !(0x03 << shift);
        value |= (config.bits() as u32) << shift;
        write_reg(&self.gicd_virtrange, regoffset, value);
    }

    fn set_priority(&self, interrupt_id: u32, priority: u8) {
        const GICD_IPRIORITYR_SIZE: u32 = 4;
        const GICD_IPRIORITYR_BITS: u32 = 8;
        let shift = (interrupt_id % GICD_IPRIORITYR_SIZE) * GICD_IPRIORITYR_BITS;
        let regnum = interrupt_id / GICD_IPRIORITYR_SIZE as u32;
        let regoffset = GicdOffset::InterruptPriority as usize + (regnum as usize * 8);

        // Set the priority in the appropriate interrupt slot (8 bits per interrupt)
        let mut value = read_reg(&self.gicd_virtrange, regoffset);
        value &= !(0xff << shift);
        value |= (priority as u32) << shift;
        write_reg(&self.gicd_virtrange, regoffset, value);
    }

    fn set_core(&self, interrupt_id: u32, core: u32) {
        const GICD_ITARGETSR_SIZE: u32 = 4;
        const GICD_ITARGETSR_BITS: u32 = 8;
        let shift = (interrupt_id % GICD_ITARGETSR_SIZE) * GICD_ITARGETSR_BITS;
        let regnum = interrupt_id / GICD_ITARGETSR_SIZE as u32;
        let regoffset = GicdOffset::InterruptProcessorTargets as usize + (regnum as usize * 8);

        // Set the core number in the appropriate interrupt slot (8 bits per interrupt)
        let mut value = read_reg(&self.gicd_virtrange, regoffset);
        value &= !(0xff << shift);
        value |= core << shift;
        write_reg(&self.gicd_virtrange, regoffset, value);
    }

    fn enable(&self, interrupt_id: u32) {
        const GICD_ISENABLER_SIZE: u32 = 32;
        let regnum = interrupt_id / GICD_ISENABLER_SIZE as u32;
        let regoffset = GicdOffset::InterruptSetEnable as usize + (regnum as usize * 8);
        let id_bit = 1 << (interrupt_id % GICD_ISENABLER_SIZE);
        write_reg(&self.gicd_virtrange, regoffset, id_bit);
    }

    fn clear(&self, interrupt_id: u32) {
        const GICD_IPRIORITY_SIZE: u32 = 4;
        let regnum = interrupt_id / GICD_IPRIORITY_SIZE as u32;
        let regoffset = GicdOffset::InterruptClearPending as usize + (regnum as usize * 8);
        let id_bit = 1 << (interrupt_id % GICD_IPRIORITY_SIZE);
        write_reg(&self.gicd_virtrange, regoffset, id_bit);
    }

    fn init_timer_test(&mut self) {
        // self.timer_val1 = self.read(SystemTimer::CloCounterLower32);
        // self.timer_val3 = self.read(TimerOffset::CloCounterLower32);
        // println!("timervalue:{}", self.timer_val1);
        println!("cntpct_el0:{}", cntpct_el0());
        println!("cntfrq_el0:{}", cntfrq_el0());
        println!("cntp_cval_el0:{}", cntp_cval_el0());
        println!("cntp_tval_el0:{}", cntp_tval_el0());
        set_cntp_tval_el0(111111);
        println!("cntp_cval_el0:{}", cntp_cval_el0());
        println!("cntp_tval_el0:{}", cntp_tval_el0());
        println!("cntp_tval_el0:{}", cntp_tval_el0());
        println!("cntp_tval_el0:{}", cntp_tval_el0());
        println!("cntp_tval_el0:{}", cntp_tval_el0());
        println!("cntp_tval_el0:{}", cntp_tval_el0());
        println!("cntp_tval_el0:{}", cntp_tval_el0());
        println!("cntp_tval_el0:{}", cntp_tval_el0());
        println!("cntp_tval_el0:{}", cntp_tval_el0());
        println!("cntp_tval_el0:{}", cntp_tval_el0());
        println!("cntp_tval_el0:{}", cntp_tval_el0());
        println!("cntp_tval_el0:{}", cntp_tval_el0());
        println!("cntp_tval_el0:{}", cntp_tval_el0());
        println!("cntp_tval_el0:{}", cntp_tval_el0());
        println!("cntp_tval_el0:{}", cntp_tval_el0());
        println!("cntp_tval_el0:{}", cntp_tval_el0());
        println!("cntp_tval_el0:{}", cntp_tval_el0());
        println!("cntp_tval_el0:{}", cntp_tval_el0());
        println!("cntp_tval_el0:{}", cntp_tval_el0());
        println!("cntp_tval_el0:{}", cntp_tval_el0());
        println!("cntp_tval_el0:{}", cntp_tval_el0());
        println!("cntp_tval_el0:{}", cntp_tval_el0());
        println!("cntp_tval_el0:{}", cntp_tval_el0());
        println!("cntp_tval_el0:{}", cntp_tval_el0());
        println!("cntp_tval_el0:{}", cntp_tval_el0());
        println!("cntp_tval_el0:{}", cntp_tval_el0());
        println!("cntp_tval_el0:{}", cntp_tval_el0());
    }
}

pub fn inittest() {
    let node = LockNode::new();
    GIC.lock(&node).as_mut().map(|gic| gic.init_timer_test()).expect("gic not initialised")
}

fn cntpct_el0() -> u64 {
    #[cfg(not(test))]
    {
        let mut value: u64;
        unsafe {
            asm!("mrs {value}, cntpct_el0", value = out(reg) value);
        }
        value
    }
    #[cfg(test)]
    0
}

fn cntfrq_el0() -> u64 {
    #[cfg(not(test))]
    {
        let mut value: u64;
        unsafe {
            asm!("mrs {value}, cntfrq_el0", value = out(reg) value);
        }
        value
    }
    #[cfg(test)]
    0
}

fn cntp_cval_el0() -> u64 {
    #[cfg(not(test))]
    {
        let mut value: u64;
        unsafe {
            asm!("mrs {value}, cntp_cval_el0", value = out(reg) value);
        }
        value
    }
    #[cfg(test)]
    0
}

fn set_cntp_cval_el0(value: u64) {
    #[cfg(not(test))]
    {
        unsafe {
            asm!("msr cntp_cval_el0, {value}", value = in(reg) value);
        }
    }
}

fn cntp_tval_el0() -> u64 {
    #[cfg(not(test))]
    {
        let mut value: u64;
        unsafe {
            asm!("mrs {value}, cntp_tval_el0", value = out(reg) value);
        }
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
}
