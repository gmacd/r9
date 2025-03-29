use core::arch::asm;

use crate::gic::{self, GENERIC_TIMER_IRQ};

pub fn init() {
    // Send generic timer to core 1, priority 0
    gic::setup_irq(GENERIC_TIMER_IRQ, 0, 0x1);

    unsafe {
        asm!("mrs x1, CNTFRQ_EL0", "msr CNTP_TVAL_EL0, x1", "mov x0, 1", "msr CNTP_CTL_EL0, x0");
    }
}
