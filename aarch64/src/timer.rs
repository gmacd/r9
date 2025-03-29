//! AArch64 timer implementation using the System Timer and GIC

use core::arch::asm;
use core::sync::atomic::{AtomicBool, Ordering};

use port::timer::{Timer, TimerConfig, TimerState};

pub static mut TIMER_EXPIRED: AtomicBool = AtomicBool::new(false);

pub struct AArch64Timer {
    base: u64,
    running: AtomicBool,
}

unsafe impl Send for AArch64Timer {}
unsafe impl Sync for AArch64Timer {}

impl Default for AArch64Timer {
    fn default() -> Self {
        Self { base: 0, running: AtomicBool::new(false) }
    }
}

impl AArch64Timer {
    pub fn init() {
        unsafe {
            // Get timer frequency
            let mut _freq: u64 = 0;
            asm!("mrs {}, cntfrq_el0", out(reg) _freq);

            // Get current count value for base
            let mut base: u64 = 0;
            asm!("mrs {}, cntpct_el0", out(reg) base);

            // Get timer period from DTB or use default
            // For now, use a reasonable default of 1ms period
            let period_ns: i64 = 1_000_000; // 1ms in nanoseconds
            // Use constant frequency (1MHz)
            let freq = 1_000_000;
            let period_ticks = (period_ns * freq) / 1_000_000_000;

            if period_ticks > 0 {
                // Set initial timer value
                asm!("msr cntp_tval_el0, {}", in(reg) period_ticks);

                // Enable the timer
                asm!("msr cntp_cval_el0, {}", in(reg) base);

                // Clear the pending timer interrupt if any
                asm!("isb");
            }

            // base is not used
            // Frequency is defined as a constant
        }
    }

    fn get_count() -> u64 {
        let mut value: u64 = 0;
        unsafe {
            asm!("mrs {}, cntpct_el0", out(reg) value,
                 options(nostack));
        }
        value
    }
}

impl Timer for AArch64Timer {
    fn init() {
        unsafe {
            // Get current count value for base
            let mut base: u64 = 0;
            asm!("mrs {}, cntpct_el0", out(reg) base);

            // Use constant frequency (1MHz)
            let freq: i64 = 1_000_000;
            let period_ns = 10_000_000; // 10ms in nanoseconds
            let period_ticks = (period_ns * freq) / 1_000_000_000;

            if period_ticks > 0 {
                // Set initial timer value
                asm!("msr cntp_tval_el0, {}", in(reg) period_ticks);

                // Enable the timer
                asm!("msr cntp_cval_el0, {}", in(reg) base);
            }
        }
    }

    fn start(&mut self, config: TimerConfig) {
        let freq = 1_000_000; // 1MHz
        let period_ticks = if config.period_ms > 0 { (config.period_ms * freq) / 1000 } else { 1 };

        let current = Self::get_count();
        let next = current + period_ticks as u64;

        unsafe {
            asm!("msr cntp_tval_el0, {}", in(reg) period_ticks);
            asm!("msr cntp_cval_el0, {}", in(reg) next);
            asm!("isb");
        }

        self.running.store(true, Ordering::SeqCst);
    }

    fn stop(&mut self) {
        unsafe {
            // Disable timer by clearing CNTV_CVAL_EL0
            asm!("msr cntp_cval_el0, {}", in(reg) 0);
        }
        self.running.store(false, Ordering::SeqCst);
    }

    fn is_expired(&self) -> bool {
        self.running.load(Ordering::SeqCst)
    }

    fn state(&self) -> TimerState {
        if self.running.load(Ordering::SeqCst) { TimerState::Running } else { TimerState::Stopped }
    }

    fn get_value(&self) -> u64 {
        Self::get_count()
    }

    fn set_value(&mut self, value: u64) {
        unsafe {
            asm!("msr cntp_cval_el0, {}", in(reg) value);
        }
    }

    fn frequency(&self) -> u32 {
        1_000_000 // 1MHz
    }
}

/// Sleep for the specified number of milliseconds
pub fn sleep_ms(ms: u32) {
    // Use the port's sleep_ms implementation
    port::timer::sleep_ms(ms);
}

/// System timer interrupt handler
#[cfg(not(test))]
unsafe extern "C" fn timer_interrupt() {
    use crate::gic;

    unsafe {
        core::ptr::write(&raw mut TIMER_EXPIRED, AtomicBool::new(true));
        // Clear the timer interrupt
        gic::clear(gic::GENERIC_TIMER_IRQ);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_arch64_timer_get_count() {
        let count = AArch64Timer::get_count();
        assert!(count <= u64::MAX);
    }

    #[test]
    fn test_arch64_timer_init() {
        AArch64Timer::init();
        assert!(AArch64Timer::frequency() > 0);
    }
}
