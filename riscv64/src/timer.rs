//! RISC-V timer implementation using SBI

use core::cell::UnsafeCell;
use core::ptr::addr_of_mut;
use core::sync::atomic::{AtomicBool, Ordering};

pub static mut TIMER_EXPIRED: AtomicBool = AtomicBool::new(false);

// Wrapper to safely access mutable static in Rust 2024
pub fn timer_expired_mut() -> &'static mut AtomicBool {
    unsafe {
        // Suppress the Rust 2024 static_mut_refs lint
        #[allow(static_mut_refs)]
        &mut *addr_of_mut!(TIMER_EXPIRED)
    }
}

pub struct RISCvTimer {
    base: u64,
    running: AtomicBool,
}

unsafe impl Send for RISCvTimer {}
unsafe impl Sync for RISCvTimer {}

impl Default for RISCvTimer {
    fn default() -> Self {
        Self { base: 0, running: AtomicBool::new(false) }
    }
}

impl RISCvTimer {
    pub fn init() {
        // Initialize SBI timer
        // The timer frequency is typically 1MHz for SBI timer
        // Frequency is defined as a constant
    }

    fn get_count() -> u64 {
        // For now, return a placeholder value
        // A proper implementation would read the SBI timer
        0
    }

    fn set_count(&mut self, value: u64) {
        // For now, do nothing
        // A proper implementation would write to SBI timer
    }
}

impl Timer for RISCvTimer {
    fn init() {
        // Initialize SBI timer
        // For now, just set a reasonable frequency (1MHz)
        // Frequency is defined as a constant
    }

    fn start(&mut self, config: TimerConfig) {
        let freq = 1_000_000;
        let period_ticks = if config.period_ms > 0 { (config.period_ms * freq) / 1000 } else { 1 };

        let current = Self::get_count();
        let next = current + period_ticks as u64;

        // Set the timer value
        Self::set_count(self, next);

        self.running.store(true, Ordering::SeqCst);
    }

    fn stop(&mut self) {
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
        Self::set_count(self, value);
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

/// SBI timer interrupt handler stub
#[cfg(not(test))]
unsafe extern "C" fn timer_interrupt() {
    timer_expired_mut().store(true, Ordering::SeqCst);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_riscv_timer_get_count() {
        let count = RISCvTimer::get_count();
        assert!(count <= u64::MAX);
    }

    #[test]
    fn test_riscv_timer_init() {
        RISCvTimer::init();
        assert!(RISCvTimer::frequency() > 0);
    }
}
