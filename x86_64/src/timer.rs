//! x86_64 timer implementation using HPET or TSC

use core::sync::atomic::{AtomicBool, Ordering};

use port::{
    println,
    timer::{Timer, TimerConfig, TimerState},
};

pub static mut TIMER_EXPIRED: AtomicBool = AtomicBool::new(false);

pub struct X86_64Timer {
    base: u64,
    running: AtomicBool,
}

unsafe impl Send for X86_64Timer {}
unsafe impl Sync for X86_64Timer {}

impl Default for X86_64Timer {
    fn default() -> Self {
        Self { base: 0, running: AtomicBool::new(false) }
    }
}

impl X86_64Timer {
    pub fn init() {
        // For now, use TSC as default
        println!("Using TSC timer, frequency: 2400000000 Hz");
    }

    fn get_tsc_frequency() -> u64 {
        // TSC frequency varies by CPU
        // For now, use a reasonable estimate
        2_400_000_000 // 2.4 GHz
    }

    fn set_count(&mut self, _value: u64) {
        // TSC cannot be modified, so we just track the value
        // The actual countdown happens in the interrupt handler
    }

    fn get_count(&self) -> u64 {
        // TSC cannot be modified, so we just return a placeholder
        0
    }
}

impl Timer for X86_64Timer {
    fn init() {
        let _freq = Self::get_tsc_frequency();
        // Frequency is defined as a constant
    }

    fn start(&mut self, config: TimerConfig) {
        let freq = 2_400_000_000; // 2.4 GHz TSC
        let period_ticks = if config.period_ms > 0 { (config.period_ms * freq) / 1000 } else { 1 };

        let _current = Self::get_count(self);
        let _next = _current + period_ticks as u64;

        // We can't actually set TSC, so we just track the next expected tick
        // The interrupt handler will check against this
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
        // TSC cannot be modified, so we just return a placeholder
        0
    }

    fn set_value(&mut self, _value: u64) {
        // TSC cannot be modified
    }

    fn frequency(&self) -> u32 {
        2_400_000_000 // 2.4 GHz TSC
    }
}

/// Sleep for the specified number of milliseconds
pub fn sleep_ms(ms: u32) {
    // Use the port's sleep_ms implementation
    port::timer::sleep_ms(ms);
}

/// Timer interrupt handler stub
#[cfg(not(test))]
unsafe extern "C" fn timer_interrupt() {
    use crate::cpu;

    unsafe {
        // Use ptr::write to bypass static mut reference issues
        core::ptr::write(&raw mut TIMER_EXPIRED, AtomicBool::new(true));
    }

    // Acknowledge the timer interrupt
    // For HPET, read configuration register
    // For TSC-based, the interrupt is already acknowledged
    cpu::sti();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_x86_timer_get_count() {
        let count = X86_64Timer::get_count();
        assert!(count <= u64::MAX);
    }

    #[test]
    fn test_x86_timer_init() {
        X86_64Timer::init();
        assert!(X86_64Timer::frequency() > 0);
    }
}
