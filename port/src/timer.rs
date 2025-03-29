//! Timer abstraction for the r9 kernel
//!
//! Provides a common interface for timer functionality across architectures.

/// Timer state
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TimerState {
    /// Timer is stopped
    Stopped,
    /// Timer is running
    Running,
    /// Timer has expired
    Expired,
}

/// Timer configuration
#[derive(Debug, Clone, Copy, Default)]
pub struct TimerConfig {
    /// Timer period in milliseconds
    pub period_ms: u32,
    /// One-shot or periodic
    pub one_shot: bool,
}

impl TimerConfig {
    pub const fn new(period_ms: u32) -> Self {
        Self { period_ms, one_shot: false }
    }

    pub const fn one_shot(period_ms: u32) -> Self {
        Self { period_ms, one_shot: true }
    }
}

/// Timer implementation
pub trait Timer {
    /// Initialize the timer subsystem
    fn init() {}

    /// Start or restart the timer with the given configuration
    fn start(&mut self, config: TimerConfig);

    /// Stop the timer
    fn stop(&mut self);

    /// Check if the timer has expired
    fn is_expired(&self) -> bool;

    /// Get the current timer state
    fn state(&self) -> TimerState;

    /// Get the current timer value (arch-specific)
    fn get_value(&self) -> u64;

    /// Set the timer value (arch-specific)
    fn set_value(&mut self, value: u64);

    /// Get the timer frequency (ticks per second)
    fn frequency(&self) -> u32;
}

/// Default timer implementation for platforms with hardware timers
pub struct HardwareTimer {}

impl Default for HardwareTimer {
    fn default() -> Self {
        Self {}
    }
}

impl Timer for HardwareTimer {
    fn init() {}

    fn start(&mut self, _config: TimerConfig) {}

    fn stop(&mut self) {}

    fn is_expired(&self) -> bool {
        false
    }

    fn state(&self) -> TimerState {
        TimerState::Stopped
    }

    fn get_value(&self) -> u64 {
        0
    }

    fn set_value(&mut self, _value: u64) {}

    fn frequency(&self) -> u32 {
        0
    }
}

/// Default timer implementation for platforms without hardware timers
pub struct SoftwareTimer {}

impl Default for SoftwareTimer {
    fn default() -> Self {
        Self {}
    }
}

impl Timer for SoftwareTimer {
    fn init() {}

    fn start(&mut self, _config: TimerConfig) {}

    fn stop(&mut self) {}

    fn is_expired(&self) -> bool {
        false
    }

    fn state(&self) -> TimerState {
        TimerState::Stopped
    }

    fn get_value(&self) -> u64 {
        0
    }

    fn set_value(&mut self, _value: u64) {}

    fn frequency(&self) -> u32 {
        0
    }
}

/// Sleep for the specified number of milliseconds
pub fn sleep_ms(ms: u32) {
    // Simple implementation: just spin for the specified time
    // A proper implementation would use interrupts
    let ticks = (ms * 1000) / 100; // Approximate
    for _ in 0..ticks {
        core::hint::spin_loop();
    }
}

/// Test helpers
#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn test_timer_config() {
        let config = TimerConfig::new(100);
        assert_eq!(config.period_ms, 100);
        assert!(!config.one_shot);

        let os_config = TimerConfig::one_shot(100);
        assert_eq!(os_config.period_ms, 100);
        assert!(os_config.one_shot);
    }

    #[test]
    fn test_timer_traits() {
        let mut timer = HardwareTimer::default();
        timer.init();

        assert_eq!(timer.state(), TimerState::Stopped);
        assert!(!timer.is_expired());
    }

    #[test]
    fn test_sleep_ms() {
        // Sleep for a very short time
        sleep_ms(1);
        // Should not panic
    }
}
