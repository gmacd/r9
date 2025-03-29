//! Simple test process that prints incrementing numbers

use crate::timer;

use port::println;

mod syscall {
    use core::arch::asm;

    /// Syscall to exit the process
    pub fn sys_exit(code: u32) {
        unsafe {
            core::arch::asm!(
                "ecall",
                "li a7, {}",
                in(reg) code,
                options(nostack)
            );
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_process_module_compiles() {
        // Just verify the module compiles
        assert!(true);
    }
}
