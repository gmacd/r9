//! Simple test process that prints incrementing numbers

use crate::swtch;
use crate::timer;
use port::println;

pub fn run() {
    println!("Starting test process");

    let mut count = 0u32;
    const MAX_ITERATIONS: u32 = 20;

    loop {
        if count >= MAX_ITERATIONS {
            println!("Test process completed {count} iterations");
            // Exit via syscall
            syscall::sys_exit(0);
        }

        println!("Iteration {count}");

        // Sleep for approximately 100ms
        timer::sleep_ms(100);

        count += 1;
    }
}

mod syscall {
    /// Syscall to exit the process
    ///   mov x0, #0
    ///   mov x1, #exit_code
    ///   svc #0
    pub fn sys_exit(_code: u32) {
        unsafe {
            core::arch::asm!(
                "mov x0, #0",
                "mov x1, {}",
                in(reg) _code,
                options(nostack),
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
