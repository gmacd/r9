use core::ptr;

use crate::maths;
#[cfg(not(test))]
use crate::{print, println};

#[derive(Debug)]
pub enum Format {
    Hex,
}

/// Map segment size to bytes
#[derive(Clone, Copy, Debug)]
pub enum SegmentSize {
    Size8 = 1,
    Size64 = 8,
}

pub fn memdump(startva: usize, count: usize, format: Format, size: SegmentSize) {
    let bytes_per_line = 16;
    let segments_per_line = bytes_per_line / size as usize;

    println!("memdump({startva:#016x}, {count}, {format:?}, {size:?})");

    let y: u64 = 0xf00dbeefcafebabe;
    let yaddr = ptr::addr_of!(y);
    let yaddr_u64 = yaddr as u64;
    let yread = unsafe { ptr::read(yaddr_u64 as *const u64) };
    let yread2 = unsafe { *(yaddr_u64 as *const u64) };
    // println!(
    //     "y:{y:0x} - yaddr:{yaddr:p} - yaddr_u64:{yaddr_u64:0x} - yread:{yread:0x} - yread2:{yread2:0x}"
    // );

    let mut va = startva;
    for segidx in 0..count {
        if segidx % segments_per_line == 0 {
            print!("0x{:016x}: ", va);
        }

        match size {
            SegmentSize::Size8 => {
                let value = unsafe { *(va as *const u8) };
                // print!("0x{:02x}({:016x})", value, va)
                print!("0x{:02x}", value)
            }
            SegmentSize::Size64 => {
                let value = unsafe { ptr::read(va as *const u64) };
                // print!("0x{:016x}({:016x})", value, va)
                print!("0x{:016x}", value)
            }
        }

        va += size as usize;

        if (segidx + 1) == count {
            println!();
            break;
        }
        if (segidx + 1) % segments_per_line == 0 {
            println!();
        } else {
            print!(" ");
        }
    }
}

pub fn memdump_ptr<T>(ptr: *const T, format: Format, size: SegmentSize) {
    let aligned_ptr = maths::round_down2_usize(ptr as usize, 16);
    let align_offset = ptr as usize - aligned_ptr;
    let real_size = size_of::<T>();
    let buffer_size = real_size + align_offset;
    let bytes_per_segment = size as usize;
    let num_segments = (buffer_size + bytes_per_segment - 1) / bytes_per_segment;

    println!(
        "memdump of type: {} unaligned_addr: {:p} size: {} align_offset: {}",
        core::any::type_name::<T>(),
        ptr,
        real_size,
        align_offset
    );
    memdump(aligned_ptr, num_segments, format, size);
}
