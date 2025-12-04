use std::alloc::Layout;

use crate::lex::Lexer;

pub mod ast;
pub mod error;
pub mod lex;
mod origin;

#[repr(transparent)]
#[derive(Copy, Clone)]
pub struct WasmMemoryHandle(usize);

pub struct Allocation {
    len: u32,
    cap: u32,
    align: u8,
    ptr: *mut u8,
}

impl Allocation {
    fn from_wasm_memory_handle(handle: WasmMemoryHandle) -> (Self, usize) {
        let ptr = handle.0 as *mut u8;

        let length_slice = unsafe { std::slice::from_raw_parts(ptr.add(0 * 4), 4) };
        let mut length_array = [0; 4];
        length_array.copy_from_slice(length_slice);
        let length = u32::from_le_bytes(length_array);

        let cap_slice = unsafe { std::slice::from_raw_parts(ptr.add(1 * 4), 4) };
        let mut cap_array = [0; 4];
        cap_array.copy_from_slice(cap_slice);
        let cap = u32::from_le_bytes(cap_array);

        let align_slice = unsafe { std::slice::from_raw_parts(ptr.add(2 * 4), 1) };
        let align = align_slice[0];
        assert!(align <= 8);

        let data = unsafe { ptr.add(2 * 4 + 1) };

        (
            Self {
                ptr,
                len: length,
                cap,
                align,
            },
            data as usize,
        )
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn alloc_u8_no_metadata(size: u32) -> usize {
    let layout = Layout::from_size_align(size as usize, std::mem::align_of::<u8>()).unwrap();
    let ptr = unsafe { std::alloc::alloc(layout) };
    assert!(!ptr.is_null());
    ptr as usize
}

#[unsafe(no_mangle)]
pub extern "C" fn dealloc_u8_no_metadata(ptr: usize, size: usize) {
    let ptr = ptr as *mut u8;
    if ptr.is_null() {
        return;
    }

    let layout = Layout::from_size_align(size, std::mem::align_of::<u8>()).unwrap();
    unsafe { std::alloc::dealloc(ptr, layout) };
}

#[unsafe(no_mangle)]
pub extern "C" fn dealloc(handle: WasmMemoryHandle) {
    let (ptr, _) = Allocation::from_wasm_memory_handle(handle);
    if ptr.cap == 0 {
        return;
    }

    let layout = Layout::from_size_align(ptr.cap as usize, ptr.align as usize).unwrap();
    unsafe { std::alloc::dealloc(ptr.ptr, layout) };
}

#[unsafe(no_mangle)]
pub extern "C" fn lex(in_ptr: *const u8, in_len: usize) -> WasmMemoryHandle {
    assert!(!in_ptr.is_null());

    let input_bytes = unsafe { &*std::ptr::slice_from_raw_parts(in_ptr, in_len) };
    let input_str = std::str::from_utf8(input_bytes).unwrap();

    let mut lexer = Lexer::new();
    lexer.lex(input_str);

    let json = miniserde::json::to_string(&(&lexer.tokens, &lexer.errors));

    let mut bytes = Vec::with_capacity(json.len() + 3 * 4 + 1);
    bytes.extend((json.len() as u32).to_le_bytes()); // len
    bytes.extend([0u8; 4]); // cap, backpatched.
    let align = std::mem::align_of::<usize>() as u8;
    bytes.extend(align.to_le_bytes());
    bytes.extend(json.as_bytes());
    assert_eq!(bytes.len(), 2 * 4 + 1 + json.len());

    let cap = bytes.capacity() as u32;
    bytes[4..8].copy_from_slice(cap.to_le_bytes().as_slice());

    let ptr = bytes.as_ptr() as usize;

    std::mem::forget(bytes);

    WasmMemoryHandle(ptr)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lex() {
        let input = " 123 456 ";
        let handle = lex(input.as_ptr(), input.len());
        let (fat_ptr, _data) = Allocation::from_wasm_memory_handle(handle);
        assert!(fat_ptr.len > 0);
        assert!(fat_ptr.cap > 0);
        assert!(fat_ptr.align == 8);

        dealloc(handle);
    }
}
