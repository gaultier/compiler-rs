use miniserde::Serialize;
use std::ptr::null_mut;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
use std::{
    alloc::{GlobalAlloc, Layout},
    cell::UnsafeCell,
};

use crate::{
    ast::{Node, Parser},
    error::Error,
    lex::{Lexer, Token},
    origin::FileId,
};

pub mod ast;
pub mod error;
pub mod lex;
mod origin;

const ARENA_SIZE: usize = 1 * 1024 * 1024;

struct SimpleAllocator {
    arena: UnsafeCell<[u8; ARENA_SIZE]>,
    remaining: AtomicUsize,
}

#[global_allocator]
static ALLOCATOR: SimpleAllocator = SimpleAllocator {
    arena: UnsafeCell::new([0x55; ARENA_SIZE]),
    remaining: AtomicUsize::new(ARENA_SIZE),
};

unsafe impl Sync for SimpleAllocator {}

unsafe impl GlobalAlloc for SimpleAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let size = layout.size();
        let align = layout.align();

        let align_mask_to_round_down = !(align - 1);
        assert!(align <= 8);

        let mut allocated = 0;
        if self
            .remaining
            .fetch_update(Relaxed, Relaxed, |mut remaining| {
                if size > remaining {
                    return None;
                }
                remaining -= size;
                remaining &= align_mask_to_round_down;
                allocated = remaining;
                Some(remaining)
            })
            .is_err()
        {
            return null_mut();
        };
        unsafe { self.arena.get().cast::<u8>().add(allocated) }
    }

    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {}
}

pub fn arena_alloc() {}

#[unsafe(no_mangle)]
pub extern "C" fn alloc_u8(size: u32) -> usize {
    let layout = Layout::from_size_align(size as usize, std::mem::align_of::<u8>()).unwrap();
    let ptr = unsafe { std::alloc::alloc(layout) };
    assert!(!ptr.is_null());
    ptr as usize
}

#[unsafe(no_mangle)]
pub extern "C" fn dealloc() {
    todo!()
}

#[repr(transparent)]
pub struct AllocHandle(u64);

#[unsafe(no_mangle)]
pub extern "C" fn lex(in_ptr: *const u8, in_len: usize, file_id: FileId) -> AllocHandle {
    assert!(!in_ptr.is_null());

    let input_bytes = unsafe { &*std::ptr::slice_from_raw_parts(in_ptr, in_len) };
    let input_str = std::str::from_utf8(input_bytes).unwrap();

    let mut lexer = Lexer::new(file_id);
    lexer.lex(input_str);

    let json = miniserde::json::to_string(&(&lexer.tokens, &lexer.errors));

    let ptr = json.as_bytes().as_ptr() as u64;
    let len = json.len() as u32 as u64;

    AllocHandle(ptr << 32 | len)
}

#[derive(Serialize)]
pub struct ParseResponse<'a> {
    pub tokens: &'a [Token],
    pub errors: &'a [Error],
    pub nodes: &'a [Node],
}

#[unsafe(no_mangle)]
pub extern "C" fn parse(in_ptr: *const u8, in_len: usize, file_id: FileId) -> AllocHandle {
    assert!(!in_ptr.is_null());

    let input_bytes = unsafe { &*std::ptr::slice_from_raw_parts(in_ptr, in_len) };
    let input_str = std::str::from_utf8(input_bytes).unwrap();

    let mut lexer = Lexer::new(file_id);
    lexer.lex(input_str);

    let mut parser = Parser::new(input_str, &lexer);
    parser.parse();

    let parser_response = ParseResponse {
        tokens: &parser.tokens,
        nodes: &parser.nodes,
        errors: &parser.errors,
    };
    let json = miniserde::json::to_string(&parser_response);

    let ptr = json.as_bytes().as_ptr() as u64;
    let len = json.len() as u32 as u64;

    AllocHandle(ptr << 32 | len)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lex() {
        let input = " 123 456 ";
        let handle = lex(input.as_ptr(), input.len(), 1);
        let (fat_ptr, _data) = Allocation::from_wasm_memory_handle(handle);
        assert!(fat_ptr.len > 0);
        assert!(fat_ptr.cap > 0);
        assert!(fat_ptr.align == 8);

        dealloc(handle);
    }
}
