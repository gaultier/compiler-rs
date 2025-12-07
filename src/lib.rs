pub mod ast;
pub mod error;
pub mod lex;
mod origin;

use memmap::MmapMut;
use miniserde::Serialize;
use std::alloc::GlobalAlloc;
use std::alloc::Layout;
use std::ptr::null_mut;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

use crate::{
    ast::{Node, Parser},
    error::Error,
    lex::{Lexer, Token},
    origin::FileId,
};

const ARENA_SIZE: usize = 1 * 1024 * 1024;

struct SimpleAllocator {
    base_addr: std::cell::OnceCell<usize>,
    offset: AtomicUsize,
}

impl SimpleAllocator {
    #[cfg(target_arch = "wasm32")]
    fn os_alloc(&self) -> usize {
        core::arch::wasm32::memory_grow(0, ARENA_SIZE);
        0
    }

    #[cfg(not(target_arch = "wasm32"))]
    fn os_alloc(&self) -> usize {
        let mut mmapped = MmapMut::map_anon(ARENA_SIZE).unwrap();
        let base_addr = mmapped.as_mut_ptr() as usize;
        std::mem::forget(mmapped);
        base_addr
    }
}

#[global_allocator]
static ALLOCATOR: SimpleAllocator = SimpleAllocator {
    base_addr: std::cell::OnceCell::new(),
    offset: AtomicUsize::new(0),
};

unsafe impl Sync for SimpleAllocator {}

unsafe impl GlobalAlloc for SimpleAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let size = layout.size();
        let align = layout.align();

        // Once.
        let base_addr = *self.base_addr.get_or_init(|| {
            let res = self.os_alloc();
            res
        });

        let mut allocated = 0;
        if self
            .offset
            .fetch_update(Relaxed, Relaxed, |mut offset| {
                let padding = (0usize).wrapping_sub(offset) & (align - 1);
                assert!(padding <= align);

                if padding + offset + size > ARENA_SIZE {
                    return None;
                }
                allocated = offset + padding;
                offset += padding + size;
                Some(offset)
            })
            .is_err()
        {
            return null_mut();
        };
        unsafe { (base_addr as *mut u8).add(allocated) }
    }

    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {}
}

#[unsafe(no_mangle)]
pub extern "C" fn dealloc() {
    todo!()
}

#[unsafe(no_mangle)]
pub extern "C" fn alloc_u8(size: u32) -> usize {
    let layout = Layout::from_size_align(size as usize, std::mem::align_of::<u8>()).unwrap();
    let ptr = unsafe { std::alloc::alloc(layout) };
    assert!(!ptr.is_null());
    ptr as usize
}

#[repr(transparent)]
pub struct AllocHandle(u64);

impl AllocHandle {
    fn unpack(&self) -> (u32, u32) {
        let ptr = (self.0 << 32) as u32;
        let len = (self.0 & 0xff_ff_ff_ff) as u32;
        (ptr, len)
    }
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
    fn test_c_api() {
        let input = " 123 456 ";
        let handle = parse(input.as_ptr(), input.len(), 1);
        let (ptr, len) = handle.unpack();
        println!("{} {}", ptr, len);
        assert!(ptr > 0);
        assert!(len > 0);

        let bytes = unsafe { std::slice::from_raw_parts(ptr as usize as *const u8, len as usize) };
        let s = std::str::from_utf8(bytes).unwrap();
        assert!(s.len() > 0);

        //dealloc(handle);
    }
}
