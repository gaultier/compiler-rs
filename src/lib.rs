use crate::lex::Lexer;

pub mod error;
pub mod lex;
mod origin;

#[repr(transparent)]
pub struct WasmMemoryHandle(u64);

impl WasmMemoryHandle {
    fn new(ptr: usize, len: usize) -> Self {
        assert!(std::mem::size_of::<usize>() == 4);
        Self((ptr as u64) << 32 | (len as u64))
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn alloc_u8(size: usize) -> usize {
    let v: Vec<u8> = Vec::with_capacity(size);
    let ptr = v.as_ptr();
    std::mem::forget(v);
    ptr as usize
}

#[unsafe(no_mangle)]
pub extern "C" fn lex(in_ptr: *const u8, in_len: usize) -> WasmMemoryHandle {
    assert!(!in_ptr.is_null());

    let input_bytes = unsafe { &*std::ptr::slice_from_raw_parts(in_ptr, in_len) };
    let input_str = std::str::from_utf8(input_bytes).unwrap();

    let mut lexer = Lexer::new();
    lexer.lex(input_str);

    let json = miniserde::json::to_string(&(&lexer.tokens, &lexer.errors));

    let res = WasmMemoryHandle::new(json.as_ptr() as usize, json.len());
    std::mem::forget(json);
    res
}
