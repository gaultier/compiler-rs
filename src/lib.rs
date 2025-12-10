use std::alloc::Layout;

pub mod amd64;
pub mod asm;
pub mod ast;
pub mod error;
pub mod ir;
pub mod lex;
mod origin;
pub mod register_alloc;

use serde::Serialize;

use crate::{
    ast::{Node, Parser},
    error::Error,
    ir::{Instruction, Lifetimes},
    lex::{Lexer, Token},
    origin::FileId,
    register_alloc::RegAlloc,
};

#[cfg(target_arch = "wasm32")]
mod wasm32 {
    use std::alloc::GlobalAlloc;
    use std::alloc::Layout;

    const ARENA_SIZE: usize = 1 * 1024 * 1024;
    const PAGE_SIZE: usize = 64 * 1024;

    struct SimpleAllocator {
        initialized: std::cell::Cell<bool>,
        offset: std::cell::Cell<usize>,
    }

    impl SimpleAllocator {
        fn os_alloc(&self) -> usize {
            let page_count = ARENA_SIZE / PAGE_SIZE;
            core::arch::wasm32::memory_grow(0, page_count);
            0
        }
    }

    #[global_allocator]
    static ALLOCATOR: SimpleAllocator = SimpleAllocator {
        initialized: std::cell::Cell::new(false),
        offset: std::cell::Cell::new(0),
    };

    unsafe impl Sync for SimpleAllocator {}

    unsafe impl GlobalAlloc for SimpleAllocator {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            let size = layout.size();
            let align = layout.align();

            // Once.
            if !self.initialized.get() {
                self.os_alloc();
                self.initialized.set(true);
                // HACK: Rust does not like pointers with a value of 0
                // so we 'do' a dummy allocation.
                self.offset.set(8);
            }

            let offset = self.offset.get();
            let padding = (0usize).wrapping_sub(offset) & (align - 1);
            assert!(padding <= align);

            if padding + offset + size > ARENA_SIZE {
                panic!();
            }

            let allocated = offset + padding;
            assert!(allocated % align == 0);
            self.offset.set(offset + padding + size);
            allocated as *mut u8
        }

        unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {}
    }

    #[unsafe(no_mangle)]
    pub extern "C" fn alloc_get_size() -> usize {
        return ALLOCATOR.offset.get();
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn dealloc() {
    todo!()
}

#[unsafe(no_mangle)]
pub extern "C" fn alloc_u8(size: usize) -> usize {
    let layout = Layout::from_size_align(size, std::mem::align_of::<u8>()).unwrap();
    let ptr = unsafe { std::alloc::alloc(layout) };
    ptr as usize
}

#[repr(transparent)]
pub struct AllocHandle(u64);

impl AllocHandle {
    pub fn unpack(&self) -> (u32, u32) {
        let ptr = (self.0 >> 32) as u32;
        let len = (self.0 & 0xff_ff_ff_ff) as u32;
        (ptr, len)
    }
}

#[derive(Serialize)]
pub struct CompileResult<'a> {
    pub errors: &'a [Error],
    pub lex_tokens: &'a [Token],
    pub ast_nodes: &'a [Node],
    pub ir_instructions: &'a [Instruction],
    pub ir_text: String,
    pub ir_lifetimes: &'a Lifetimes,
    pub ir_eval: &'a ir::EvalResult,
    pub regalloc: &'a RegAlloc,
    pub amd64_instructions: &'a [amd64::Instruction],
    pub asm_text: String,
}

#[unsafe(no_mangle)]
pub extern "C" fn compile(in_ptr: *const u8, in_len: usize, file_id: FileId) -> AllocHandle {
    let input_bytes = unsafe {
        std::ptr::slice_from_raw_parts(in_ptr, in_len)
            .as_ref()
            .unwrap()
    };
    let input_str = std::str::from_utf8(input_bytes).unwrap();

    let mut lexer = Lexer::new(file_id);
    lexer.lex(input_str);

    let mut parser = Parser::new(input_str, &lexer);
    parser.parse();

    let mut ir_emitter = ir::Emitter::new();
    ir_emitter.emit(&parser.nodes);

    let mut ir_text = Vec::with_capacity(in_len * 3);
    for ins in &ir_emitter.instructions {
        ins.write(&mut ir_text).unwrap();
    }
    let eval = ir::eval(&ir_emitter.instructions);

    let target_arch = asm::ArchKind::Amd64;
    let vcode = asm::ir_to_vcode(&ir_emitter.instructions, &target_arch);

    let regalloc = register_alloc::regalloc(&vcode, &ir_emitter.lifetimes, &asm::abi(&target_arch));

    let mut asm_emitter = amd64::Emitter::new();
    asm_emitter.emit(&ir_emitter.instructions, &regalloc);

    let mut asm_text = Vec::with_capacity(asm_emitter.instructions.len() * 8);
    for ins in &asm_emitter.instructions {
        ins.write(&mut asm_text).unwrap();
    }

    let parser_response = CompileResult {
        lex_tokens: &parser.tokens,
        ast_nodes: &parser.nodes,
        errors: &parser.errors,
        ir_instructions: &ir_emitter.instructions,
        ir_text: String::from_utf8(ir_text).unwrap(),
        ir_lifetimes: &ir_emitter.lifetimes,
        ir_eval: &eval,
        regalloc: &regalloc,
        amd64_instructions: &asm_emitter.instructions,
        asm_text: String::from_utf8(asm_text).unwrap(),
    };
    let json = serde_json::to_string(&parser_response).unwrap();

    let ptr = json.as_bytes().as_ptr() as u64;
    let len = json.len() as u32 as u64;
    println!("ptr={}", ptr);

    AllocHandle(ptr << 32 | len)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_c_api() {
        let base = 3;
        let align = 8;
        let padding = (0usize).wrapping_sub(base) & (align - 1);
        assert_eq!(padding + base, align);

        let input = "123 +1+32444444444444444";
        let input_alloc = alloc_u8(input.len()) as *mut u8;
        let input_slice = unsafe { std::slice::from_raw_parts_mut(input_alloc, input.len()) };
        input_slice.copy_from_slice(input.as_bytes());

        let handle = compile(input_slice.as_ptr(), input_slice.len(), 1);
        let (ptr, len) = handle.unpack();
        println!("handle={} ptr={} len={}", handle.0, ptr, len);
        assert!(ptr > 0);
        assert!(len > 0);

        //let bytes = unsafe { std::slice::from_raw_parts(ptr as usize as *const u8, len as usize) };
        //let s = std::str::from_utf8(bytes).unwrap();
        //assert!(s.len() > 0);
        //
        //dealloc(handle);
    }
}
