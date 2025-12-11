use std::alloc::Layout;

pub mod amd64;
pub mod asm;
pub mod ast;
pub mod error;
pub mod ir;
pub mod lex;
mod origin;
pub mod register_alloc;

use log::trace;
use serde::Serialize;

use crate::{
    asm::ArchKind,
    ast::{Node, Parser},
    error::Error,
    ir::{Instruction, LiveRanges},
    lex::{Lexer, Token},
    origin::FileId,
    register_alloc::{MemoryLocation, RegisterMapping},
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

#[derive(Serialize, Default, Debug)]
pub struct CompileResult {
    pub errors: Vec<Error>,
    pub lex_tokens: Vec<Token>,
    pub ast_nodes: Vec<Node>,
    pub ir_instructions: Vec<Instruction>,
    pub ir_text: String,
    pub ir_live_ranges: LiveRanges,
    pub ir_eval: ir::EvalResult,
    pub vcode: Vec<asm::VInstruction>,
    pub vreg_to_memory_location: RegisterMapping,
    pub asm_instructions: Vec<asm::Instruction>,
    pub asm_text: String,
    pub asm_eval: asm::EvalResult,
}

#[derive(Serialize, Default, Debug)]
struct JsonCompileResult {
    pub errors: Vec<Error>,
    pub lex_tokens: Vec<Token>,
    pub ast_nodes: Vec<Node>,
    pub ir_instructions: Vec<Instruction>,
    pub ir_text: String,
    pub ir_live_ranges: LiveRanges,
    pub ir_eval: ir::EvalResult,
    pub vcode: Vec<asm::VInstruction>,
    pub vreg_to_memory_location: RegisterMapping,
    pub asm_instructions: Vec<asm::Instruction>,
    pub asm_text: String,
    pub asm_eval: Vec<(MemoryLocation, ir::Value)>,
}

pub fn compile(input: &str, file_id: FileId, target_arch: ArchKind) -> CompileResult {
    let mut lexer = Lexer::new(file_id);
    lexer.lex(input);
    trace!("lexer: {:#?}", lexer);

    let mut parser = Parser::new(input, &lexer);
    parser.parse();
    trace!("parser: {:#?}", parser);

    if !parser.errors.is_empty() {
        return CompileResult {
            lex_tokens: parser.tokens,
            ast_nodes: parser.nodes,
            errors: parser.errors,
            ..Default::default()
        };
    }

    let mut ir_emitter = ir::Emitter::new();
    ir_emitter.emit(&parser.nodes);
    trace!("ir_emitter: {:#?}", ir_emitter);

    let mut ir_text = Vec::with_capacity(input.len() * 3);
    for ins in &ir_emitter.instructions {
        ins.write(&mut ir_text).unwrap();
    }
    trace!("ir_text: {}", unsafe { str::from_utf8_unchecked(&ir_text) });

    let ir_eval = ir::eval(&ir_emitter.instructions);
    trace!("ir_eval: {:#?}", ir_eval);

    let vcode = asm::ir_to_vcode(&ir_emitter.instructions, &target_arch);
    trace!("vcode: {:#?}", vcode);

    let mut vreg_to_memory_location =
        register_alloc::regalloc(&vcode, &ir_emitter.live_ranges, &asm::abi(&target_arch));
    trace!("vreg_to_memory_location: {:#?}", vreg_to_memory_location);

    let mut asm_emitter = asm::Emitter::new();
    let asm_instructions = asm_emitter.vcode_to_asm(&vcode, &mut vreg_to_memory_location);
    trace!("asm_instructions: {:#?}", asm_instructions);

    let mut asm_text = Vec::with_capacity(asm_instructions.len() * 8);
    for ins in &asm_instructions {
        ins.write(&mut asm_text).unwrap();
    }
    trace!("asm_text: {}", unsafe {
        str::from_utf8_unchecked(&asm_text)
    });

    let asm_eval = asm::eval(&asm_instructions);
    trace!("asm_eval: {:#?}", asm_eval);

    CompileResult {
        lex_tokens: parser.tokens,
        ast_nodes: parser.nodes,
        errors: parser.errors,
        ir_instructions: ir_emitter.instructions,
        ir_text: String::from_utf8(ir_text).unwrap(),
        ir_live_ranges: ir_emitter.live_ranges,
        ir_eval,
        vcode,
        vreg_to_memory_location,
        asm_instructions,
        asm_text: String::from_utf8(asm_text).unwrap(),
        asm_eval,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn wasm_compile(
    in_ptr: *const u8,
    in_len: usize,
    file_id: FileId,
    target_arch: ArchKind,
) -> AllocHandle {
    let input_bytes = unsafe {
        std::ptr::slice_from_raw_parts(in_ptr, in_len)
            .as_ref()
            .unwrap()
    };
    let input_str = std::str::from_utf8(input_bytes).unwrap();

    let compiled = compile(input_str, file_id, target_arch);
    let json_compiled = JsonCompileResult {
        errors: compiled.errors,
        lex_tokens: compiled.lex_tokens,
        ast_nodes: compiled.ast_nodes,
        ir_instructions: compiled.ir_instructions,
        ir_text: compiled.ir_text,
        ir_live_ranges: compiled.ir_live_ranges,
        ir_eval: compiled.ir_eval,
        vcode: compiled.vcode,
        vreg_to_memory_location: compiled.vreg_to_memory_location,
        asm_instructions: compiled.asm_instructions,
        asm_text: compiled.asm_text,
        asm_eval: compiled.asm_eval.into_iter().collect(),
    };

    let json = serde_json::to_string(&json_compiled).unwrap();

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

        let handle = wasm_compile(input_slice.as_ptr(), input_slice.len(), 1, ArchKind::Amd64);
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

    #[test]
    fn test_api() {
        let input = "123 *2+32";

        let compiled = compile(&input, 1, ArchKind::Amd64);
        assert_eq!(compiled.errors.len(), 0);
        assert_eq!(compiled.lex_tokens.len(), 6 /* including EOF */);
        assert_eq!(compiled.ast_nodes.len(), 5);
        assert_eq!(compiled.ir_instructions.len(), 5);
        assert_eq!(compiled.asm_instructions.len(), 7);
        assert_eq!(
            compiled.vreg_to_memory_location.len(),
            compiled.asm_eval.len()
        );

        for (vreg, ir_val) in &compiled.ir_eval {
            let preg = &compiled.vreg_to_memory_location[vreg];
            let asm_val = compiled.asm_eval.get(&preg).unwrap();
            assert_eq!(ir_val, asm_val);
        }
    }
}
