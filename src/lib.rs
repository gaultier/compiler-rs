pub mod amd64;
pub mod asm;
pub mod ast;
pub mod elf;
pub mod error;
pub mod ir;
pub mod lex;
pub mod macho;
mod origin;
pub mod register_alloc;
pub mod type_checker;
mod utils;

use std::{
    collections::{BTreeMap, HashMap},
    fmt::Write,
};

use log::trace;

use crate::{
    asm::{Encoding, Target},
    ast::{Node, Parser},
    error::Error,
    ir::VirtualRegister,
    lex::{Lexer, Token},
    origin::FileId,
    register_alloc::RegisterMapping,
    type_checker::Size,
};

#[cfg(target_arch = "wasm32")]
mod wasm32 {
    use crate::{
        asm::{Architecture, Encoding},
        ast::Node,
        error::Error,
        ir::{self, Instruction, LiveRanges},
        lex::Token,
        origin::FileId,
        register_alloc::{MemoryLocation, RegisterMapping},
    };
    use serde::Serialize;
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

    #[unsafe(no_mangle)]
    pub extern "C" fn wasm_compile(
        in_ptr: *const u8,
        in_len: usize,
        file_id: FileId,
        target_arch: Architecture,
    ) -> AllocHandle {
        let input_bytes = unsafe {
            std::ptr::slice_from_raw_parts(in_ptr, in_len)
                .as_ref()
                .unwrap()
        };
        let input_str = std::str::from_utf8(input_bytes).unwrap();

        let compiled = super::compile(input_str, file_id, target_arch);
        let json_compiled = JsonCompileResult {
            errors: compiled.errors,
            lex_tokens: compiled.lex_tokens,
            ast_nodes: compiled.ast_nodes,
            ir_fn_defs: compiled.ir_fn_defs,
            ir_text: compiled.ir_text,
            //ir_eval: compiled.ir_eval,
            //vreg_to_memory_location: compiled.vreg_to_memory_location,
            asm_encoded: compiled.asm_encoded,
        };

        let json = serde_json::to_string(&json_compiled).unwrap();

        let ptr = json.as_bytes().as_ptr() as u64;
        let len = json.len() as u32 as u64;
        println!("ptr={}", ptr);

        AllocHandle(ptr << 32 | len)
    }

    #[derive(Serialize, Default, Debug)]
    struct JsonCompileResult {
        pub errors: Vec<Error>,
        pub lex_tokens: Vec<Token>,
        pub ast_nodes: Vec<Node>,
        pub ir_fn_defs: Vec<ir::FnDef>,
        pub ir_text: String,
        //pub ir_live_ranges: LiveRanges,
        //pub ir_eval: ir::EvalResult,
        //pub vreg_to_memory_location: RegisterMapping,
        pub asm_encoded: Encoding,
    }
}

#[derive(Default, Debug)]
pub struct CompileResult {
    pub errors: Vec<Error>,
    pub lex_tokens: Vec<Token>,
    pub ast_nodes: Vec<Node>,
    pub ir_fn_defs: Vec<ir::FnDef>,
    pub ir_text: String,
    pub ir_eval: ir::Eval,
    pub vreg_to_memory_locations: Vec<RegisterMapping>,
    pub asm_instructions: Vec<asm::Instruction>,
    pub asm_text: String,
    pub asm_encoded: Encoding,
}

pub fn compile(
    input: &str,
    file_id: FileId,
    file_id_to_name: &HashMap<FileId, String>,
    target: &Target,
) -> CompileResult {
    let mut lexer = Lexer::new(file_id);
    lexer.lex(input);
    trace!("lexer: {:#?}", lexer);

    let mut parser = Parser::new(input, &lexer, file_id_to_name);
    parser.parse();
    trace!("ast_nodes: {:#?}", &parser.nodes);
    trace!("parser errors: {:#?}", parser.errors);

    let mut errors = parser.errors;
    errors.extend(type_checker::check_nodes(
        &parser.nodes,
        &mut parser.node_to_type,
        &parser.name_to_def,
    ));

    if !errors.is_empty() {
        return CompileResult {
            lex_tokens: parser.tokens,
            ast_nodes: parser.nodes,
            errors,
            ..Default::default()
        };
    }

    let mut ir_emitter = ir::Emitter::new(&parser.nodes, &parser.node_to_type, &parser.name_to_def);
    ir_emitter.emit_nodes();
    trace!("ir_emitter: {:#?}", ir_emitter);

    let mut ir_text = String::with_capacity(input.len() * 3);
    for fn_def in &ir_emitter.fn_defs {
        writeln!(&mut ir_text, "\n{} {{", fn_def).unwrap();

        for ins in &fn_def.instructions {
            write!(&mut ir_text, "  {}", ins).unwrap();
        }

        writeln!(&mut ir_text, "}}").unwrap();
    }
    trace!("ir_text: {}", &ir_text);

    //let ir_eval = ir::eval(&ir_emitter.instructions);
    //trace!("ir_eval: {:#?}", ir_eval);

    let mut asm_text = String::with_capacity(input.len() * 10); // Heuristic. TODO: Revisit.
    let mut asm_instructions = Vec::with_capacity(input.len() * 10);

    for fn_def in &ir_emitter.fn_defs {
        let vreg_to_size = fn_def
            .instructions
            .iter()
            .filter_map(|x| x.res_vreg.map(|vreg| (vreg, x.typ.size.unwrap())))
            .collect::<BTreeMap<VirtualRegister, Size>>();

        let (vreg_to_memory_location, stack_offset) =
            register_alloc::regalloc(&fn_def.live_ranges, &vreg_to_size, &asm::abi(&target.arch));
        trace!("vreg_to_memory_location: {:#?}", vreg_to_memory_location);

        let (fn_asm_instructions, _) =
            asm::emit_fn_def(fn_def, &vreg_to_memory_location, stack_offset, target);

        trace!(
            "asm_instructions: fn_name={} ins={:#?}",
            fn_def.name, fn_asm_instructions
        );
        writeln!(&mut asm_text, "{}:", &fn_def.name).unwrap();

        for ins in &fn_asm_instructions {
            writeln!(&mut asm_text, "  {}", ins.display(file_id_to_name)).unwrap();
        }
        writeln!(&mut asm_text, "\n").unwrap();
        // FIXME: Keep fn_def.instructions structure to be able to record each fn location in order
        // to be able to call functions.
        asm_instructions.extend(fn_asm_instructions);
    }

    trace!("asm_text: {}", &asm_text);

    let encoding = asm::encode(&asm_instructions, target, file_id_to_name);
    trace!(
        "asm encoded: entrypoint={:#X} bin={:#04X?}",
        encoding.entrypoint, &encoding.instructions
    );

    CompileResult {
        lex_tokens: parser.tokens,
        ast_nodes: vec![], //parser.nodes,
        errors,
        ir_fn_defs: ir_emitter.fn_defs,
        ir_text,
        ir_eval: ir::Eval::default(),
        vreg_to_memory_locations: Vec::new(),
        asm_instructions,
        asm_text,
        asm_encoded: encoding,
    }
}
