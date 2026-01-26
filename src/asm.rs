use std::{
    collections::{BTreeMap, HashMap},
    fmt::{Debug, Display},
};

use log::trace;
use serde::Serialize;

use crate::{
    amd64,
    ir::{self},
    origin::{FileId, Origin},
    register_alloc::RegisterMapping,
};

#[repr(u8)]
pub enum Architecture {
    Amd64,
    // TODO
}

pub enum Os {
    Linux,
    MacOS,
}

pub struct Target {
    pub os: Os,
    pub arch: Architecture,
    // More: version, CPU features, etc.
}

pub enum BinaryFormat {
    Elf,
    MachO,
}

pub(crate) struct Abi {
    pub(crate) gprs: Vec<Register>,
}

#[derive(Serialize, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Register {
    Amd64(amd64::Register),
}

#[derive(Serialize, Debug)]
pub enum Instruction {
    Amd64(amd64::Instruction),
    // TODO
}

#[derive(Serialize, Debug, Clone, Copy)]
pub enum Visibility {
    Local,
    Global,
}

#[derive(Serialize, Debug, Clone, Copy)]
pub struct Symbol {
    pub location: usize,
    pub visibility: Visibility,
    pub origin: Origin,
}

#[derive(Serialize, Debug, Default)]
pub struct Encoding {
    pub instructions: Vec<u8>,
    pub entrypoint: usize,
    pub symbols: BTreeMap<String, Symbol>,
}

impl Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Register::Amd64(register) => std::fmt::Display::fmt(register, f),
        }
    }
}

pub(crate) fn abi(target_arch: &Architecture) -> Abi {
    match target_arch {
        Architecture::Amd64 => amd64::abi(),
    }
}

pub(crate) fn encode(
    instructions: &[Instruction],
    target: &Target,
    file_id_to_name: &HashMap<FileId, String>,
) -> Encoding {
    match target.arch {
        Architecture::Amd64 => amd64::encode(instructions, target, file_id_to_name),
    }
}

pub(crate) struct Stack {
    pub(crate) offset: isize,
}

impl Stack {
    pub(crate) fn new(initial_stack_value: isize) -> Self {
        Self {
            offset: initial_stack_value,
        }
    }

    // Intended to be used with `rbp` indexing i.e.: `mov [rbp-8], 1`.
    pub(crate) fn new_slot(&mut self, size: usize, align: usize) -> isize {
        assert_ne!(size, 0);
        assert_ne!(align, 0);
        assert!(align.is_power_of_two());

        let old_offset = self.offset;

        self.offset &= !(align as isize - 1);
        assert_eq!(self.offset % align as isize, 0);
        assert!(self.offset <= old_offset, "{} {}", self.offset, old_offset);

        self.offset -= size as isize;

        assert_ne!(self.offset, 0);

        self.offset
    }
}

pub(crate) fn emit_fn_def(
    fn_def: &ir::FnDef,
    vreg_to_memory_location: &RegisterMapping,
    stack_offset: isize,
    target: &Target,
) -> (Vec<Instruction>, Stack) {
    trace!("asm: stack_offset={}", stack_offset);

    match target.arch {
        Architecture::Amd64 => {
            let mut emitter = amd64::Emitter::new(stack_offset);
            emitter.emit_fn_def(fn_def, vreg_to_memory_location);

            (
                emitter.asm.into_iter().map(Instruction::Amd64).collect(),
                emitter.stack,
            )
        }
    }
}

pub struct InstructionFormatter<'a> {
    ins: &'a Instruction,
    file_id_to_name: &'a HashMap<FileId, String>,
}

impl<'a> Display for InstructionFormatter<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.ins {
            Instruction::Amd64(ins) => write!(f, "{}", ins.display(self.file_id_to_name)),
        }
    }
}

impl<'a> Instruction {
    pub(crate) fn display(
        &'a self,
        file_id_to_name: &'a HashMap<FileId, String>,
    ) -> InstructionFormatter<'a> {
        InstructionFormatter {
            ins: self,
            file_id_to_name,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_stack() {
        let mut stack = Stack::new(0);
        let off1 = stack.new_slot(1, 1); // byte.
        assert_eq!(off1, -1);
        assert_eq!(stack.offset, -1);

        let off2 = stack.new_slot(16, 8); // 2 qwords.
        assert_eq!(stack.offset, -24);
        assert_eq!(off2, -24);
    }
}
