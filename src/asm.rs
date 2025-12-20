use std::{
    collections::BTreeMap,
    fmt::{Debug, Display},
    io::Write,
};

use log::trace;
use serde::Serialize;

use crate::{
    amd64,
    ir::{self},
    register_alloc::{MemoryLocation, RegisterMapping},
    type_checker::Size,
};

#[repr(u8)]
pub enum ArchKind {
    Amd64,
    // TODO
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

pub type EvalResult = BTreeMap<MemoryLocation, ir::EvalValue>;

impl Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Register::Amd64(register) => register.fmt(f),
        }
    }
}

pub fn eval(instructions: &[Instruction]) -> EvalResult {
    match instructions.first() {
        Some(Instruction::Amd64(_)) => {
            let mut interpreter = amd64::Interpreter::new();
            interpreter.eval(instructions);
            interpreter.state
        }
        _ => EvalResult::new(),
    }
}

pub(crate) fn abi(target_arch: &ArchKind) -> Abi {
    match target_arch {
        ArchKind::Amd64 => amd64::abi(),
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

pub(crate) fn emit(
    irs: &[ir::Instruction],
    vreg_to_memory_location: &RegisterMapping,
    stack_offset: isize,
    target_arch: &ArchKind,
) -> (Vec<Instruction>, Stack) {
    trace!("asm: stack_offset={}", stack_offset);

    match target_arch {
        ArchKind::Amd64 => {
            let mut emitter = amd64::Emitter::new(stack_offset);
            emitter.emit(irs, vreg_to_memory_location);

            (
                emitter.asm.into_iter().map(Instruction::Amd64).collect(),
                emitter.stack,
            )
        }
    }
}

impl Instruction {
    pub fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        match self {
            Instruction::Amd64(ins) => ins.write(w),
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
