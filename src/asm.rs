use std::{
    collections::{BTreeMap, HashMap},
    fmt::Display,
    io::Write,
};

use serde::Serialize;

use crate::{
    amd64,
    ir::{self},
    origin::Origin,
    register_alloc::{MemoryLocation, RegisterMapping},
};

#[repr(u8)]
pub enum ArchKind {
    Amd64,
    // TODO
}

pub(crate) struct Abi {
    pub(crate) gprs: Vec<Register>,
}

#[derive(Serialize, Debug, Clone, Copy)]
pub enum OperandSize {
    _8 = 1,
    _16 = 2,
    _32 = 4,
    _64 = 8,
}

#[derive(Serialize, Debug, Clone, Copy)]
pub enum InstructionKind {
    Amd64(amd64::InstructionKind),
}

#[derive(Serialize, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Register {
    Amd64(amd64::Register),
}

#[derive(Serialize, Debug, Clone)]
pub struct Operand {
    pub operand_size: OperandSize,
    pub kind: OperandKind,
}

#[derive(Serialize, Debug, Clone)]
pub enum OperandKind {
    Register(Register),
    Immediate(i64),
    Stack(isize),
    FnName(String),
}

#[derive(Serialize, Debug)]
pub struct Instruction {
    pub kind: InstructionKind,
    pub operands: Vec<Operand>,
    pub origin: Origin,
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
    match instructions.first().map(|ins| ins.kind) {
        Some(InstructionKind::Amd64(_)) => {
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

impl Operand {
    pub(crate) fn from_memory_location(operand_size: &OperandSize, loc: &MemoryLocation) -> Self {
        Self {
            operand_size: *operand_size,
            kind: loc.into(),
        }
    }

    pub fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        match &self.kind {
            OperandKind::Register(register) => w.write_all(register.to_str().as_bytes()),
            OperandKind::Immediate(n) => write!(w, "{}", n),
            OperandKind::FnName(name) => w.write_all(name.as_bytes()),
            OperandKind::Stack(off) => {
                self.operand_size.write(w)?;
                write!(w, " [rbp {:+}]", off)
            }
        }
    }

    pub(crate) fn is_reg(&self) -> bool {
        matches!(self.kind, OperandKind::Register(_))
    }

    pub(crate) fn is_imm(&self) -> bool {
        matches!(self.kind, OperandKind::Immediate(_))
    }

    pub(crate) fn is_imm32(&self) -> bool {
        matches!(self.kind, OperandKind::Immediate(imm) if imm <= i32::MAX as i64)
    }

    pub(crate) fn is_mem(&self) -> bool {
        matches!(self.kind, OperandKind::Stack(_))
    }

    pub(crate) fn is_rm(&self) -> bool {
        self.is_reg() || self.is_mem()
    }

    pub(crate) fn as_amd64_reg(&self) -> amd64::Register {
        match self.kind {
            OperandKind::Register(Register::Amd64(reg)) => reg,
            _ => panic!("not a register"),
        }
    }

    pub(crate) fn as_reg(&self) -> Register {
        match self.kind {
            OperandKind::Register(reg) => reg,
            _ => panic!("not a register"),
        }
    }

    pub(crate) fn as_imm(&self) -> i64 {
        match self.kind {
            OperandKind::Immediate(imm) => imm,
            _ => panic!("not an immediate"),
        }
    }
}

impl Instruction {
    pub fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        w.write_all(self.kind.to_str().as_bytes())?;

        self.operands.iter().enumerate().try_for_each(|(i, o)| {
            if i == 0 {
                write!(w, " ")?;
            } else {
                write!(w, ", ")?;
            }
            o.write(w)
        })?;

        w.write_all(b" // ")?;
        self.origin.write(w, &HashMap::new() /* FIXME */)?;

        writeln!(w)
    }
}

impl InstructionKind {
    pub(crate) fn to_str(self) -> &'static str {
        match self {
            InstructionKind::Amd64(instruction_kind) => instruction_kind.to_str(),
        }
    }
}

impl From<&MemoryLocation> for OperandKind {
    fn from(value: &MemoryLocation) -> Self {
        match value {
            MemoryLocation::Register(reg) => OperandKind::Register(*reg),
            MemoryLocation::Stack(off) => OperandKind::Stack(*off),
        }
    }
}

impl From<MemoryLocation> for OperandKind {
    fn from(value: MemoryLocation) -> Self {
        (&value).into()
    }
}

impl From<&OperandKind> for MemoryLocation {
    fn from(value: &OperandKind) -> Self {
        match value {
            OperandKind::Register(register) => MemoryLocation::Register(*register),
            OperandKind::Immediate(_imm) => panic!(),
            OperandKind::Stack(off) => MemoryLocation::Stack(*off),
            OperandKind::FnName(_) => todo!(),
        }
    }
}

impl From<OperandKind> for MemoryLocation {
    fn from(value: OperandKind) -> Self {
        (&value).into()
    }
}

impl Register {
    pub(crate) fn to_str(self) -> &'static str {
        match self {
            Register::Amd64(r) => r.to_str(),
        }
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

    pub(crate) fn is_aligned(&self, align: usize) -> bool {
        (self.offset as usize).is_multiple_of(align)
    }

    // Intended to be used with `rbp` indexing i.e.: `mov [rbp-8], 1`.
    pub(crate) fn new_slot(&mut self, size: usize, align: usize) -> isize {
        assert_ne!(size, 0);
        assert_ne!(align, 0);

        let padding = (0usize).wrapping_sub(self.offset as usize) & (align - 1);
        assert!(padding <= align);

        self.offset -= (size + padding) as isize;

        assert_ne!(self.offset, 0);

        self.offset
    }
}

pub(crate) fn emit(
    irs: &[ir::Instruction],
    vreg_to_memory_location: &RegisterMapping,
    target_arch: &ArchKind,
) -> (Vec<Instruction>, Stack) {
    match target_arch {
        ArchKind::Amd64 => {
            // Assume we are always in `main` or one of its callees and thus
            // `sp % 16 == -8` since a `call` just happened and thus the
            // return address is on the stack.
            let mut emitter = amd64::Emitter::new(-8);
            emitter.emit(irs, vreg_to_memory_location);

            (
                emitter
                    .asm
                    .into_iter()
                    .map(|x| Instruction {
                        kind: InstructionKind::Amd64(x.kind),
                        operands: x.operands,
                        origin: x.origin,
                    })
                    .collect(),
                emitter.stack,
            )
        }
    }
}

impl OperandSize {
    pub(crate) fn as_bytes_count(&self) -> usize {
        match self {
            OperandSize::_8 => 1,
            OperandSize::_16 => 2,
            OperandSize::_32 => 4,
            OperandSize::_64 => 8,
        }
    }

    pub fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        match self {
            OperandSize::_8 => w.write_all(b"BYTE PTR"),
            OperandSize::_16 => w.write_all(b"WORD PTR"),
            OperandSize::_32 => w.write_all(b"DWORD PTR"),
            OperandSize::_64 => w.write_all(b"QWORD PTR"),
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
