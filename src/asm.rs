use std::{collections::BTreeMap, io::Write};

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
    One = 1,
    Two = 2,
    Four = 4,
    Eight = 8,
}

#[derive(Serialize, Debug, Clone, Copy)]
pub enum InstructionKind {
    Amd64(amd64::InstructionKind),
}

#[derive(Serialize, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Register {
    Amd64(amd64::Register),
}

#[derive(Serialize, Debug, Clone, Copy)]
pub struct Operand {
    pub operand_size: OperandSize,
    pub kind: OperandKind,
}

#[derive(Serialize, Debug, Clone, Copy)]
pub enum OperandKind {
    Register(Register),
    Immediate(u64),
    Stack(usize),
}

#[derive(Serialize, Debug)]
pub struct Instruction {
    pub kind: InstructionKind,
    pub operands: Vec<Operand>,
    pub origin: Origin,
}

pub type EvalResult = BTreeMap<MemoryLocation, ir::Value>;

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
    pub(crate) fn new(operand_size: &OperandSize, kind: &OperandKind) -> Self {
        Self {
            operand_size: *operand_size,
            kind: *kind,
        }
    }

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
            OperandKind::Stack(off) => write!(w, "sp + {}", off),
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

        writeln!(w)
    }
}

impl InstructionKind {
    pub(crate) fn arch(&self) -> ArchKind {
        match self {
            InstructionKind::Amd64(_) => ArchKind::Amd64,
        }
    }

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

impl From<&OperandKind> for MemoryLocation {
    fn from(value: &OperandKind) -> Self {
        match value {
            OperandKind::Register(register) => MemoryLocation::Register(*register),
            OperandKind::Immediate(_imm) => panic!(),
            OperandKind::Stack(off) => MemoryLocation::Stack(*off),
        }
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
    pub(crate) offset: usize,
}

impl Stack {
    pub(crate) fn new() -> Self {
        Self { offset: 0 }
    }

    pub(crate) fn new_slot(&mut self, size: usize, align: usize) -> usize {
        let padding = (0usize).wrapping_sub(self.offset) & (align - 1);
        let res = self.offset + padding;

        self.offset += res + size;

        res
    }
}

pub(crate) fn emit(
    irs: &[ir::Instruction],
    vreg_to_memory_location: &RegisterMapping,
    target_arch: &ArchKind,
) -> (Vec<Instruction>, Stack) {
    match target_arch {
        ArchKind::Amd64 => amd64::emit(irs, vreg_to_memory_location),
    }
}
