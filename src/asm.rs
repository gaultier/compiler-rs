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

#[derive(Serialize, Debug)]
pub struct VInstruction {
    pub kind: InstructionKind,
    pub operands: Vec<ir::Operand>,
    pub origin: Origin,
}

#[derive(Serialize, Debug, Clone, Copy)]
pub enum Mutability {
    Read,
    Write,
    ReadWrite,
}

#[derive(Serialize, Debug, Clone, Copy)]
pub struct Operand {
    pub operand_size: OperandSize,
    pub kind: OperandKind,
    pub implicit: bool,
    pub mutability: Mutability,
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

pub(crate) fn ir_to_vcode(irs: &[ir::Instruction], target_arch: &ArchKind) -> Vec<VInstruction> {
    match target_arch {
        ArchKind::Amd64 => amd64::ir_to_vcode(irs),
    }
}

pub(crate) fn abi(target_arch: &ArchKind) -> Abi {
    match target_arch {
        ArchKind::Amd64 => amd64::abi(),
    }
}

impl Operand {
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

        self.operands
            .iter()
            .filter(|o| !o.implicit)
            .enumerate()
            .map(|(i, o)| {
                if i == 0 {
                    write!(w, " ")?;
                } else {
                    write!(w, ", ")?;
                }
                o.write(w)
            })
            .collect::<std::io::Result<()>>()?;

        writeln!(w)
    }
}

impl InstructionKind {
    pub(crate) fn to_str(self) -> &'static str {
        match self {
            InstructionKind::Amd64(instruction_kind) => instruction_kind.to_str(),
        }
    }

    pub(crate) fn get_in_out(&self) -> Vec<format::Operand> {
        match self {
            InstructionKind::Amd64(k) => k.get_in_out(),
        }
    }
}

impl OperandKind {
    pub(crate) fn is_immediate(&self) -> bool {
        matches!(self, OperandKind::Immediate(_))
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

impl VInstruction {
    pub fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        w.write_all(self.kind.to_str().as_bytes())?;

        for op in &self.operands {
            write!(w, " ")?;
            op.write(w)?;
        }

        writeln!(w)
    }
}

pub(crate) struct Stack {
    pub(crate) offset: usize,
}

pub(crate) struct Emitter {
    stack: Stack,
}

impl Stack {
    pub(crate) fn new_slot(&mut self, size: usize, align: usize) -> usize {
        let padding = (0usize).wrapping_sub(self.offset) & (align - 1);
        let res = self.offset + padding;

        self.offset += res + size;

        res
    }
}

impl Emitter {
    pub(crate) fn new() -> Self {
        Self {
            stack: Stack { offset: 0 },
        }
    }

    pub(crate) fn vcode_to_asm(
        &mut self,
        vcode: &[VInstruction],
        vreg_to_memory_location: &RegisterMapping,
    ) -> Vec<Instruction> {
        let mut instructions = Vec::with_capacity(vcode.len());

        for vins in vcode {
            let in_out = vins.kind.get_in_out();
            for (i, fmt_op) in in_out.iter().enumerate() {
                match fmt_op {
                    format::Operand {
                        location: format::Location::FixedRegister(fixed_preg),
                        mutability,
                        ..
                    } => {
                        let op = vins.operands[i];
                        match op {
                            ir::Operand::VirtualRegister(vreg) => {
                                match vreg_to_memory_location.get(&vreg) {
                                    Some(MemoryLocation::Register(preg)) if preg != fixed_preg => {
                                        let _stack_offset = self.stack.new_slot(8, 8); // FIXME
                                        todo!(
                                            "need to shuffle registers around for an instruction with an operand that requires a fixed register"
                                        );
                                    }
                                    Some(MemoryLocation::Stack(_off)) => todo!(),
                                    _ => {}
                                }
                            }
                            _ => {}
                        }
                    }
                    _ => {}
                }
            }

            let operands = vins
                .operands
                .iter()
                .map(|op| match op {
                    ir::Operand::VirtualRegister(vreg) => match vreg_to_memory_location.get(vreg) {
                        Some(MemoryLocation::Register(preg)) => Operand {
                            operand_size: OperandSize::Eight,
                            kind: OperandKind::Register(*preg),
                            // FIXME
                            implicit: false,
                            mutability: Mutability::Read,
                        },
                        Some(MemoryLocation::Stack(_)) => todo!(),
                        None => panic!("vreg does not have a preg"),
                    },
                    ir::Operand::Num(num) => Operand {
                        operand_size: OperandSize::Eight,
                        kind: OperandKind::Immediate(*num),
                        implicit: false,
                        mutability: Mutability::Read,
                    },
                })
                .collect::<Vec<Operand>>();

            let ins = Instruction {
                kind: vins.kind,
                operands,
                origin: vins.origin,
            };
            instructions.push(ins);
        }

        instructions
    }
}

pub(crate) mod format {
    use crate::asm::{Mutability, Register};

    pub(crate) enum Location {
        // Fixed registers.
        FixedRegister(Register),

        Imm64,
        Rm64,
        R64,
        Memory, // Memory
    }

    pub(crate) struct Operand {
        pub(crate) location: Location,
        pub(crate) mutability: Mutability,
        pub(crate) implicit: bool,
        // TODO: extension, align
    }
}
