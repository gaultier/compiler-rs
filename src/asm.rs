use serde::Serialize;

use crate::{
    amd64,
    ir::{self, Operand},
    origin::Origin,
    register_alloc::Register,
};

pub enum ArchKind {
    Amd64,
    // TODO
}

pub struct Abi {
    pub arch_kind: ArchKind,
    pub gprs: Vec<Register>,
}

#[derive(Serialize, Debug, Clone, Copy)]
pub enum OperandSize {
    One = 1,
    Two = 2,
    Four = 4,
    Eight = 8,
}

#[derive(Serialize, Debug)]
pub enum InstructionKind {
    Amd64(amd64::InstructionKind),
}

#[derive(Serialize, Debug)]
pub struct VInstruction {
    pub kind: InstructionKind,
    pub lhs: Option<Operand>,
    pub rhs: Option<Operand>,
    pub origin: Origin,
}

pub fn ir_to_vcode(irs: &[ir::Instruction], target_arch: &ArchKind) -> Vec<VInstruction> {
    match target_arch {
        ArchKind::Amd64 => amd64::ir_to_vcode(irs),
    }
}

pub fn abi(target_arch: &ArchKind) -> Abi {
    match target_arch {
        ArchKind::Amd64 => amd64::abi(),
    }
}
