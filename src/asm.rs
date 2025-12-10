use serde::Serialize;

use crate::register_alloc::Register;

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
