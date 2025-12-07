use serde::Serialize;

use crate::{
    ast::{Node, NodeData},
    origin::Origin,
};

pub type VirtualRegister = u32;

#[derive(Serialize, Debug)]
pub struct MemoryLocation {}

#[derive(Serialize, Debug)]
pub struct Metadata {
    // Result of the IR instruction.
    pub vreg: VirtualRegister,
    pub memory_location: MemoryLocation,
}

#[derive(Serialize, Debug)]
pub enum InstructionKind {
    Add,
    Set, // Set virtual registers.
}

#[derive(Serialize, Debug)]
pub struct Instruction {
    pub kind: InstructionKind,
    pub args_count: u8,
    pub lhs: Operand,
    pub rhs: Operand,
    pub origin: Origin,
    // TODO: metadata.
}

#[derive(Serialize)]
pub enum OperandKind {
    VReg,
    Num,
}

#[derive(Serialize, Debug)]
pub enum Operand {
    Num(u64),
    VReg(u32),
}

pub struct Emitter {
    pub instructions: Vec<Instruction>,
}

impl Emitter {
    pub fn new() -> Self {
        Self {
            instructions: Vec::new(),
        }
    }

    pub fn emit(&mut self, nodes: &[Node]) {
        for node in nodes {
            match node.kind {
                crate::ast::NodeKind::Number => {
                    let num = match node.data {
                        Some(NodeData::Num(n)) => n,
                        _ => panic!("expected number but was not present"),
                    };
                    let metadata_idx: u32 = 1; // TODO
                    let ins = Instruction {
                        kind: InstructionKind::Set,
                        args_count: 1,
                        lhs: Operand::VReg(metadata_idx),
                        rhs: Operand::Num(num),
                        origin: node.origin,
                    };
                    self.instructions.push(ins);
                }
                crate::ast::NodeKind::Add => todo!(),
            }
        }
    }
}
