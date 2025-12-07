use serde::Serialize;

use crate::{
    ast::{Node, NodeData},
    origin::Origin,
};

type VirtualRegister = u32;

#[derive(Serialize)]
struct MemoryLocation {}

#[derive(Serialize)]
struct Metadata {
    // Result of the IR instruction.
    vreg: VirtualRegister,
    memory_location: MemoryLocation,
}

#[derive(Serialize)]
enum InstructionKind {
    Add,
    Set, // Set virtual registers.
}

#[derive(Serialize)]
struct Instruction {
    kind: InstructionKind,
    args_count: u8,
    lhs: Operand,
    rhs: Operand,
    origin: Origin,
    // TODO: metadata.
}

#[derive(Serialize)]
enum OperandKind {
    VReg,
    Num,
}

#[derive(Serialize)]
enum Operand {
    Num(u64),
    VReg(u32),
}

struct Emitter {
    instructions: Vec<Instruction>,
}

impl Emitter {
    fn emit(&mut self, nodes: &[Node]) {
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
