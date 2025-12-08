use std::io::Write;

use serde::Serialize;

use crate::{
    ast::{Node, NodeData},
    origin::Origin,
};

#[repr(transparent)]
#[derive(Serialize, Debug, Clone, Copy)]
pub struct VirtualRegister(u32);

#[derive(Serialize, Debug)]
pub struct MemoryLocation {}

#[derive(Serialize, Debug)]
pub enum InstructionKind {
    Add,
    Set, // Set virtual registers.
}

#[derive(Serialize, Debug)]
pub struct Instruction {
    pub kind: InstructionKind,
    pub args_count: u8,
    pub lhs: Option<Operand>,
    pub rhs: Option<Operand>,
    pub origin: Origin,
    pub res_vreg: VirtualRegister,
    // TODO: type, lifetime.
}

#[derive(Serialize)]
pub enum OperandKind {
    VReg,
    Num,
}

#[derive(Serialize, Debug)]
pub enum Operand {
    Num(u64),
    VReg(VirtualRegister),
}

pub struct Emitter {
    pub instructions: Vec<Instruction>,
    vreg: VirtualRegister,
}

impl Emitter {
    pub fn new() -> Self {
        Self {
            instructions: Vec::new(),
            vreg: VirtualRegister(0),
        }
    }

    fn make_vreg(&mut self) -> VirtualRegister {
        self.vreg.0 += 1;
        self.vreg
    }

    pub fn emit(&mut self, nodes: &[Node]) {
        let mut stack = Vec::new();

        for node in nodes {
            match node.kind {
                crate::ast::NodeKind::Number => {
                    let num = match node.data {
                        Some(NodeData::Num(n)) => n,
                        _ => panic!("expected number but was not present"),
                    };
                    let res_vreg = self.make_vreg();
                    let ins = Instruction {
                        kind: InstructionKind::Set,
                        args_count: 1,
                        lhs: Some(Operand::Num(num)),
                        rhs: None,
                        origin: node.origin,
                        res_vreg,
                    };
                    self.instructions.push(ins);
                    stack.push(res_vreg);
                }
                crate::ast::NodeKind::Add => {
                    // TODO: Checks.
                    let rhs = stack.pop().unwrap();
                    let lhs = stack.pop().unwrap();

                    let res_vreg = self.make_vreg();

                    let ins = Instruction {
                        kind: InstructionKind::Add,
                        args_count: 2,
                        lhs: Some(Operand::VReg(lhs)),
                        rhs: Some(Operand::VReg(rhs)),
                        origin: node.origin,
                        res_vreg,
                    };
                    self.instructions.push(ins);
                    stack.push(res_vreg);
                }
            }
        }
    }
}

impl Operand {
    pub fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        match self {
            Operand::Num(n) => {
                write!(w, "(u64.const {})", n)
            }
            Operand::VReg(r) => write!(w, "(vreg {})", r.0),
        }
    }
}

impl Instruction {
    pub fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        match self.kind {
            InstructionKind::Add => {
                write!(w, "add ")?;
                write!(w, "(vreg {}) ", self.res_vreg.0)?;

                if let Some(lhs) = &self.lhs {
                    lhs.write(w)?;
                }
                write!(w, " ")?;

                if let Some(rhs) = &self.rhs {
                    rhs.write(w)?;
                }
            }
            InstructionKind::Set => {
                write!(w, "set ")?;
                write!(w, "(vreg {}) ", self.res_vreg.0)?;

                if let Some(lhs) = &self.lhs {
                    lhs.write(w)?;
                }

                write!(w, " ")?;

                if let Some(rhs) = &self.rhs {
                    rhs.write(w)?;
                }
            }
        };

        writeln!(w)
    }
}
