use std::{collections::BTreeMap, io::Write};

use serde::Serialize;

use crate::{
    ast::{Node, NodeData},
    origin::Origin,
};

#[derive(Serialize, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct VirtualRegister(u32);

//pub enum VirtualRegisterConstraint {
//    Result,
//}

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
    pub res_vreg: Option<VirtualRegister>,
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
    VirtualRegister(VirtualRegister),
}

#[derive(Serialize, Debug)]
pub struct Lifetime {
    pub(crate) start: u32,
    pub(crate) end: u32, // Inclusive.
}

pub type Lifetimes = BTreeMap<VirtualRegister, Lifetime>;
//pub type Constraints = BTreeMap<VirtualRegister, VirtualRegisterConstraint>;

pub struct Emitter {
    pub instructions: Vec<Instruction>,
    vreg: VirtualRegister,
    pub lifetimes: Lifetimes,
    //pub constraints: Constraints,
}

impl Emitter {
    pub fn new() -> Self {
        Self {
            instructions: Vec::new(),
            vreg: VirtualRegister(0),
            lifetimes: Lifetimes::new(),
            //constraints: Constraints::new(),
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
                        res_vreg: Some(res_vreg),
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
                        lhs: Some(Operand::VirtualRegister(lhs)),
                        rhs: Some(Operand::VirtualRegister(rhs)),
                        origin: node.origin,
                        res_vreg: Some(res_vreg),
                    };
                    self.instructions.push(ins);
                    stack.push(res_vreg);
                }
            }
        }

        self.lifetimes = self.compute_lifetimes();
    }

    fn extend_lifetime_on_use(vreg: VirtualRegister, ins_position: u32, lifetimes: &mut Lifetimes) {
        lifetimes.entry(vreg).and_modify(|e| e.end = ins_position);
    }

    fn compute_lifetimes(&self) -> Lifetimes {
        let mut res = Lifetimes::new();

        for (i, ins) in self.instructions.iter().enumerate() {
            match ins.kind {
                InstructionKind::Add | InstructionKind::Set => {
                    let res_vreg = ins.res_vreg.unwrap();
                    assert!(res_vreg.0 > 0);

                    let lifetime = Lifetime {
                        start: i as u32,
                        end: i as u32,
                    };
                    res.insert(res_vreg, lifetime);

                    if let Some(Operand::VirtualRegister(vreg)) = &ins.lhs {
                        Self::extend_lifetime_on_use(*vreg, i as u32, &mut res);
                    }
                    if let Some(Operand::VirtualRegister(vreg)) = &ins.rhs {
                        Self::extend_lifetime_on_use(*vreg, i as u32, &mut res);
                    }
                }
            }
        }

        res
    }
}

impl Operand {
    pub fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        match self {
            Operand::Num(n) => {
                write!(w, "(u64.const {})", n)
            }
            Operand::VirtualRegister(r) => write!(w, "(vreg {})", r.0),
        }
    }
}

impl Instruction {
    pub fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        if let Some(vreg) = self.res_vreg {
            write!(w, "v{} := ", vreg.0)?;
        }

        match self.kind {
            InstructionKind::Add => {
                write!(w, "add ")?;

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

#[derive(Serialize, Copy, Clone, Debug)]
pub enum Value {
    Num(u64),
}

pub type EvalResult = BTreeMap<VirtualRegister, Value>;

pub fn eval(irs: &[Instruction]) -> EvalResult {
    let mut res = EvalResult::new();

    for ir in irs {
        match ir.kind {
            InstructionKind::Add => {
                let lhs = match ir.lhs.as_ref().unwrap() {
                    Operand::Num(num) => Value::Num(*num),
                    Operand::VirtualRegister(vreg) => res.get(&vreg).unwrap().clone(),
                };
                let rhs = match ir.rhs.as_ref().unwrap() {
                    Operand::Num(num) => Value::Num(*num),
                    Operand::VirtualRegister(vreg) => res.get(&vreg).unwrap().clone(),
                };
                let sum = match (lhs, rhs) {
                    (Value::Num(lhs), Value::Num(rhs)) => Value::Num(lhs + rhs),
                    //_ => panic!("unexpected values, not numerical"),
                };
                res.insert(ir.res_vreg.unwrap(), sum);
            }
            InstructionKind::Set => {
                let value = match ir.lhs.as_ref().unwrap() {
                    Operand::Num(num) => Value::Num(*num),
                    Operand::VirtualRegister(vreg) => res.get(&vreg).unwrap().clone(),
                };
                assert!(ir.rhs.is_none());

                res.insert(ir.res_vreg.unwrap(), value);
            }
        }
    }

    res
}
