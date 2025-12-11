use std::{collections::BTreeMap, io::Write};

use serde::Serialize;

use crate::{
    ast::{Node, NodeData},
    origin::Origin,
};

#[derive(Serialize, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct VirtualRegister(pub u32);

//pub enum VirtualRegisterConstraint {
//    Result,
//}

#[derive(Serialize, Debug)]
pub enum InstructionKind {
    Add,
    Multiply,
    Set, // Set virtual register.
}

#[derive(Serialize, Debug)]
pub struct Instruction {
    pub kind: InstructionKind,
    pub args_count: u8,
    pub lhs: Option<Operand>,
    pub rhs: Option<Operand>,
    pub origin: Origin,
    pub res_vreg: Option<VirtualRegister>,
    // TODO: type, live_range.
}

#[derive(Serialize, Debug, Clone, Copy)]
pub enum Operand {
    Num(u64),
    VirtualRegister(VirtualRegister),
}

#[derive(Serialize, Debug, Clone, Copy, PartialEq, Eq)]
pub struct LiveRange {
    pub(crate) start: u32,
    pub(crate) end: u32, // Inclusive.
}

pub type LiveRanges = BTreeMap<VirtualRegister, LiveRange>;
//pub type Constraints = BTreeMap<VirtualRegister, VirtualRegisterConstraint>;

pub struct Emitter {
    pub instructions: Vec<Instruction>,
    vreg: VirtualRegister,
    pub live_ranges: LiveRanges,
    //pub constraints: Constraints,
}

impl Default for Emitter {
    fn default() -> Self {
        Self::new()
    }
}

impl Emitter {
    pub fn new() -> Self {
        Self {
            instructions: Vec::new(),
            vreg: VirtualRegister(0),
            live_ranges: LiveRanges::new(),
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
                crate::ast::NodeKind::Multiply => {
                    // TODO: Checks.
                    let rhs = stack.pop().unwrap();
                    let lhs = stack.pop().unwrap();

                    let res_vreg = self.make_vreg();

                    let ins = Instruction {
                        kind: InstructionKind::Multiply,
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

        self.live_ranges = self.compute_live_ranges();
    }

    fn extend_live_range_on_use(
        vreg: VirtualRegister,
        ins_position: u32,
        live_ranges: &mut LiveRanges,
    ) {
        live_ranges.entry(vreg).and_modify(|e| e.end = ins_position);
    }

    fn compute_live_ranges(&self) -> LiveRanges {
        let mut res = LiveRanges::new();

        for (i, ins) in self.instructions.iter().enumerate() {
            match ins.kind {
                InstructionKind::Add | InstructionKind::Multiply | InstructionKind::Set => {
                    let res_vreg = ins.res_vreg.unwrap();
                    assert!(res_vreg.0 > 0);

                    let live_range = LiveRange {
                        start: i as u32,
                        end: i as u32,
                    };
                    res.insert(res_vreg, live_range);

                    if let Some(Operand::VirtualRegister(vreg)) = &ins.lhs {
                        Self::extend_live_range_on_use(*vreg, i as u32, &mut res);
                    }
                    if let Some(Operand::VirtualRegister(vreg)) = &ins.rhs {
                        Self::extend_live_range_on_use(*vreg, i as u32, &mut res);
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
            Operand::VirtualRegister(r) => write!(w, "(v{})", r.0),
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
                write!(w, "add")?;
            }
            InstructionKind::Multiply => {
                write!(w, "mul")?;
            }
            InstructionKind::Set => {
                write!(w, "set")?;
            }
        };
        write!(w, " ")?;

        if let Some(lhs) = &self.lhs {
            lhs.write(w)?;
        }
        write!(w, " ")?;

        if let Some(rhs) = &self.rhs {
            rhs.write(w)?;
        }

        writeln!(w)
    }
}

#[derive(Serialize, Copy, Clone, Debug)]
pub enum Value {
    Num(u64),
}

pub type EvalResult = BTreeMap<VirtualRegister, Value>;

impl Value {
    pub(crate) fn as_num(&self) -> u64 {
        match self {
            Value::Num(num) => *num,
        }
    }
}

pub fn eval(irs: &[Instruction]) -> EvalResult {
    let mut res = EvalResult::new();

    for ir in irs {
        match ir.kind {
            InstructionKind::Add => {
                let lhs = match ir.lhs.as_ref().unwrap() {
                    Operand::Num(num) => Value::Num(*num),
                    Operand::VirtualRegister(vreg) => *res.get(vreg).unwrap(),
                };
                let rhs = match ir.rhs.as_ref().unwrap() {
                    Operand::Num(num) => Value::Num(*num),
                    Operand::VirtualRegister(vreg) => *res.get(vreg).unwrap(),
                };
                let sum = Value::Num(lhs.as_num() + rhs.as_num());
                res.insert(ir.res_vreg.unwrap(), sum);
            }
            InstructionKind::Multiply => {
                let lhs = match ir.lhs.as_ref().unwrap() {
                    Operand::Num(num) => Value::Num(*num),
                    Operand::VirtualRegister(vreg) => *res.get(vreg).unwrap(),
                };
                let rhs = match ir.rhs.as_ref().unwrap() {
                    Operand::Num(num) => Value::Num(*num),
                    Operand::VirtualRegister(vreg) => *res.get(vreg).unwrap(),
                };
                let mul = match (lhs, rhs) {
                    (Value::Num(lhs), Value::Num(rhs)) => Value::Num(lhs * rhs),
                    //_ => panic!("unexpected values, not numerical"),
                };
                res.insert(ir.res_vreg.unwrap(), mul);
            }
            InstructionKind::Set => {
                let value = match ir.lhs.as_ref().unwrap() {
                    Operand::Num(num) => Value::Num(*num),
                    Operand::VirtualRegister(vreg) => *res.get(vreg).unwrap(),
                };
                assert!(ir.rhs.is_none());

                res.insert(ir.res_vreg.unwrap(), value);
            }
        }
    }

    res
}
