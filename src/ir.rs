use std::{
    collections::BTreeMap,
    fmt::Display,
    io::{Write, stdout},
    panic,
};

use serde::Serialize;

use crate::{
    ast::{Node, NodeData},
    origin::Origin,
    type_checker::{Size, Type, TypeKind},
};

#[derive(Serialize, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct VirtualRegister(pub u32);

#[derive(Serialize, Debug)]
pub enum InstructionKind {
    IAdd,
    IMultiply,
    IDivide,
    Set, // Set virtual register.
    FnCall,
}

#[derive(Serialize, Debug)]
pub struct Instruction {
    pub kind: InstructionKind,
    pub args_count: usize,
    pub operands: Vec<Operand>,
    pub origin: Origin,
    pub res_vreg: Option<VirtualRegister>,
    pub typ: Type,
}

#[derive(Serialize, Debug, Clone)]
pub enum OperandKind {
    Num(i64),
    Bool(bool),
    Fn(String),
    VirtualRegister(VirtualRegister),
}

#[derive(Serialize, Debug, Clone)]
pub struct Operand {
    kind: OperandKind,
    typ: Type,
}

#[derive(Serialize, Debug, Clone, Copy, PartialEq, Eq)]
pub struct LiveRange {
    pub(crate) start: u32,
    pub(crate) end: u32, // Inclusive.
}

pub type LiveRanges = BTreeMap<VirtualRegister, LiveRange>;

#[derive(Debug)]
pub struct Emitter {
    pub instructions: Vec<Instruction>,
    vreg: VirtualRegister,
    pub live_ranges: LiveRanges,
}

impl Display for VirtualRegister {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "v{}", self.0)
    }
}

impl Display for LiveRange {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}, {})", self.start, self.end)
    }
}

impl Default for Emitter {
    fn default() -> Self {
        Self::new()
    }
}

impl Emitter {
    pub(crate) fn new() -> Self {
        Self {
            instructions: Vec::new(),
            vreg: VirtualRegister(0),
            live_ranges: LiveRanges::new(),
        }
    }

    fn make_vreg(&mut self) -> VirtualRegister {
        self.vreg.0 += 1;
        self.vreg
    }

    pub fn emit(&mut self, nodes: &[Node]) {
        let mut stack = Vec::new();
        //        let mut name_resolutions = BTreeMap::<String, Operand>::new();

        for node in nodes {
            match node.kind {
                crate::ast::NodeKind::Number => {
                    let num = match node.data {
                        Some(NodeData::Num(n)) => n,
                        _ => panic!("expected number but was not present"),
                    };
                    assert_eq!(*node.typ.kind, TypeKind::Number);

                    let res_vreg = self.make_vreg();
                    let ins = Instruction {
                        kind: InstructionKind::Set,
                        args_count: 1,
                        operands: vec![Operand::new_int(num as i64)],
                        origin: node.origin,
                        res_vreg: Some(res_vreg),
                        typ: node.typ.clone(),
                    };
                    self.instructions.push(ins);
                    stack.push(res_vreg);
                }
                crate::ast::NodeKind::Bool => {
                    let b = match node.data {
                        Some(NodeData::Bool(b)) => b,
                        _ => panic!("expected boolean but was not present"),
                    };
                    assert_eq!(*node.typ.kind, TypeKind::Bool);

                    let res_vreg = self.make_vreg();
                    let ins = Instruction {
                        kind: InstructionKind::Set,
                        args_count: 1,
                        operands: vec![Operand::new_bool(b)],
                        origin: node.origin,
                        res_vreg: Some(res_vreg),
                        typ: node.typ.clone(),
                    };
                    self.instructions.push(ins);
                    stack.push(res_vreg);
                }
                crate::ast::NodeKind::BuiltinPrintln => {
                    // Only do checks.
                    match &*node.typ.kind {
                        TypeKind::Function(_, args) if args.len() == 1 => {}
                        _ => panic!("unexpected println type"),
                    };
                }
                crate::ast::NodeKind::FnCall => {
                    let args_count = match node.data.unwrap() {
                        crate::ast::NodeData::Num(n) => n as usize,
                        _ => panic!(
                            "invalid AST: node data for FnCall (i.e. the argument count) should be a number"
                        ),
                    };
                    let mut args = Vec::with_capacity(args_count);
                    for _ in 0..args_count {
                        args.push(stack.pop().unwrap());
                    }

                    // FIXME: Proper name resolution.
                    let fn_name = Operand {
                        kind: OperandKind::Fn(String::from("println_u64")),
                        typ: node.typ.clone(),
                    };

                    let (res_vreg, ret_type) = match &*node.typ.kind {
                        TypeKind::Function(ret_type, _) if *ret_type.kind == TypeKind::Void => {
                            (None, ret_type.clone())
                        }
                        TypeKind::Function(ret_type, _) => {
                            (Some(self.make_vreg()), ret_type.clone())
                        }
                        _ => panic!("not a function type"),
                    };

                    if let Some(res_vreg) = res_vreg {
                        stack.push(res_vreg);
                    }
                    let mut operands = Vec::with_capacity(args.len() + 1);
                    operands.push(fn_name);
                    operands.extend(args.iter().map(|x| Operand::new_vreg(*x, todo!())));

                    let ins = Instruction {
                        kind: InstructionKind::FnCall,
                        args_count,
                        operands,
                        origin: node.origin,
                        res_vreg,
                        typ: ret_type,
                    };
                    self.instructions.push(ins);
                }
                crate::ast::NodeKind::Add => {
                    // TODO: Checks.
                    let rhs = stack.pop().unwrap();
                    let lhs = stack.pop().unwrap();

                    assert_eq!(*node.typ.kind, TypeKind::Number);

                    let res_vreg = self.make_vreg();

                    let ins = Instruction {
                        kind: InstructionKind::IAdd,
                        args_count: 2,
                        operands: vec![
                            Operand::new_vreg(lhs, todo!()),
                            Operand::new_vreg(rhs, todo!()),
                        ],
                        origin: node.origin,
                        res_vreg: Some(res_vreg),
                        typ: node.typ.clone(),
                    };
                    self.instructions.push(ins);
                    stack.push(res_vreg);
                }
                crate::ast::NodeKind::Multiply => {
                    let rhs = stack.pop().unwrap();
                    let lhs = stack.pop().unwrap();

                    assert_eq!(*node.typ.kind, TypeKind::Number);

                    let res_vreg = self.make_vreg();

                    let ins = Instruction {
                        kind: InstructionKind::IMultiply,
                        args_count: 2,
                        operands: vec![
                            Operand::new_vreg(lhs, todo!()),
                            Operand::new_vreg(rhs, todo!()),
                        ],
                        origin: node.origin,
                        res_vreg: Some(res_vreg),
                        typ: node.typ.clone(),
                    };
                    self.instructions.push(ins);
                    stack.push(res_vreg);
                }
                crate::ast::NodeKind::Divide => {
                    let rhs = stack.pop().unwrap();
                    let lhs = stack.pop().unwrap();

                    assert_eq!(*node.typ.kind, TypeKind::Number);

                    let res_vreg = self.make_vreg();

                    let ins = Instruction {
                        kind: InstructionKind::IDivide,
                        args_count: 2,
                        operands: vec![
                            Operand::new_vreg(lhs, todo!()),
                            Operand::new_vreg(rhs, todo!()),
                        ],
                        origin: node.origin,
                        res_vreg: Some(res_vreg),
                        typ: node.typ.clone(),
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
                InstructionKind::FnCall => {
                    if let Some(res_vreg) = ins.res_vreg {
                        assert!(res_vreg.0 > 0);
                        let live_range = LiveRange {
                            start: i as u32,
                            end: i as u32,
                        };
                        res.insert(res_vreg, live_range);
                    }
                }
                InstructionKind::IAdd
                | InstructionKind::IMultiply
                | InstructionKind::IDivide
                | InstructionKind::Set => {
                    let res_vreg = ins.res_vreg.unwrap();
                    assert!(res_vreg.0 > 0);

                    let live_range = LiveRange {
                        start: i as u32,
                        end: i as u32,
                    };
                    res.insert(res_vreg, live_range);

                    if let Some(Operand {
                        kind: OperandKind::VirtualRegister(vreg),
                        ..
                    }) = &ins.operands.first()
                    {
                        Self::extend_live_range_on_use(*vreg, i as u32, &mut res);
                    }
                    if let Some(Operand {
                        kind: OperandKind::VirtualRegister(vreg),
                        ..
                    }) = &ins.operands.get(1)
                    {
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
        match self.kind {
            OperandKind::Num(n) => {
                write!(w, "{}", n)
            }
            OperandKind::Bool(b) => {
                write!(w, "{}", b)
            }
            OperandKind::VirtualRegister(r) => write!(w, "v{}", r.0),
            OperandKind::Fn(name) => w.write_all(name.as_bytes()),
        }?;
        w.write_all(b" ")?;
        Ok(())

        // self.typ.write(w)
    }
}

impl Operand {
    fn new_int(n: i64) -> Self {
        Self {
            kind: OperandKind::Num(n),
            typ: Type::make_int(),
        }
    }

    fn new_bool(b: bool) -> Self {
        Self {
            kind: OperandKind::Bool(b),
            typ: Type::make_bool(),
        }
    }

    fn new_vreg(vreg: VirtualRegister, typ: &Type) -> Self {
        Self {
            kind: OperandKind::VirtualRegister(vreg),
            typ: typ.clone(),
        }
    }
}

impl Instruction {
    pub fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        if let Some(vreg) = self.res_vreg {
            write!(w, "v{} {} := ", vreg.0, self.typ)?;
        }

        match self.kind {
            InstructionKind::IAdd => {
                write!(w, "iadd")?;
            }
            InstructionKind::IMultiply => {
                write!(w, "imul")?;
            }
            InstructionKind::IDivide => {
                write!(w, "idiv")?;
            }
            InstructionKind::Set => {
                write!(w, "set")?;
            }
            InstructionKind::FnCall => {
                write!(w, "call")?;
            }
        };
        write!(w, " ")?;

        for op in &self.operands {
            op.write(w)?;
            write!(w, " ")?;
        }

        writeln!(w)
    }
}

#[derive(Serialize, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum EvalValueKind {
    Num(i64),
    Bool(bool),
    Fn(String),
}

#[derive(Serialize, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct EvalValue {
    pub kind: EvalValueKind,
    pub typ: Type,
}

pub type EvalResult = BTreeMap<VirtualRegister, EvalValue>;

impl EvalValue {
    pub(crate) fn as_num(&self) -> i64 {
        match self.kind {
            EvalValueKind::Num(num) => num,
            _ => panic!("not a number"),
        }
    }

    pub(crate) fn size(&self) -> Size {
        self.typ.size
    }

    pub(crate) fn new_int(n: i64) -> Self {
        Self {
            kind: EvalValueKind::Num(n),
            typ: Type::make_int(),
        }
    }

    pub(crate) fn new_bool(n: bool) -> Self {
        Self {
            kind: EvalValueKind::Bool(b),
            typ: Type::make_bool(),
        }
    }

    pub fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        match &self.kind {
            EvalValueKind::Num(n) => write!(w, "{}", n),
            EvalValueKind::Bool(b) => write!(w, "{}", b),
            EvalValueKind::Fn(name) => w.write_all(name.as_bytes()),
        }
    }
}

pub fn eval(irs: &[Instruction]) -> EvalResult {
    let mut res = EvalResult::new();

    for ir in irs {
        match ir.kind {
            InstructionKind::FnCall => {
                let fn_name = match &ir.operands.first().unwrap().kind {
                    OperandKind::Fn(name) => name,
                    _ => panic!("invalid FnCall IR: {:#?}", ir.operands.first()),
                };
                match fn_name.as_str() {
                    "println_u64" => {
                        for op in &ir.operands[1..] {
                            let val = match op.kind {
                                OperandKind::VirtualRegister(vreg) => res.get(&vreg).unwrap(),
                                _ => panic!("unexpected fn call operand: {:#?}", op),
                            };
                            val.write(&mut stdout()).unwrap();
                            writeln!(&mut stdout()).unwrap();
                        }
                    }
                    _ => unimplemented!(),
                }
            }
            InstructionKind::IAdd => {
                let lhs = ir.operands.first().unwrap();
                let lhs = match lhs.kind {
                    OperandKind::Num(num) => EvalValue::new_int(num),
                    OperandKind::VirtualRegister(vreg) => res.get(&vreg).unwrap().clone(),
                    _ => panic!("incompatible operands"),
                };

                let rhs = ir.operands.get(1).unwrap();
                let rhs = match rhs.kind {
                    OperandKind::Num(num) => EvalValue::new_int(num),
                    OperandKind::VirtualRegister(vreg) => res.get(&vreg).unwrap().clone(),
                    _ => panic!("incompatible operands"),
                };
                assert_eq!(lhs.size(), rhs.size());

                let sum = EvalValue {
                    kind: EvalValueKind::Num(lhs.as_num() + rhs.as_num()),
                    typ: lhs.typ.clone(),
                };
                res.insert(ir.res_vreg.unwrap(), sum);
            }
            InstructionKind::IMultiply => {
                let lhs = ir.operands.first().unwrap();
                let lhs = match lhs.kind {
                    OperandKind::Num(num) => EvalValue::new_int(num),
                    OperandKind::VirtualRegister(vreg) => res.get(&vreg).unwrap().clone(),
                    _ => panic!("incompatible operands"),
                };

                let rhs = ir.operands.get(1).unwrap();
                let rhs = match rhs.kind {
                    OperandKind::Num(num) => EvalValue::new_int(num),
                    OperandKind::VirtualRegister(vreg) => res.get(&vreg).unwrap().clone(),
                    _ => panic!("incompatible operands"),
                };
                assert_eq!(lhs.size(), rhs.size());

                let mul = EvalValue {
                    kind: EvalValueKind::Num(lhs.as_num() * rhs.as_num()),
                    typ: lhs.typ.clone(),
                };
                res.insert(ir.res_vreg.unwrap(), mul);
            }
            InstructionKind::IDivide => {
                let lhs = ir.operands.first().unwrap();
                let lhs = match lhs.kind {
                    OperandKind::Num(num) => EvalValue::new_int(num),
                    OperandKind::VirtualRegister(vreg) => res.get(&vreg).unwrap().clone(),
                    _ => panic!("incompatible operands"),
                };

                let rhs = ir.operands.get(1).unwrap();
                let rhs = match rhs.kind {
                    OperandKind::Num(num) => EvalValue::new_int(num),
                    OperandKind::VirtualRegister(vreg) => res.get(&vreg).unwrap().clone(),
                    _ => panic!("incompatible operands"),
                };
                assert_eq!(lhs.size(), rhs.size());

                let div = EvalValue {
                    kind: EvalValueKind::Num(lhs.as_num() / rhs.as_num()),
                    typ: lhs.typ.clone(),
                };
                res.insert(ir.res_vreg.unwrap(), div);
            }
            InstructionKind::Set => {
                let value = ir.operands.first().unwrap();
                let value = match &value.kind {
                    OperandKind::Num(num) => EvalValue {
                        kind: EvalValueKind::Num(*num),
                        typ: value.typ.clone(),
                    },
                    OperandKind::Bool(b) => EvalValue {
                        kind: EvalValueKind::Bool(*b),
                        typ: value.typ.clone(),
                    },
                    OperandKind::VirtualRegister(vreg) => res.get(&vreg).unwrap().clone(),
                    OperandKind::Fn(name) => EvalValue {
                        kind: EvalValueKind::Fn(name.to_owned()),
                        typ: value.typ.clone(),
                    },
                };
                assert!(ir.operands.get(1).is_none());

                res.insert(ir.res_vreg.unwrap(), value);
            }
        }
    }

    res
}
