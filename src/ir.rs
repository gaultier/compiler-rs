use std::{
    collections::BTreeMap,
    fmt::Display,
    io::{Write, stdout},
    panic,
};

use log::trace;
use serde::Serialize;

use crate::{
    ast::{Node, NodeKind},
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
    ICmp,
    Set, // Set virtual register.
    FnCall,
    JumpIfFalse,
}

#[derive(Serialize, Debug)]
pub struct Instruction {
    pub kind: InstructionKind,
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
    pub kind: OperandKind,
    pub typ: Type,
}

#[derive(Serialize, Debug, Clone, Copy, PartialEq, Eq)]
pub struct LiveRange {
    pub(crate) start: u32,
    pub(crate) end: u32, // Inclusive.
}

pub type LiveRanges = BTreeMap<VirtualRegister, LiveRange>;

#[derive(Debug)]
struct Label {
    name: String,
}

#[derive(Debug)]
pub struct Emitter {
    pub fn_defs: Vec<FnDef>,
    pub labels: Vec<Label>,
    label_current: usize,
}

#[derive(Debug, Serialize)]
pub struct FnDef {
    pub name: String,
    pub instructions: Vec<Instruction>,
    vreg: VirtualRegister,
    pub live_ranges: LiveRanges,
    vreg_to_type: BTreeMap<VirtualRegister, Type>,
    typ: Type,
    pub origin: Origin,
    pub stack_size: usize,
}

impl Display for FnDef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "func {}{}", self.name, self.typ)
    }
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

fn fn_name_ast_to_ir(ast_name: &str, typ_str: &str) -> String {
    match (ast_name, typ_str) {
        ("println", "(bool)") => "builtin.println_bool",
        ("println", "(int)") => "builtin.println_u64",
        _ => ast_name,
    }
    .to_owned()
}

impl FnDef {
    fn new(name: String, typ: &Type, origin: Origin, stack_size: usize) -> Self {
        Self {
            name,
            instructions: Vec::new(),
            vreg: VirtualRegister(0),
            live_ranges: LiveRanges::new(),
            vreg_to_type: BTreeMap::new(),
            typ: typ.clone(),
            origin,
            stack_size,
        }
    }

    fn make_vreg(&mut self, typ: &Type) -> VirtualRegister {
        self.vreg.0 += 1;

        self.vreg_to_type.insert(self.vreg, typ.clone());

        self.vreg
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
                InstructionKind::JumpIfFalse => {
                    todo!()
                }
                InstructionKind::IAdd
                | InstructionKind::IMultiply
                | InstructionKind::IDivide
                | InstructionKind::ICmp
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

impl Emitter {
    pub(crate) fn new() -> Self {
        Self {
            fn_defs: Vec::new(),
            labels: Vec::new(),
            label_current: 0,
        }
    }

    fn emit_node(&mut self, fn_def: &mut FnDef, node: &Node) {
        match &node.kind {
            crate::ast::NodeKind::Package(_) | crate::ast::NodeKind::FnDef(_) => {
                panic!(
                    "unexpected AST node inside function definition: {:#?}",
                    &node
                );
            }
            crate::ast::NodeKind::Number(num) => {
                assert_eq!(*node.typ.kind, TypeKind::Number);

                let res_vreg = fn_def.make_vreg(&node.typ);
                fn_def.instructions.push(Instruction {
                    kind: InstructionKind::Set,
                    operands: vec![Operand::new_int(*num as i64)],
                    origin: node.origin,
                    res_vreg: Some(res_vreg),
                    typ: node.typ.clone(),
                });
            }
            crate::ast::NodeKind::Bool(b) => {
                assert_eq!(*node.typ.kind, TypeKind::Bool);

                let res_vreg = fn_def.make_vreg(&node.typ);
                fn_def.instructions.push(Instruction {
                    kind: InstructionKind::Set,
                    operands: vec![Operand::new_bool(*b)],
                    origin: node.origin,
                    res_vreg: Some(res_vreg),
                    typ: node.typ.clone(),
                });
            }
            crate::ast::NodeKind::Identifier(_) => {
                todo!()
            }
            crate::ast::NodeKind::FnCall => {
                let (fn_name, args) = node.children.split_first().unwrap();
                // TODO: Support function pointers.
                let ast_fn_name = if let Node {
                    kind: NodeKind::Identifier(name),
                    ..
                } = fn_name
                {
                    name
                } else {
                    panic!("invalid fn call function name: {:#?}", node)
                };

                let arg_type = node
                    .children
                    .first()
                    .as_ref()
                    .map(|x| x.typ.to_string())
                    .unwrap_or_default();
                let real_fn_name = fn_name_ast_to_ir(ast_fn_name, &arg_type);
                let fn_name = Operand {
                    kind: OperandKind::Fn(real_fn_name.to_owned()),
                    typ: node.typ.clone(),
                };

                // Check type.
                let (res_vreg, ret_type) = match &*node.typ.kind {
                    TypeKind::Function(ret_type, _) if *ret_type.kind == TypeKind::Void => {
                        (None, ret_type.clone())
                    }
                    TypeKind::Function(ret_type, _) => {
                        (Some(fn_def.make_vreg(&node.typ)), ret_type.clone())
                    }
                    _ => panic!("not a function type: {:#?}", node.typ),
                };

                let mut operands = Vec::with_capacity(args.len() + 1);
                operands.push(fn_name);
                for arg in args {
                    self.emit_node(fn_def, arg);
                    let (vreg, typ) = fn_def
                        .instructions
                        .last()
                        .map(|x| (x.res_vreg.unwrap(), &x.typ))
                        .unwrap();
                    operands.push(Operand::new_vreg(vreg, typ));
                }

                trace!(
                    "ir: emit fn call: ast_name={} real_name={} arg_type={:?}",
                    ast_fn_name, real_fn_name, arg_type,
                );

                fn_def.instructions.push(Instruction {
                    kind: InstructionKind::FnCall,
                    operands,
                    origin: node.origin,
                    res_vreg,
                    typ: ret_type,
                });
            }
            crate::ast::NodeKind::Add => {
                assert_eq!(node.children.len(), 2);

                let ast_lhs = &node.children[0];
                let ast_rhs = &node.children[1];

                assert_eq!(*ast_lhs.typ.kind, TypeKind::Number);
                assert_eq!(*ast_lhs.typ.kind, TypeKind::Number);
                assert_eq!(*node.typ.kind, TypeKind::Number);

                self.emit_node(fn_def, ast_lhs);
                let (ir_lhs_vreg, ir_lhs_typ) = (
                    fn_def.instructions.last().unwrap().res_vreg.unwrap(),
                    fn_def.instructions.last().unwrap().typ.clone(),
                );

                self.emit_node(fn_def, ast_rhs);
                let (ir_rhs_vreg, ir_rhs_typ) = (
                    fn_def.instructions.last().unwrap().res_vreg.unwrap(),
                    fn_def.instructions.last().unwrap().typ.clone(),
                );

                let res_vreg = fn_def.make_vreg(&node.typ);

                fn_def.instructions.push(Instruction {
                    kind: InstructionKind::IAdd,
                    operands: vec![
                        Operand::new_vreg(ir_lhs_vreg, &ir_lhs_typ),
                        Operand::new_vreg(ir_rhs_vreg, &ir_rhs_typ),
                    ],
                    origin: node.origin,
                    res_vreg: Some(res_vreg),
                    typ: node.typ.clone(),
                });
            }
            crate::ast::NodeKind::Multiply => {
                todo!()
            }
            crate::ast::NodeKind::Divide => {
                todo!()
            }
            NodeKind::Block => {
                for node in &node.children {
                    self.emit_node(fn_def, &node);
                }
            }
            NodeKind::If(cond) => {
                assert_eq!(*cond.typ.kind, TypeKind::Bool);

                self.emit_node(fn_def, cond);

                if node.children.is_empty() {
                    return;
                }
                // TODO: Clear condition flags?

                let if_body = &node.children[0];
                assert_eq!(if_body.kind, NodeKind::Block);

                //let ins_jmp_to_else_body = Instruction {
                //    kind: InstructionKind::JumpIfFalse,
                //    origin: node.origin,
                //    operands: vec![/* TODO */],
                //    res_vreg: None,
                //    typ: Type::new_void(),
                //};
                todo!();
            }
        }
    }

    fn new_synth_label(&mut self, context: &str) -> Label {
        self.label_current += 1;
        Label {
            name: format!(".{}_{}", self.label_current, context),
        }
    }

    fn emit_def(&mut self, node: &Node) -> Option<FnDef> {
        match &node.kind {
            crate::ast::NodeKind::Package(_) => None,
            // Start of a new function.
            crate::ast::NodeKind::FnDef(fn_name) => {
                let stack_size = 0; // TODO
                let mut fn_def = FnDef::new(
                    fn_name_ast_to_ir(fn_name, &node.typ.to_string()),
                    &node.typ,
                    node.origin,
                    stack_size,
                );
                for node in &node.children {
                    self.emit_node(&mut fn_def, node);
                }

                fn_def.live_ranges = fn_def.compute_live_ranges();
                Some(fn_def)
            }
            _ => panic!("unexpected top-level AST node: {:#?}", node),
        }
    }

    pub fn emit(&mut self, nodes: &[Node]) {
        for node in nodes {
            if let Some(def) = self.emit_def(node) {
                self.fn_defs.push(def);
            }
        }
    }
}

impl Display for Operand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            OperandKind::Num(n) => {
                write!(f, "{}", n)
            }
            OperandKind::Bool(b) => {
                write!(f, "{}", b)
            }
            OperandKind::VirtualRegister(r) => write!(f, "v{}", r.0),
            OperandKind::Fn(name) => f.write_str(name),
        }?;
        f.write_str(" ")
    }
}

impl Operand {
    fn new_int(n: i64) -> Self {
        Self {
            kind: OperandKind::Num(n),
            typ: Type::new_int(),
        }
    }

    fn new_bool(b: bool) -> Self {
        Self {
            kind: OperandKind::Bool(b),
            typ: Type::new_bool(),
        }
    }

    fn new_vreg(vreg: VirtualRegister, typ: &Type) -> Self {
        Self {
            kind: OperandKind::VirtualRegister(vreg),
            typ: typ.clone(),
        }
    }
}

impl Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(vreg) = self.res_vreg {
            write!(f, "v{} {} := ", vreg.0, self.typ)?;
        }

        match self.kind {
            InstructionKind::IAdd => {
                write!(f, "iadd")?;
            }
            InstructionKind::IMultiply => {
                write!(f, "imul")?;
            }
            InstructionKind::IDivide => {
                write!(f, "idiv")?;
            }
            InstructionKind::ICmp => {
                write!(f, "icmp")?;
            }
            InstructionKind::Set => {
                write!(f, "set")?;
            }
            InstructionKind::FnCall => {
                write!(f, "call")?;
            }
            InstructionKind::JumpIfFalse => {
                write!(f, "jmp_if_false")?;
            }
        };
        write!(f, " ")?;

        for op in &self.operands {
            op.fmt(f)?;
            write!(f, " ")?;
        }

        writeln!(f)
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
        self.typ.size.unwrap()
    }

    pub(crate) fn new_int(n: i64) -> Self {
        Self {
            kind: EvalValueKind::Num(n),
            typ: Type::new_int(),
        }
    }

    pub(crate) fn new_bool(b: bool) -> Self {
        Self {
            kind: EvalValueKind::Bool(b),
            typ: Type::new_bool(),
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
            InstructionKind::JumpIfFalse => {
                todo!();
            }
            InstructionKind::FnCall => {
                let fn_name = match &ir.operands.first().unwrap().kind {
                    OperandKind::Fn(name) => name,
                    _ => panic!("invalid FnCall IR: {:#?}", ir.operands.first()),
                };
                match fn_name.as_str() {
                    "builtin.println_u64" => {
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
                assert_eq!(ir.operands.len(), 2);

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
                assert_eq!(ir.operands.len(), 2);

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
                assert_eq!(ir.operands.len(), 2);

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
            InstructionKind::ICmp => {
                assert_eq!(ir.operands.len(), 2);

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

                let cmp = lhs.as_num().cmp(&rhs.as_num());
                let cmp_num = match cmp {
                    std::cmp::Ordering::Less => -1,
                    std::cmp::Ordering::Equal => 0,
                    std::cmp::Ordering::Greater => 1,
                };

                let cmp_res = EvalValue {
                    kind: EvalValueKind::Num(cmp_num),
                    typ: lhs.typ.clone(),
                };
                res.insert(ir.res_vreg.unwrap(), cmp_res);
            }
            InstructionKind::Set => {
                let value = ir.operands.first().unwrap();
                let value = match &value.kind {
                    OperandKind::Num(num) => EvalValue::new_int(*num),
                    OperandKind::Bool(b) => EvalValue::new_bool(*b),
                    OperandKind::VirtualRegister(vreg) => res.get(vreg).unwrap().clone(),
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
