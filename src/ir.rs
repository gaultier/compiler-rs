use std::{collections::BTreeMap, fmt::Display, io::Write, panic};

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
    IAdd(Operand, Operand),
    IMultiply(Operand, Operand),
    IDivide(Operand, Operand),
    ICmp(Operand, Operand),
    Set(Operand), // Set virtual register.
    FnCall(String, Vec<Operand>),
    JumpIfFalse(String, Operand),
    Jump(String),
    LabelDef(String),
    VarDecl(String, Operand),
}

#[derive(Serialize, Debug)]
pub struct Instruction {
    pub kind: InstructionKind,
    pub origin: Origin,
    pub res_vreg: Option<VirtualRegister>,
    pub typ: Type,
}

#[derive(Serialize, Debug, Clone)]
pub enum OperandKind {
    Num(i64),
    Bool(bool),
    Fn(String),
    Label(String),
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
pub struct Emitter {
    pub fn_defs: Vec<FnDef>,
    pub labels: Vec<String>,
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
    name_to_vreg: BTreeMap<String, VirtualRegister>,
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

fn fn_name_ast_to_ir(ast_name: &str, typ_str: &str, arg0_typ: &str) -> String {
    match (ast_name, typ_str, arg0_typ) {
        ("println", "(any)", "bool") => "builtin.println_bool",
        ("println", "(any)", "int") => "builtin.println_int",
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
            name_to_vreg: BTreeMap::new(),
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
            let i = i as u32;
            match &ins.kind {
                InstructionKind::VarDecl(_, op) => {
                    assert!(ins.res_vreg.is_none());

                    if let Operand {
                        kind: OperandKind::VirtualRegister(vreg),
                        ..
                    } = op
                    {
                        Self::extend_live_range_on_use(*vreg, i, &mut res);
                    } else {
                        panic!("expected vreg operand");
                    }
                }
                InstructionKind::FnCall(_, operands) => {
                    if let Some(res_vreg) = ins.res_vreg {
                        assert!(res_vreg.0 > 0);
                        let live_range = LiveRange { start: i, end: i };
                        res.insert(res_vreg, live_range);
                    }
                    for op in operands {
                        if let Operand {
                            kind: OperandKind::VirtualRegister(vreg),
                            ..
                        } = op
                        {
                            Self::extend_live_range_on_use(*vreg, i, &mut res);
                        }
                    }
                }

                // Nothing to do for these instructions as they don't operate on virtual registers.
                InstructionKind::LabelDef(_)
                | InstructionKind::Jump(_)
                | InstructionKind::JumpIfFalse(_, _) => {}

                InstructionKind::IAdd(lhs, rhs)
                | InstructionKind::IMultiply(lhs, rhs)
                | InstructionKind::IDivide(lhs, rhs)
                | InstructionKind::ICmp(lhs, rhs) => {
                    let res_vreg = ins.res_vreg.unwrap();
                    assert!(res_vreg.0 > 0);

                    let live_range = LiveRange { start: i, end: i };
                    res.insert(res_vreg, live_range);

                    if let Operand {
                        kind: OperandKind::VirtualRegister(vreg),
                        ..
                    } = lhs
                    {
                        Self::extend_live_range_on_use(*vreg, i, &mut res);
                    }
                    if let Operand {
                        kind: OperandKind::VirtualRegister(vreg),
                        ..
                    } = rhs
                    {
                        Self::extend_live_range_on_use(*vreg, i, &mut res);
                    }
                }
                InstructionKind::Set(op) => {
                    let res_vreg = ins.res_vreg.unwrap();
                    assert!(res_vreg.0 > 0);

                    let live_range = LiveRange { start: i, end: i };
                    res.insert(res_vreg, live_range);

                    if let Operand {
                        kind: OperandKind::VirtualRegister(vreg),
                        ..
                    } = op
                    {
                        Self::extend_live_range_on_use(*vreg, i, &mut res);
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
            crate::ast::NodeKind::Package(_) | crate::ast::NodeKind::FnDef { .. } => {
                panic!(
                    "unexpected AST node inside function definition: {:#?}",
                    &node
                );
            }
            NodeKind::For { cond, block } => {
                assert_eq!(*node.typ.kind, TypeKind::Void);

                let loop_label = format!(".{}_for_loop", self.label_current);
                let end_label = format!(".{}_for_end", self.label_current);
                self.label_current += 1;

                fn_def.instructions.push(Instruction {
                    kind: InstructionKind::LabelDef(loop_label.clone()),
                    origin: node.origin,
                    res_vreg: None,
                    typ: Type::new_void(),
                });

                if let Some(cond) = cond {
                    self.emit_node(fn_def, cond);
                    let vreg = fn_def.instructions.last().unwrap().res_vreg.unwrap();

                    let op = Operand {
                        kind: OperandKind::VirtualRegister(vreg),
                        typ: fn_def.instructions.last().unwrap().typ.clone(),
                    };
                    fn_def.instructions.push(Instruction {
                        kind: InstructionKind::JumpIfFalse(end_label.clone(), op),
                        origin: node.origin,
                        res_vreg: None,
                        typ: Type::new_void(),
                    });
                }
                for stmt in block {
                    self.emit_node(fn_def, stmt);
                }
                fn_def.instructions.push(Instruction {
                    kind: InstructionKind::Jump(loop_label.clone()),
                    origin: node.origin,
                    res_vreg: None,
                    typ: Type::new_void(),
                });

                fn_def.instructions.push(Instruction {
                    kind: InstructionKind::LabelDef(end_label),
                    origin: node.origin,
                    res_vreg: None,
                    typ: Type::new_void(),
                });
            }
            crate::ast::NodeKind::Number(num) => {
                assert_eq!(*node.typ.kind, TypeKind::Number);

                let res_vreg = fn_def.make_vreg(&node.typ);
                fn_def.instructions.push(Instruction {
                    kind: InstructionKind::Set(Operand::new_int(*num as i64)),
                    origin: node.origin,
                    res_vreg: Some(res_vreg),
                    typ: node.typ.clone(),
                });
            }
            crate::ast::NodeKind::Bool(b) => {
                assert_eq!(*node.typ.kind, TypeKind::Bool);

                let res_vreg = fn_def.make_vreg(&node.typ);
                fn_def.instructions.push(Instruction {
                    kind: InstructionKind::Set(Operand::new_bool(*b)),
                    origin: node.origin,
                    res_vreg: Some(res_vreg),
                    typ: node.typ.clone(),
                });
            }
            crate::ast::NodeKind::Identifier(identifier) => {
                let vreg = *fn_def.name_to_vreg.get(identifier).unwrap();
                let res_vreg = fn_def.make_vreg(&node.typ);
                fn_def.instructions.push(Instruction {
                    kind: InstructionKind::Set(Operand::new_vreg(vreg, &node.typ)),
                    origin: node.origin,
                    res_vreg: Some(res_vreg),
                    typ: node.typ.clone(),
                });
            }
            crate::ast::NodeKind::FnCall { callee, args } => {
                // TODO: Support function pointers.
                let ast_fn_name = if let Node {
                    kind: NodeKind::Identifier(name),
                    ..
                } = &**callee
                {
                    name
                } else {
                    panic!("invalid fn call function name: {:#?}", node)
                };

                let arg_type = callee.typ.to_string();
                let arg0_typ = args.first().map(|x| x.typ.to_string()).unwrap_or_default();
                let real_fn_name = fn_name_ast_to_ir(ast_fn_name, &arg_type, &arg0_typ);

                // Check type.
                let (res_vreg, ret_type) = match &*callee.typ.kind {
                    TypeKind::Function(ret_type, _) if *ret_type.kind == TypeKind::Void => {
                        (None, ret_type.clone())
                    }
                    TypeKind::Function(ret_type, _) => {
                        (Some(fn_def.make_vreg(&node.typ)), ret_type.clone())
                    }
                    _ => panic!("not a function type: {:#?}", node.typ),
                };

                let mut operands = Vec::with_capacity(args.len());
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
                    kind: InstructionKind::FnCall(real_fn_name, operands),
                    origin: node.origin,
                    res_vreg,
                    typ: ret_type,
                });
            }
            crate::ast::NodeKind::Cmp(lhs, rhs) => {
                // Set by the parser.
                assert_eq!(*node.typ.kind, TypeKind::Bool);
                assert_ne!(*lhs.typ.kind, TypeKind::Unknown);
                assert_ne!(*rhs.typ.kind, TypeKind::Unknown);

                self.emit_node(fn_def, lhs);
                let lhs_vreg = fn_def.instructions.last().unwrap().res_vreg.unwrap();
                self.emit_node(fn_def, rhs);
                let rhs_vreg = fn_def.instructions.last().unwrap().res_vreg.unwrap();

                let res_vreg = fn_def.make_vreg(&node.typ);

                fn_def.instructions.push(Instruction {
                    kind: InstructionKind::ICmp(
                        Operand {
                            kind: OperandKind::VirtualRegister(lhs_vreg),
                            typ: lhs.typ.clone(),
                        },
                        Operand {
                            kind: OperandKind::VirtualRegister(rhs_vreg),
                            typ: rhs.typ.clone(),
                        },
                    ),
                    origin: node.origin,
                    res_vreg: Some(res_vreg),
                    typ: node.typ.clone(),
                });
            }
            crate::ast::NodeKind::Add(ast_lhs, ast_rhs) => {
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
                    kind: InstructionKind::IAdd(
                        Operand::new_vreg(ir_lhs_vreg, &ir_lhs_typ),
                        Operand::new_vreg(ir_rhs_vreg, &ir_rhs_typ),
                    ),
                    origin: node.origin,
                    res_vreg: Some(res_vreg),
                    typ: node.typ.clone(),
                });
            }
            crate::ast::NodeKind::Multiply(ast_lhs, ast_rhs) => {
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
                    kind: InstructionKind::IMultiply(
                        Operand::new_vreg(ir_lhs_vreg, &ir_lhs_typ),
                        Operand::new_vreg(ir_rhs_vreg, &ir_rhs_typ),
                    ),
                    origin: node.origin,
                    res_vreg: Some(res_vreg),
                    typ: node.typ.clone(),
                });
            }
            crate::ast::NodeKind::Divide(ast_lhs, ast_rhs) => {
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
                    kind: InstructionKind::IDivide(
                        Operand::new_vreg(ir_lhs_vreg, &ir_lhs_typ),
                        Operand::new_vreg(ir_rhs_vreg, &ir_rhs_typ),
                    ),
                    origin: node.origin,
                    res_vreg: Some(res_vreg),
                    typ: node.typ.clone(),
                });
            }
            NodeKind::Block(stmts) => {
                for node in stmts {
                    self.emit_node(fn_def, node);
                }
            }
            NodeKind::If {
                cond,
                then_block,
                else_block,
            } => {
                assert_eq!(*cond.typ.kind, TypeKind::Bool);

                self.emit_node(fn_def, cond);

                if then_block.is_none() {
                    return;
                }
                let then_body = then_block.as_ref().unwrap();

                assert!(matches!(then_body.kind, NodeKind::Block(_)));

                let else_label = if else_block.is_some() {
                    Some(format!(".{}_if_else", self.label_current))
                } else {
                    None
                };
                let end_label = format!(".{}_if_end", self.label_current);
                self.label_current += 1;

                let vreg: VirtualRegister = fn_def.instructions.last().unwrap().res_vreg.unwrap();
                let typ = fn_def.instructions.last().unwrap().typ.clone();
                assert_eq!(*typ.kind, TypeKind::Bool);

                let op = Operand {
                    kind: OperandKind::VirtualRegister(vreg),
                    typ,
                };
                fn_def.instructions.push(Instruction {
                    kind: InstructionKind::JumpIfFalse(
                        else_label.clone().unwrap_or_else(|| end_label.clone()),
                        op,
                    ),
                    origin: node.origin,
                    res_vreg: None,
                    typ: Type::new_void(),
                });

                // Then-body.
                if let NodeKind::Block(stmts) = &then_body.kind {
                    for node in stmts {
                        self.emit_node(fn_def, node);
                    }
                }

                // Else body.
                if let Some(else_body) = else_block {
                    assert!(matches!(else_body.kind, NodeKind::Block(_)));

                    fn_def.instructions.push(Instruction {
                        kind: InstructionKind::Jump(end_label.clone()),
                        origin: node.origin,
                        res_vreg: None,
                        typ: Type::new_void(),
                    });

                    fn_def.instructions.push(Instruction {
                        kind: InstructionKind::LabelDef(else_label.clone().unwrap()),
                        origin: node.origin,
                        res_vreg: None,
                        typ: Type::new_void(),
                    });

                    if let NodeKind::Block(stmts) = &else_body.kind {
                        for node in stmts {
                            self.emit_node(fn_def, node);
                        }
                    }
                }

                // End.
                {
                    fn_def.instructions.push(Instruction {
                        kind: InstructionKind::LabelDef(end_label),
                        origin: node.origin,
                        res_vreg: None,
                        typ: Type::new_void(),
                    });
                }
            }
            NodeKind::VarDecl(identifier, expr) => {
                self.emit_node(fn_def, expr);
                let op_vreg = fn_def.instructions.last().unwrap().res_vreg.unwrap();
                let op_typ = fn_def.instructions.last().unwrap().typ.clone();

                assert!(fn_def.name_to_vreg.get(identifier).is_none());
                fn_def.name_to_vreg.insert(identifier.to_owned(), op_vreg);

                fn_def.instructions.push(Instruction {
                    kind: InstructionKind::VarDecl(
                        identifier.clone(),
                        Operand {
                            kind: OperandKind::VirtualRegister(op_vreg),
                            typ: op_typ,
                        },
                    ),
                    origin: node.origin,
                    res_vreg: None,
                    typ: node.typ.clone(),
                });
            }
        }
    }

    fn emit_def(&mut self, node: &Node) -> Option<FnDef> {
        match &node.kind {
            crate::ast::NodeKind::Package(_) => None,
            // Start of a new function.
            crate::ast::NodeKind::FnDef { name, body } => {
                let stack_size = 0; // TODO
                let mut fn_def = FnDef::new(name.to_owned(), &node.typ, node.origin, stack_size);
                for node in body {
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
            OperandKind::Label(l) => f.write_str(l),
            OperandKind::VirtualRegister(r) => write!(f, "v{}", r.0),
            OperandKind::Fn(name) => f.write_str(name),
        }
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

    pub(crate) fn as_vreg(&self) -> Option<VirtualRegister> {
        match self.kind {
            OperandKind::VirtualRegister(vreg) => Some(vreg),
            _ => None,
        }
    }
}

impl Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(vreg) = self.res_vreg {
            write!(f, "v{} {} := ", vreg.0, self.typ)?;
        }

        match &self.kind {
            InstructionKind::IAdd(lhs, rhs) => {
                write!(f, "iadd {} {}", lhs, rhs)?;
            }
            InstructionKind::IMultiply(lhs, rhs) => {
                write!(f, "imul {} {}", lhs, rhs)?;
            }
            InstructionKind::IDivide(lhs, rhs) => {
                write!(f, "idiv {} {}", lhs, rhs)?;
            }
            InstructionKind::ICmp(lhs, rhs) => {
                write!(f, "icmp {} {}", lhs, rhs)?;
            }
            InstructionKind::Set(op) => {
                write!(f, "set {}", op)?;
            }
            InstructionKind::FnCall(name, ops) => {
                write!(f, "call {}", name)?;
                for op in ops {
                    write!(f, " {}", op)?;
                }
            }
            InstructionKind::JumpIfFalse(label, op) => {
                write!(f, "jmp_if_false {} {}", label, op)?;
            }
            InstructionKind::Jump(op) => {
                write!(f, "jmp {}", op)?;
            }
            InstructionKind::LabelDef(op) => {
                write!(f, "label {}", op)?;
            }
            InstructionKind::VarDecl(identifier, op) => {
                write!(f, "var_decl {} {}", identifier, op)?;
            }
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

#[derive(Debug, Default)]
pub struct Eval {
    pub(crate) vregs: BTreeMap<VirtualRegister, EvalValue>,
    pub(crate) stdout: Vec<u8>,
}

impl Eval {
    fn new() -> Self {
        Self {
            vregs: BTreeMap::new(),
            stdout: Vec::new(),
        }
    }
}

impl EvalValue {
    pub(crate) fn as_num(&self) -> i64 {
        match self.kind {
            EvalValueKind::Num(num) => num,
            _ => panic!("not a number"),
        }
    }

    pub(crate) fn as_bool(&self) -> bool {
        match self.kind {
            EvalValueKind::Bool(b) => b,
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

pub fn eval(irs: &[Instruction]) -> Eval {
    let mut eval = Eval::new();

    let jump_locations: BTreeMap<String, usize> = irs
        .iter()
        .enumerate()
        .filter_map(|(i, ins)| match &ins.kind {
            InstructionKind::LabelDef(label) => Some((label.clone(), i)),
            _ => None,
        })
        .collect();
    let mut name_to_vreg: BTreeMap<String, VirtualRegister> = BTreeMap::new();

    let mut pc: usize = 0;
    loop {
        if pc >= irs.len() {
            break;
        }

        let ir = &irs[pc];

        match &ir.kind {
            InstructionKind::VarDecl(identifier, op) => {
                assert!(ir.res_vreg.is_none());
                assert!(name_to_vreg.get(identifier).is_none());
                let vreg = op.as_vreg().unwrap();

                name_to_vreg.insert(identifier.to_owned(), vreg);
            }
            InstructionKind::JumpIfFalse(label, cond) => {
                let vreg = cond.as_vreg().unwrap();
                let val = eval.vregs.get(&vreg).unwrap();
                if let EvalValue {
                    kind:
                        EvalValueKind::Bool(false) | EvalValueKind::Num(-1) | EvalValueKind::Num(1),
                    ..
                } = val
                {
                    pc = *jump_locations.get(label).unwrap();
                    continue;
                }
            }
            InstructionKind::Jump(label) => {
                pc = *jump_locations.get(label).unwrap();
                continue;
            }
            InstructionKind::LabelDef(_) => {}
            InstructionKind::FnCall(fn_name, operands) => match fn_name.as_str() {
                "builtin.println_int" => {
                    for op in operands {
                        let val = match op.kind {
                            OperandKind::VirtualRegister(vreg) => eval.vregs.get(&vreg).unwrap(),
                            _ => panic!("unexpected fn call operand: {:#?}", op),
                        };
                        writeln!(&mut eval.stdout, "{}", val.as_num()).unwrap();
                    }
                }
                "builtin.println_bool" => {
                    for op in operands {
                        let val = match op.kind {
                            OperandKind::VirtualRegister(vreg) => eval.vregs.get(&vreg).unwrap(),
                            _ => panic!("unexpected fn call operand: {:#?}", op),
                        };
                        writeln!(&mut eval.stdout, "{}", val.as_bool()).unwrap();
                    }
                }
                _ => unimplemented!("{}", fn_name),
            },
            InstructionKind::IAdd(lhs, rhs) => {
                let lhs = match &lhs.kind {
                    OperandKind::Num(num) => EvalValue::new_int(*num),
                    OperandKind::VirtualRegister(vreg) => eval.vregs.get(vreg).unwrap().clone(),
                    _ => panic!("incompatible operands"),
                };

                let rhs = match &rhs.kind {
                    OperandKind::Num(num) => EvalValue::new_int(*num),
                    OperandKind::VirtualRegister(vreg) => eval.vregs.get(vreg).unwrap().clone(),
                    _ => panic!("incompatible operands"),
                };
                assert_eq!(lhs.size(), rhs.size());

                let sum = EvalValue {
                    kind: EvalValueKind::Num(lhs.as_num() + rhs.as_num()),
                    typ: lhs.typ.clone(),
                };
                eval.vregs.insert(ir.res_vreg.unwrap(), sum);
            }
            InstructionKind::IMultiply(lhs, rhs) => {
                let lhs = match &lhs.kind {
                    OperandKind::Num(num) => EvalValue::new_int(*num),
                    OperandKind::VirtualRegister(vreg) => eval.vregs.get(vreg).unwrap().clone(),
                    _ => panic!("incompatible operands"),
                };

                let rhs = match &rhs.kind {
                    OperandKind::Num(num) => EvalValue::new_int(*num),
                    OperandKind::VirtualRegister(vreg) => eval.vregs.get(vreg).unwrap().clone(),
                    _ => panic!("incompatible operands"),
                };
                assert_eq!(lhs.size(), rhs.size());

                let mul = EvalValue {
                    kind: EvalValueKind::Num(lhs.as_num() * rhs.as_num()),
                    typ: lhs.typ.clone(),
                };
                eval.vregs.insert(ir.res_vreg.unwrap(), mul);
            }
            InstructionKind::IDivide(lhs, rhs) => {
                let lhs = match &lhs.kind {
                    OperandKind::Num(num) => EvalValue::new_int(*num),
                    OperandKind::VirtualRegister(vreg) => eval.vregs.get(vreg).unwrap().clone(),
                    _ => panic!("incompatible operands"),
                };

                let rhs = match &rhs.kind {
                    OperandKind::Num(num) => EvalValue::new_int(*num),
                    OperandKind::VirtualRegister(vreg) => eval.vregs.get(vreg).unwrap().clone(),
                    _ => panic!("incompatible operands"),
                };
                assert_eq!(lhs.size(), rhs.size());

                let div = EvalValue {
                    kind: EvalValueKind::Num(lhs.as_num() / rhs.as_num()),
                    typ: lhs.typ.clone(),
                };
                eval.vregs.insert(ir.res_vreg.unwrap(), div);
            }
            InstructionKind::ICmp(lhs, rhs) => {
                let lhs = match &lhs.kind {
                    OperandKind::Num(num) => EvalValue::new_int(*num),
                    OperandKind::VirtualRegister(vreg) => eval.vregs.get(vreg).unwrap().clone(),
                    _ => panic!("incompatible operands"),
                };

                let rhs = match &rhs.kind {
                    OperandKind::Num(num) => EvalValue::new_int(*num),
                    OperandKind::VirtualRegister(vreg) => eval.vregs.get(vreg).unwrap().clone(),
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
                eval.vregs.insert(ir.res_vreg.unwrap(), cmp_res);
            }
            InstructionKind::Set(value) => {
                let value = match &value.kind {
                    OperandKind::Num(num) => EvalValue::new_int(*num),
                    OperandKind::Bool(b) => EvalValue::new_bool(*b),
                    OperandKind::Label(_l) => unimplemented!(),
                    OperandKind::VirtualRegister(vreg) => eval.vregs.get(vreg).unwrap().clone(),
                    OperandKind::Fn(name) => EvalValue {
                        kind: EvalValueKind::Fn(name.to_owned()),
                        typ: value.typ.clone(),
                    },
                };

                eval.vregs.insert(ir.res_vreg.unwrap(), value);
            }
        }
        pc += 1;
    }

    eval
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::{ast::Parser, lex::Lexer, type_checker};

    #[test]
    fn eval_print_iadd() {
        let input = "package main
            func main() {
              println(123 + 456)
            }
            ";

        let file_id = 1;
        let mut file_id_to_name = HashMap::new();
        file_id_to_name.insert(1, String::from("test.go"));

        let mut lexer = Lexer::new(file_id);
        lexer.lex(input);
        assert!(lexer.errors.is_empty());

        let mut parser = Parser::new(input, &lexer, &file_id_to_name);
        let mut ast_nodes = parser.parse();
        assert!(parser.errors.is_empty());

        let mut name_to_type = parser.name_to_type;

        assert!(type_checker::check_nodes(&mut ast_nodes, &mut name_to_type).is_empty());

        let mut ir_emitter = super::Emitter::new();
        ir_emitter.emit(&ast_nodes);

        let builtins = Parser::builtins(16);
        assert_eq!(ir_emitter.fn_defs.len(), builtins.len() + 1);

        let ir_eval = super::eval(&ir_emitter.fn_defs[1].instructions);
        assert_eq!(ir_eval.stdout, b"579\n");
    }

    #[test]
    fn eval_print_imul() {
        let input = "package main
            func main() {
              println(123 * 456 + 3)
            }
            ";

        let file_id = 1;
        let mut file_id_to_name = HashMap::new();
        file_id_to_name.insert(1, String::from("test.go"));

        let mut lexer = Lexer::new(file_id);
        lexer.lex(input);
        assert!(lexer.errors.is_empty());

        let mut parser = Parser::new(input, &lexer, &file_id_to_name);
        let mut ast_nodes = parser.parse();
        assert!(parser.errors.is_empty());

        let mut name_to_type = parser.name_to_type;
        assert!(type_checker::check_nodes(&mut ast_nodes, &mut name_to_type).is_empty());

        let mut ir_emitter = super::Emitter::new();
        ir_emitter.emit(&ast_nodes);

        let builtins = Parser::builtins(16);
        assert_eq!(ir_emitter.fn_defs.len(), builtins.len() + 1);

        let ir_eval = super::eval(&ir_emitter.fn_defs[1].instructions);
        assert_eq!(ir_eval.stdout, b"56091\n");
    }

    #[test]
    fn eval_print_idiv() {
        let input = "package main
            func main() {
              println(123 * 456 / 3)
            }
            ";

        let file_id = 1;
        let mut file_id_to_name = HashMap::new();
        file_id_to_name.insert(1, String::from("test.go"));

        let mut lexer = Lexer::new(file_id);
        lexer.lex(input);
        assert!(lexer.errors.is_empty());

        let mut parser = Parser::new(input, &lexer, &file_id_to_name);
        let mut ast_nodes = parser.parse();
        assert!(parser.errors.is_empty());

        let mut name_to_type = parser.name_to_type;
        assert!(type_checker::check_nodes(&mut ast_nodes, &mut name_to_type).is_empty());

        let mut ir_emitter = super::Emitter::new();
        ir_emitter.emit(&ast_nodes);

        let builtins = Parser::builtins(16);
        assert_eq!(ir_emitter.fn_defs.len(), builtins.len() + 1);

        let ir_eval = super::eval(&ir_emitter.fn_defs[1].instructions);
        assert_eq!(ir_eval.stdout, b"18696\n");
    }

    #[test]
    fn eval_print_bool() {
        let input = "package main
            func main() {
              println(true)
              println(false)
            }
            ";

        let file_id = 1;
        let mut file_id_to_name = HashMap::new();
        file_id_to_name.insert(1, String::from("test.go"));

        let mut lexer = Lexer::new(file_id);
        lexer.lex(input);
        assert!(lexer.errors.is_empty());

        let mut parser = Parser::new(input, &lexer, &file_id_to_name);
        let mut ast_nodes = parser.parse();
        assert!(parser.errors.is_empty());

        let mut name_to_type = parser.name_to_type;
        let type_errors = type_checker::check_nodes(&mut ast_nodes, &mut name_to_type);
        assert!(type_errors.is_empty(), "{:#?}", type_errors);

        let mut ir_emitter = super::Emitter::new();
        ir_emitter.emit(&ast_nodes);

        let builtins = Parser::builtins(16);
        assert_eq!(ir_emitter.fn_defs.len(), builtins.len() + 1);

        let ir_eval = super::eval(&ir_emitter.fn_defs[1].instructions);
        assert_eq!(ir_eval.stdout, b"true\nfalse\n");
    }

    #[test]
    fn eval_if_false_then_print() {
        let input = "package main
            func main() {
              if false {
                  println(123)
              }
            }
            ";

        let file_id = 1;
        let mut file_id_to_name = HashMap::new();
        file_id_to_name.insert(1, String::from("test.go"));

        let mut lexer = Lexer::new(file_id);
        lexer.lex(input);
        assert!(lexer.errors.is_empty());

        let mut parser = Parser::new(input, &lexer, &file_id_to_name);
        let mut ast_nodes = parser.parse();
        assert!(parser.errors.is_empty());

        let mut name_to_type = parser.name_to_type;
        assert!(type_checker::check_nodes(&mut ast_nodes, &mut name_to_type).is_empty());

        let mut ir_emitter = super::Emitter::new();
        ir_emitter.emit(&ast_nodes);

        let builtins = Parser::builtins(16);
        assert_eq!(ir_emitter.fn_defs.len(), builtins.len() + 1);

        let ir_eval = super::eval(&ir_emitter.fn_defs[1].instructions);
        assert!(ir_eval.stdout.is_empty());
    }

    #[test]
    fn eval_if_true_then_print() {
        let input = "package main
            func main() {
              if true {
                  println(123)
              }
            }
            ";

        let file_id = 1;
        let mut file_id_to_name = HashMap::new();
        file_id_to_name.insert(1, String::from("test.go"));

        let mut lexer = Lexer::new(file_id);
        lexer.lex(input);
        assert!(lexer.errors.is_empty());

        let mut parser = Parser::new(input, &lexer, &file_id_to_name);
        let mut ast_nodes = parser.parse();
        assert!(parser.errors.is_empty());

        let mut name_to_type = parser.name_to_type;
        assert!(type_checker::check_nodes(&mut ast_nodes, &mut name_to_type).is_empty());

        let mut ir_emitter = super::Emitter::new();
        ir_emitter.emit(&ast_nodes);

        let builtins = Parser::builtins(16);
        assert_eq!(ir_emitter.fn_defs.len(), builtins.len() + 1);

        let ir_eval = super::eval(&ir_emitter.fn_defs[1].instructions);
        assert_eq!(ir_eval.stdout, b"123\n");
    }

    #[test]
    fn eval_if_else_branch_then() {
        let input = " 
package main

func main() {
	if true {
		println(2)
	} else {
		println(3)
	}
}
            ";

        let file_id = 1;
        let mut file_id_to_name = HashMap::new();
        file_id_to_name.insert(1, String::from("test.go"));

        let mut lexer = Lexer::new(file_id);
        lexer.lex(input);
        assert!(lexer.errors.is_empty());

        let mut parser = Parser::new(input, &lexer, &file_id_to_name);
        let mut ast_nodes = parser.parse();
        assert!(parser.errors.is_empty());

        let mut name_to_type = parser.name_to_type;
        assert!(type_checker::check_nodes(&mut ast_nodes, &mut name_to_type).is_empty());

        let mut ir_emitter = super::Emitter::new();
        ir_emitter.emit(&ast_nodes);

        let builtins = Parser::builtins(16);
        assert_eq!(ir_emitter.fn_defs.len(), builtins.len() + 1);

        let ir_eval = super::eval(&ir_emitter.fn_defs[1].instructions);
        assert_eq!(ir_eval.stdout, b"2\n");
    }

    #[test]
    fn eval_if_else_branch_else() {
        let input = " 
package main

func main() {
	if false {
		println(2)
	} else {
		println(3)
	}
}
            ";

        let file_id = 1;
        let mut file_id_to_name = HashMap::new();
        file_id_to_name.insert(1, String::from("test.go"));

        let mut lexer = Lexer::new(file_id);
        lexer.lex(input);
        assert!(lexer.errors.is_empty());

        let mut parser = Parser::new(input, &lexer, &file_id_to_name);
        let mut ast_nodes = parser.parse();
        assert!(parser.errors.is_empty());

        let mut name_to_type = parser.name_to_type;
        assert!(type_checker::check_nodes(&mut ast_nodes, &mut name_to_type).is_empty());

        let mut ir_emitter = super::Emitter::new();
        ir_emitter.emit(&ast_nodes);

        let builtins = Parser::builtins(16);
        assert_eq!(ir_emitter.fn_defs.len(), builtins.len() + 1);

        let ir_eval = super::eval(&ir_emitter.fn_defs[1].instructions);
        assert_eq!(ir_eval.stdout, b"3\n");
    }

    #[test]
    fn eval_if_cmp_true() {
        let input = " 
package main

func main() {
	if 1 == 1 {
      println(1)
  } else {
      println(2)
	} 
}
            ";

        let file_id = 1;
        let mut file_id_to_name = HashMap::new();
        file_id_to_name.insert(1, String::from("test.go"));

        let mut lexer = Lexer::new(file_id);
        lexer.lex(input);
        assert!(lexer.errors.is_empty());

        let mut parser = Parser::new(input, &lexer, &file_id_to_name);
        let mut ast_nodes = parser.parse();
        assert!(parser.errors.is_empty());

        let mut name_to_type = parser.name_to_type;
        assert!(type_checker::check_nodes(&mut ast_nodes, &mut name_to_type).is_empty());

        let mut ir_emitter = super::Emitter::new();
        ir_emitter.emit(&ast_nodes);

        let builtins = Parser::builtins(16);
        assert_eq!(ir_emitter.fn_defs.len(), builtins.len() + 1);

        let ir_eval = super::eval(&ir_emitter.fn_defs[1].instructions);
        assert_eq!(ir_eval.stdout, b"1\n");
    }

    #[test]
    fn eval_if_cmp_false() {
        let input = " 
package main

func main() {
	if 1 == 4 {
      println(1)
  } else {
      println(2)
	} 
}
            ";

        let file_id = 1;
        let mut file_id_to_name = HashMap::new();
        file_id_to_name.insert(1, String::from("test.go"));

        let mut lexer = Lexer::new(file_id);
        lexer.lex(input);
        assert!(lexer.errors.is_empty());

        let mut parser = Parser::new(input, &lexer, &file_id_to_name);
        let mut ast_nodes = parser.parse();
        assert!(parser.errors.is_empty());

        let mut name_to_type = parser.name_to_type;
        assert!(type_checker::check_nodes(&mut ast_nodes, &mut name_to_type).is_empty());

        let mut ir_emitter = super::Emitter::new();
        ir_emitter.emit(&ast_nodes);

        let builtins = Parser::builtins(16);
        assert_eq!(ir_emitter.fn_defs.len(), builtins.len() + 1);

        let ir_eval = super::eval(&ir_emitter.fn_defs[1].instructions);
        assert_eq!(ir_eval.stdout, b"2\n");
    }
}
