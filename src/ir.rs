use std::{
    collections::{BTreeMap, HashMap},
    fmt::Display,
    io::Write,
    panic,
};

use log::trace;
use serde::Serialize;

use crate::{
    ast::{NameToDef, Node, NodeId, NodeKind},
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
pub struct Emitter<'a> {
    pub fn_defs: Vec<FnDef>,
    pub labels: Vec<String>,
    label_current: usize,
    node_to_type: &'a HashMap<NodeId, Type>,
    nodes: &'a [Node],
    name_to_def: &'a NameToDef,
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
    node_to_vreg: HashMap<NodeId, VirtualRegister>,
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
            node_to_vreg: HashMap::new(),
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

impl<'a> Emitter<'a> {
    pub(crate) fn new(
        nodes: &'a [Node],
        node_to_type: &'a HashMap<NodeId, Type>,
        name_to_def: &'a NameToDef,
    ) -> Self {
        Self {
            fn_defs: Vec::new(),
            labels: Vec::new(),
            label_current: 0,
            node_to_type,
            nodes,
            name_to_def,
        }
    }

    fn fn_def_mut(&mut self) -> &mut FnDef {
        self.fn_defs.last_mut().unwrap()
    }

    fn vreg(&self) -> VirtualRegister {
        self.fn_defs
            .last()
            .unwrap()
            .instructions
            .last()
            .unwrap()
            .res_vreg
            .unwrap()
    }

    fn emit_node(&mut self, node_id: NodeId) {
        let node = &self.nodes[node_id];

        match &node.kind {
            NodeKind::File(decls) => {
                for decl in decls {
                    self.emit_node(*decl);
                }
            }
            NodeKind::Package(_) => {}
            // Start of a new function.
            NodeKind::FnDef(crate::ast::FnDef {
                name,
                args: _,
                ret: _,
                body,
            }) => {
                let stack_size = 0; // TODO
                let typ = self.node_to_type.get(&node_id).unwrap();
                self.fn_defs
                    .push(FnDef::new(name.to_owned(), typ, node.origin, stack_size));
                self.emit_node(*body);

                self.fn_def_mut().live_ranges = self.fn_def_mut().compute_live_ranges();
            }
            NodeKind::Unary(_op, _expr) => todo!(),
            NodeKind::For { cond, block } => {
                let loop_label = format!(".{}_for_loop", self.label_current);
                let end_label = format!(".{}_for_end", self.label_current);
                self.label_current += 1;

                self.fn_def_mut().instructions.push(Instruction {
                    kind: InstructionKind::LabelDef(loop_label.clone()),
                    origin: node.origin,
                    res_vreg: None,
                    typ: Type::new_void(),
                });

                if let Some(cond) = cond {
                    self.emit_node(*cond);
                    let vreg = self.vreg();

                    let op = Operand {
                        kind: OperandKind::VirtualRegister(vreg),
                        typ: self.fn_def_mut().instructions.last().unwrap().typ.clone(),
                    };
                    self.fn_def_mut().instructions.push(Instruction {
                        kind: InstructionKind::JumpIfFalse(end_label.clone(), op),
                        origin: node.origin,
                        res_vreg: None,
                        typ: Type::new_void(),
                    });
                }
                self.emit_node(*block);
                self.fn_def_mut().instructions.push(Instruction {
                    kind: InstructionKind::Jump(loop_label.clone()),
                    origin: node.origin,
                    res_vreg: None,
                    typ: Type::new_void(),
                });

                self.fn_def_mut().instructions.push(Instruction {
                    kind: InstructionKind::LabelDef(end_label),
                    origin: node.origin,
                    res_vreg: None,
                    typ: Type::new_void(),
                });
            }
            crate::ast::NodeKind::Number(num) => {
                let typ = self.node_to_type.get(&node_id).unwrap();
                assert_eq!(*typ.kind, TypeKind::Number);

                let res_vreg = self.fn_def_mut().make_vreg(typ);
                self.fn_def_mut().instructions.push(Instruction {
                    kind: InstructionKind::Set(Operand::new_int(*num as i64)),
                    origin: node.origin,
                    res_vreg: Some(res_vreg),
                    typ: typ.clone(),
                });
            }
            crate::ast::NodeKind::Bool(b) => {
                let typ = self.node_to_type.get(&node_id).unwrap();
                assert_eq!(*typ.kind, TypeKind::Bool);

                let res_vreg = self.fn_def_mut().make_vreg(typ);
                self.fn_def_mut().instructions.push(Instruction {
                    kind: InstructionKind::Set(Operand::new_bool(*b)),
                    origin: node.origin,
                    res_vreg: Some(res_vreg),
                    typ: typ.clone(),
                });
            }
            crate::ast::NodeKind::Identifier(identifier) => {
                let def_id = self.name_to_def.get_definitive(identifier).unwrap();
                dbg!(identifier, def_id);
                dbg!(&self.fn_def_mut().node_to_vreg);
                let vreg = *self.fn_def_mut().node_to_vreg.get(def_id).unwrap();

                let typ = self.node_to_type.get(&node_id).unwrap();
                let res_vreg = self.fn_def_mut().make_vreg(typ);
                self.fn_def_mut().instructions.push(Instruction {
                    kind: InstructionKind::Set(Operand::new_vreg(vreg, typ)),
                    origin: node.origin,
                    res_vreg: Some(res_vreg),
                    typ: typ.clone(),
                });
            }
            crate::ast::NodeKind::FnCall { callee, args } => {
                // TODO: Support function pointers.
                let ast_fn_name = self.nodes[*callee].kind.as_identifier().unwrap();
                let def_id = self.name_to_def.get_definitive(ast_fn_name).unwrap();

                let callee_type = self.node_to_type.get(def_id).unwrap();
                let arg_type = callee_type.to_string();

                // Check type.
                let typ = self.node_to_type.get(&node_id).unwrap();
                let (res_vreg, ret_type, arg_types) = match &*callee_type.kind {
                    TypeKind::Function(ret_type, arg_types) if *ret_type.kind == TypeKind::Void => {
                        (None, ret_type.clone(), arg_types)
                    }
                    TypeKind::Function(ret_type, arg_types) => (
                        Some(self.fn_def_mut().make_vreg(typ)),
                        ret_type.clone(),
                        arg_types,
                    ),
                    _ => panic!("not a function type: {:#?}", typ),
                };

                let arg0_typ = arg_types.first().map(|x| x.to_string()).unwrap_or_default();
                let real_fn_name = fn_name_ast_to_ir(ast_fn_name, &arg_type, &arg0_typ);

                self.emit_node(*args);
                // TODO: Handle multiple args.
                let (arg_vreg, arg_typ) = self
                    .fn_def_mut()
                    .instructions
                    .last()
                    .map(|x| (x.res_vreg.unwrap(), &x.typ))
                    .unwrap();
                let operands = vec![Operand::new_vreg(arg_vreg, arg_typ)];

                trace!(
                    "ir: emit fn call: ast_name={} real_name={} arg_type={:?}",
                    ast_fn_name, real_fn_name, arg_type,
                );

                self.fn_def_mut().instructions.push(Instruction {
                    kind: InstructionKind::FnCall(real_fn_name, operands),
                    origin: node.origin,
                    res_vreg,
                    typ: ret_type,
                });
            }
            crate::ast::NodeKind::Cmp(lhs, rhs) => {
                // Set by the parser.
                let typ = self.node_to_type.get(&node_id).unwrap();
                assert_eq!(*typ.kind, TypeKind::Bool);

                let lhs_type = self.node_to_type.get(lhs).unwrap();
                let rhs_type = self.node_to_type.get(rhs).unwrap();
                assert_ne!(*lhs_type.kind, TypeKind::Any);
                assert_ne!(*rhs_type.kind, TypeKind::Any);

                self.emit_node(*lhs);
                let lhs_vreg = self.vreg();
                self.emit_node(*rhs);
                let rhs_vreg = self.vreg();

                let res_vreg = self.fn_def_mut().make_vreg(typ);

                self.fn_def_mut().instructions.push(Instruction {
                    kind: InstructionKind::ICmp(
                        Operand {
                            kind: OperandKind::VirtualRegister(lhs_vreg),
                            typ: lhs_type.clone(),
                        },
                        Operand {
                            kind: OperandKind::VirtualRegister(rhs_vreg),
                            typ: rhs_type.clone(),
                        },
                    ),
                    origin: node.origin,
                    res_vreg: Some(res_vreg),
                    typ: typ.clone(),
                });
            }
            crate::ast::NodeKind::Add(ast_lhs, ast_rhs) => {
                let typ = self.node_to_type.get(&node_id).unwrap();
                let lhs_type = self.node_to_type.get(ast_lhs).unwrap();
                let rhs_type = self.node_to_type.get(ast_rhs).unwrap();
                assert_eq!(*lhs_type.kind, TypeKind::Number);
                assert_eq!(*rhs_type.kind, TypeKind::Number);
                assert_eq!(*typ.kind, TypeKind::Number);

                self.emit_node(*ast_lhs);
                let (ir_lhs_vreg, ir_lhs_typ) = (
                    self.vreg(),
                    self.fn_def_mut().instructions.last().unwrap().typ.clone(),
                );

                self.emit_node(*ast_rhs);
                let (ir_rhs_vreg, ir_rhs_typ) = (
                    self.vreg(),
                    self.fn_def_mut().instructions.last().unwrap().typ.clone(),
                );

                let res_vreg = self.fn_def_mut().make_vreg(typ);

                self.fn_def_mut().instructions.push(Instruction {
                    kind: InstructionKind::IAdd(
                        Operand::new_vreg(ir_lhs_vreg, &ir_lhs_typ),
                        Operand::new_vreg(ir_rhs_vreg, &ir_rhs_typ),
                    ),
                    origin: node.origin,
                    res_vreg: Some(res_vreg),
                    typ: typ.clone(),
                });
            }
            crate::ast::NodeKind::Multiply(ast_lhs, ast_rhs) => {
                let typ = self.node_to_type.get(&node_id).unwrap();
                let lhs_type = self.node_to_type.get(ast_lhs).unwrap();
                let rhs_type = self.node_to_type.get(ast_rhs).unwrap();
                assert_eq!(*lhs_type.kind, TypeKind::Number);
                assert_eq!(*rhs_type.kind, TypeKind::Number);
                assert_eq!(*typ.kind, TypeKind::Number);

                self.emit_node(*ast_lhs);
                let (ir_lhs_vreg, ir_lhs_typ) = (
                    self.vreg(),
                    self.fn_def_mut().instructions.last().unwrap().typ.clone(),
                );

                self.emit_node(*ast_rhs);
                let (ir_rhs_vreg, ir_rhs_typ) = (
                    self.vreg(),
                    self.fn_def_mut().instructions.last().unwrap().typ.clone(),
                );

                let res_vreg = self.fn_def_mut().make_vreg(typ);

                self.fn_def_mut().instructions.push(Instruction {
                    kind: InstructionKind::IMultiply(
                        Operand::new_vreg(ir_lhs_vreg, &ir_lhs_typ),
                        Operand::new_vreg(ir_rhs_vreg, &ir_rhs_typ),
                    ),
                    origin: node.origin,
                    res_vreg: Some(res_vreg),
                    typ: typ.clone(),
                });
            }
            crate::ast::NodeKind::Divide(ast_lhs, ast_rhs) => {
                let typ = self.node_to_type.get(&node_id).unwrap();
                let lhs_type = self.node_to_type.get(ast_lhs).unwrap();
                let rhs_type = self.node_to_type.get(ast_rhs).unwrap();
                assert_eq!(*lhs_type.kind, TypeKind::Number);
                assert_eq!(*rhs_type.kind, TypeKind::Number);
                assert_eq!(*typ.kind, TypeKind::Number);

                self.emit_node(*ast_lhs);
                let (ir_lhs_vreg, ir_lhs_typ) = (
                    self.vreg(),
                    self.fn_def_mut().instructions.last().unwrap().typ.clone(),
                );

                self.emit_node(*ast_rhs);
                let (ir_rhs_vreg, ir_rhs_typ) = (
                    self.vreg(),
                    self.fn_def_mut().instructions.last().unwrap().typ.clone(),
                );

                let res_vreg = self.fn_def_mut().make_vreg(typ);

                self.fn_def_mut().instructions.push(Instruction {
                    kind: InstructionKind::IDivide(
                        Operand::new_vreg(ir_lhs_vreg, &ir_lhs_typ),
                        Operand::new_vreg(ir_rhs_vreg, &ir_rhs_typ),
                    ),
                    origin: node.origin,
                    res_vreg: Some(res_vreg),
                    typ: typ.clone(),
                });
            }
            NodeKind::Block(stmts) => {
                for stmt in stmts {
                    self.emit_node(*stmt);
                }
            }
            NodeKind::If {
                cond,
                then_block: then_block_id,
                else_block: else_block_id,
            } => {
                let cond_type = &self.node_to_type.get(cond).unwrap();
                assert_eq!(*cond_type.kind, TypeKind::Bool);

                self.emit_node(*cond);

                let then_block = &self.nodes[*then_block_id];
                assert!(matches!(then_block.kind, NodeKind::Block(_)));

                let else_label = if else_block_id.is_some() {
                    Some(format!(".{}_if_else", self.label_current))
                } else {
                    None
                };
                let end_label = format!(".{}_if_end", self.label_current);
                self.label_current += 1;

                let vreg: VirtualRegister = self.vreg();
                let typ = self.fn_def_mut().instructions.last().unwrap().typ.clone();
                assert_eq!(*typ.kind, TypeKind::Bool);

                let op = Operand {
                    kind: OperandKind::VirtualRegister(vreg),
                    typ,
                };
                self.fn_def_mut().instructions.push(Instruction {
                    kind: InstructionKind::JumpIfFalse(
                        else_label.clone().unwrap_or_else(|| end_label.clone()),
                        op,
                    ),
                    origin: node.origin,
                    res_vreg: None,
                    typ: Type::new_void(),
                });

                // Then-body.
                self.emit_node(*then_block_id);

                // Else body.
                if let Some(else_block_id) = else_block_id {
                    self.fn_def_mut().instructions.push(Instruction {
                        kind: InstructionKind::Jump(end_label.clone()),
                        origin: node.origin,
                        res_vreg: None,
                        typ: Type::new_void(),
                    });

                    self.fn_def_mut().instructions.push(Instruction {
                        kind: InstructionKind::LabelDef(else_label.clone().unwrap()),
                        origin: node.origin,
                        res_vreg: None,
                        typ: Type::new_void(),
                    });

                    self.emit_node(*else_block_id);
                }

                // End.
                {
                    self.fn_def_mut().instructions.push(Instruction {
                        kind: InstructionKind::LabelDef(end_label),
                        origin: node.origin,
                        res_vreg: None,
                        typ: Type::new_void(),
                    });
                }
            }
            NodeKind::VarDecl(identifier, expr) => {
                self.emit_node(*expr);
                let op_vreg = self.vreg();
                let op_typ = self.fn_def_mut().instructions.last().unwrap().typ.clone();

                // TODO: Should every `make_vreg()` call also insert in this map?
                // But the only use of the map is to map a name to a vreg.
                self.fn_def_mut().node_to_vreg.insert(node_id, op_vreg);

                let typ = self.node_to_type.get(&node_id).unwrap();
                self.fn_def_mut().instructions.push(Instruction {
                    kind: InstructionKind::VarDecl(
                        identifier.clone(),
                        Operand {
                            kind: OperandKind::VirtualRegister(op_vreg),
                            typ: op_typ,
                        },
                    ),
                    origin: node.origin,
                    res_vreg: None,
                    typ: typ.clone(),
                });
            }
            NodeKind::Assignment(_lhs, _op, _rhs) => {
                todo!()
            }
            NodeKind::Arguments(args) => {
                // TODO: More?
                for arg in args {
                    self.emit_node(*arg);
                }
            }
        }
    }

    pub fn emit_nodes(&mut self) {
        self.emit_node(NodeId(0));
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

    let mut pc: usize = 0;
    loop {
        if pc >= irs.len() {
            break;
        }

        let ir = &irs[pc];

        match &ir.kind {
            InstructionKind::VarDecl(_, op) => {
                assert!(ir.res_vreg.is_none());
                let __vreg = op.as_vreg().unwrap();
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

    use crate::{
        ast::Parser,
        error::{Error, ErrorKind},
        ir::{Eval, FnDef},
        lex::Lexer,
        type_checker,
    };

    fn run(input: &str) -> Result<(usize, Vec<FnDef>, Eval), Vec<Error>> {
        let file_id = 1;
        let mut file_id_to_name = HashMap::new();
        file_id_to_name.insert(1, String::from("test.go"));

        let mut lexer = Lexer::new(file_id);
        lexer.lex(input);

        let mut parser = Parser::new(input, &lexer, &file_id_to_name);
        parser.parse();
        let builtins_len = 1;

        let mut errors = parser.errors;
        errors.extend(type_checker::check_nodes(
            &parser.nodes,
            &mut parser.node_to_type,
            &parser.name_to_def,
        ));
        if !errors.is_empty() {
            return Err(errors);
        }

        let mut ir_emitter =
            super::Emitter::new(&parser.nodes, &parser.node_to_type, &parser.name_to_def);
        ir_emitter.emit_nodes();

        let main = ir_emitter
            .fn_defs
            .iter()
            .find(|f| f.name == "main")
            .unwrap();
        let ir_eval = super::eval(&main.instructions);
        Ok((builtins_len, ir_emitter.fn_defs, ir_eval))
    }

    #[test]
    fn eval_print_iadd() {
        let input = "package main
            func main() {
              println(123 + 456)
            }
            ";

        let (builtins_len, fn_defs, eval) = run(&input).unwrap();
        assert_eq!(fn_defs.len(), builtins_len + 1);
        assert_eq!(eval.stdout, b"579\n");
    }

    #[test]
    fn eval_print_imul() {
        let input = "package main
            func main() {
              println(123 * 456 + 3)
            }
            ";

        let (builtins_len, fn_defs, eval) = run(&input).unwrap();
        assert_eq!(fn_defs.len(), builtins_len + 1);
        assert_eq!(eval.stdout, b"56091\n");
    }

    #[test]
    fn eval_print_idiv() {
        let input = "package main
            func main() {
              println(123 * 456 / 3)
            }
            ";

        let (builtins_len, fn_defs, eval) = run(&input).unwrap();
        assert_eq!(fn_defs.len(), builtins_len + 1);
        assert_eq!(eval.stdout, b"18696\n");
    }

    #[test]
    fn eval_print_bool() {
        let input = "package main
            func main() {
              println(true)
              println(false)
            }
            ";

        let (builtins_len, fn_defs, eval) = run(&input).unwrap();
        assert_eq!(fn_defs.len(), builtins_len + 1);
        assert_eq!(eval.stdout, b"true\nfalse\n");
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

        let (builtins_len, fn_defs, eval) = run(&input).unwrap();
        assert_eq!(fn_defs.len(), builtins_len + 1);
        assert!(eval.stdout.is_empty());
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

        let (builtins_len, fn_defs, eval) = run(&input).unwrap();
        assert_eq!(fn_defs.len(), builtins_len + 1);
        assert_eq!(eval.stdout, b"123\n");
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

        let (builtins_len, fn_defs, eval) = run(&input).unwrap();
        assert_eq!(fn_defs.len(), builtins_len + 1);
        assert_eq!(eval.stdout, b"2\n");
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

        let (builtins_len, fn_defs, eval) = run(&input).unwrap();
        assert_eq!(fn_defs.len(), builtins_len + 1);
        assert_eq!(eval.stdout, b"3\n");
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

        let (builtins_len, fn_defs, eval) = run(&input).unwrap();
        assert_eq!(fn_defs.len(), builtins_len + 1);
        assert_eq!(eval.stdout, b"1\n");
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

        let (builtins_len, fn_defs, eval) = run(&input).unwrap();
        assert_eq!(fn_defs.len(), builtins_len + 1);
        assert_eq!(eval.stdout, b"2\n");
    }

    #[test]
    fn eval_var() {
        let input = " 
package main

func main() {
  var a = 3*4
  var b = 1 + 2 + a
  println(a)
  println(b)
}
";

        let (builtins_len, fn_defs, eval) = run(&input).unwrap();
        assert_eq!(fn_defs.len(), builtins_len + 1);
        assert_eq!(eval.stdout, b"12\n15\n");
    }

    #[test]
    fn eval_var_shadowed_in_if() {
        let input = " 
package main

func main() {
  var a = 3*4
  if true {
    var a = 1
    println(a)
  }
}
";

        let (builtins_len, fn_defs, eval) = run(&input).unwrap();
        assert_eq!(fn_defs.len(), builtins_len + 1);
        assert_eq!(eval.stdout, b"1\n");
    }

    #[test]
    fn eval_var_shadowed_in_block() {
        let input = " 
package main

func main() {
  var a = 3*4
  {
    var a = 1
    println(a)
  }
}
";

        let (builtins_len, fn_defs, eval) = run(&input).unwrap();
        assert_eq!(fn_defs.len(), builtins_len + 1);
        assert_eq!(eval.stdout, b"1\n");
    }

    #[test]
    fn err_var_not_in_scope_block() {
        let input = " 
package main

func main() {
  {
  var a = 3*4
  }
  {
    println(a)
  }
}
";

        let errs = run(&input).unwrap_err();
        assert_eq!(errs.len(), 1);
        let err = &errs[0];
        assert_eq!(err.kind, ErrorKind::UnknownIdentifier);
    }

    #[test]
    fn err_var_in_if_not_in_scope_in_else() {
        let input = " 
package main

func main() {
  if true {
    var a = 3*4
  } else {
    println(a)
  }
}
";

        let errs = run(&input).unwrap_err();
        assert_eq!(errs.len(), 1);
        let err = &errs[0];
        assert_eq!(err.kind, ErrorKind::UnknownIdentifier);
    }

    #[test]
    fn err_var_in_else_not_in_scope_in_if() {
        let input = " 
package main

func main() {
  if true {
    println(a)
  } else {
    var a = 3*4
  }
}
";

        let errs = run(&input).unwrap_err();
        assert!(
            errs.iter()
                .find(|e| e.kind == ErrorKind::UnknownIdentifier)
                .is_some()
        );
    }

    #[test]
    fn eval_var_in_parent_scope() {
        let input = " 
package main

func main() {
  {
    var a = 3*4
    {
        println(a)
    }
  } 
}
";

        let (builtins_len, fn_defs, eval) = run(&input).unwrap();
        assert_eq!(fn_defs.len(), builtins_len + 1);
        assert_eq!(eval.stdout, b"12\n");
    }

    #[test]
    fn err_var_redefined_in_current_scope() {
        let input = " 
package main

func main() {
    var a = 3*4
    var b = 3*4
    var a = 3*4
}
";

        let errs = run(&input).unwrap_err();
        assert!(
            errs.iter()
                .find(|e| e.kind == ErrorKind::NameAlreadyDefined)
                .is_some()
        );
    }
}
