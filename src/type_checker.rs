use std::{collections::HashMap, fmt::Display};

#[cfg(test)]
use proptest_derive::Arbitrary;

use serde::Serialize;

use crate::{
    ast::{Node, NodeId, NodeKind},
    error::Error,
    origin::Origin,
};

#[derive(Serialize, Clone, PartialEq, Eq, Debug, PartialOrd, Ord)]
pub enum TypeKind {
    Void,
    Number,
    Bool,
    Any,
    Function(Type, Vec<Type>),
}

#[derive(Serialize, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(test, derive(Arbitrary))]
pub enum Size {
    _8,
    _16,
    _32,
    _64,
}

#[derive(Serialize, Clone, PartialEq, Eq, Debug, PartialOrd, Ord)]
pub struct Type {
    pub kind: Box<TypeKind>,
    pub size: Option<Size>,
    pub origin: Origin,
}

impl Default for Type {
    fn default() -> Self {
        Self {
            kind: Box::new(TypeKind::Any),
            size: None,
            origin: Origin::new_unknown(),
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &*self.kind {
            TypeKind::Void => f.write_str("void"),
            TypeKind::Number => write!(f, "int"),
            TypeKind::Bool => f.write_str("bool"),
            TypeKind::Any => f.write_str("any"),
            TypeKind::Function(ret, args) => {
                f.write_str("(")?;
                for arg in args {
                    arg.fmt(f)?;
                }
                f.write_str(")")?;

                match &*ret.kind {
                    TypeKind::Any => panic!("invalid return type: {:#?}", ret),
                    TypeKind::Void => {} // Noop
                    _ => {
                        ret.fmt(f)?;
                    }
                };
                Ok(())
            }
        }?;

        Ok(())
    }
}

impl Type {
    pub(crate) fn new(kind: &TypeKind, size: &Option<Size>, origin: &Origin) -> Self {
        Self {
            kind: Box::new(kind.clone()),
            size: *size,
            origin: *origin,
        }
    }

    pub(crate) fn merge(&self, other: &Type) -> Result<Type, Error> {
        match (&*self.kind, &*other.kind) {
            (TypeKind::Function(_, _), TypeKind::Function(_, _)) => {
                if self == other {
                    Ok(self.clone())
                } else {
                    Err(Error::new_incompatible_types(&self.origin, self, other))
                }
            }
            (TypeKind::Any, x) if x != &TypeKind::Any => Ok(other.clone()),
            (x, TypeKind::Any) if x != &TypeKind::Any => Ok(self.clone()),
            (TypeKind::Void, TypeKind::Void) => Ok(self.clone()),
            (TypeKind::Bool, TypeKind::Bool) => Ok(self.clone()),
            (TypeKind::Number, TypeKind::Number) => {
                if self.size == other.size {
                    Ok(self.clone())
                } else {
                    Err(Error::new_incompatible_types(&self.origin, self, other))
                }
            }

            _ => Err(Error::new_incompatible_types(&self.origin, self, other)),
        }
    }

    pub(crate) fn new_int() -> Self {
        Type::new(&TypeKind::Number, &Some(Size::_64), &Origin::new_builtin())
    }

    pub(crate) fn new_any() -> Self {
        Type::new(&TypeKind::Any, &Some(Size::_64), &Origin::new_builtin())
    }

    pub(crate) fn new_bool() -> Self {
        Type::new(&TypeKind::Bool, &Some(Size::_8), &Origin::new_builtin())
    }

    pub(crate) fn new_void() -> Self {
        Type::new(&TypeKind::Void, &None, &Origin::new_builtin())
    }

    pub(crate) fn new_function(return_type: &Type, args: &[Type], origin: &Origin) -> Self {
        Type::new(
            &TypeKind::Function(return_type.clone(), args.to_owned()),
            &Some(Size::_64),
            origin,
        )
    }
}

pub fn check_node(
    node_id: NodeId,
    nodes: &[Node],
    errs: &mut Vec<Error>,
    node_to_type: &mut HashMap<NodeId, Type>,
    name_to_def: &HashMap<String, NodeId>,
) {
    let node = &nodes[node_id];
    match &node.kind {
        NodeKind::File(decls) => {
            for decl in decls {
                check_node(*decl, nodes, errs, node_to_type, name_to_def);
            }
        }
        NodeKind::Package(_) => {}
        NodeKind::VarDecl(_identifier, expr) => {
            check_node(*expr, nodes, errs, node_to_type, name_to_def);

            let expr_typ = node_to_type.get(expr).unwrap();
            node_to_type.insert(node_id, expr_typ.clone());

            // FIXME: Since the current scope gets popped
            // when exiting it, we lose information.
            //var_name_to_type
            //    .get_mut(identifier)
            //    .unwrap()
            //    .last_mut()
            //    .unwrap()
            //    .0 = node.typ.clone();
        }
        NodeKind::For { cond, block } => {
            if let Some(cond) = cond {
                check_node(*cond, nodes, errs, node_to_type, name_to_def);
            }

            for stmt in block {
                check_node(*stmt, nodes, errs, node_to_type, name_to_def);
            }
        }
        NodeKind::FnDef(crate::ast::FnDef {
            name: _,
            args,
            ret,
            body,
        }) => {
            for arg in args {
                check_node(*arg, nodes, errs, node_to_type, name_to_def);
            }
            // TODO: More checks.

            if let Some(ret) = ret {
                check_node(*ret, nodes, errs, node_to_type, name_to_def);
            }

            let arg_types: Vec<Type> = args
                .iter()
                .map(|a| node_to_type.get(&a).unwrap().clone())
                .collect();
            let ret_type = ret
                .map(|r| node_to_type.get(&r).unwrap().clone())
                .unwrap_or_else(|| Type::new_void());
            let typ = Type::new_function(&ret_type, &arg_types, &node.origin);
            node_to_type.insert(node_id, typ);

            for stmt in body {
                check_node(*stmt, nodes, errs, node_to_type, name_to_def);
            }
        }
        NodeKind::Number(_) => {
            assert!(matches!(
                *node_to_type.get(&node_id).unwrap().kind,
                TypeKind::Number
            ));
        }
        NodeKind::Bool(_) => {
            assert!(matches!(
                *node_to_type.get(&node_id).unwrap().kind,
                TypeKind::Bool
            ));
        }
        NodeKind::Identifier(identifier) => {
            let def_id = name_to_def.get(identifier).unwrap();
            let def_type = node_to_type.get(def_id).unwrap();

            node_to_type.insert(node_id, def_type.clone());
        }
        NodeKind::FnCall { callee, args } => {
            let def_type = node_to_type.get(callee).unwrap();
            let (ret_type, args_type) = match &*def_type.kind {
                TypeKind::Function(ret_type, args_type) => (ret_type.clone(), args_type.clone()),
                _ => {
                    panic!("invalid function type")
                }
            };
            if *ret_type.kind != TypeKind::Void {
                todo!();
            }

            if args.len() != args_type.len() {
                errs.push(Error::new_incompatible_arguments_count(
                    &node.origin,
                    args_type.len(),
                    args.len(),
                ));

                return;
            }

            for (i, arg) in args.iter().enumerate() {
                check_node(*arg, nodes, errs, node_to_type, name_to_def);
                let arg_type = node_to_type.get(arg).unwrap();

                let _typ = match arg_type.merge(&args_type[i]) {
                    Err(err) => {
                        errs.push(err);
                        continue;
                    }
                    Ok(t) => t,
                };
            }

            node_to_type.insert(node_id, ret_type);
        }
        NodeKind::Add(lhs, rhs) | NodeKind::Multiply(lhs, rhs) | NodeKind::Divide(lhs, rhs) => {
            check_node(*lhs, nodes, errs, node_to_type, name_to_def);
            check_node(*rhs, nodes, errs, node_to_type, name_to_def);

            let lhs_type = node_to_type.get(lhs).unwrap();
            let rhs_type = node_to_type.get(lhs).unwrap();
            let typ = lhs_type.merge(rhs_type);
            match typ {
                Ok(typ) => {
                    node_to_type.insert(node_id, typ);
                }
                Err(err) => {
                    errs.push(err);
                    // To avoid cascading errors, pretend the type is fine.
                    node_to_type.insert(node_id, Type::new_int());
                }
            }
        }
        NodeKind::Cmp(lhs, rhs) => {
            // Set by the parser.
            let typ = node_to_type.get(lhs).unwrap();
            assert_eq!(*typ.kind, TypeKind::Bool);

            check_node(*lhs, nodes, errs, node_to_type, name_to_def);
            check_node(*rhs, nodes, errs, node_to_type, name_to_def);

            let lhs_type = node_to_type.get(lhs).unwrap();
            let rhs_type = node_to_type.get(lhs).unwrap();
            let typ = lhs_type.merge(rhs_type);
            if let Err(err) = typ {
                errs.push(err);
            }
        }
        NodeKind::If {
            cond,
            then_block,
            else_block,
        } => {
            check_node(*cond, nodes, errs, node_to_type, name_to_def);
            check_node(*then_block, nodes, errs, node_to_type, name_to_def);
            check_node(*else_block, nodes, errs, node_to_type, name_to_def);
        }
        NodeKind::Block(stmts) => {
            for stmt in stmts {
                check_node(*stmt, nodes, errs, node_to_type, name_to_def);
            }
        }
    }
}

pub fn check_nodes(
    nodes: &[Node],
    node_to_type: &mut HashMap<NodeId, Type>,
    name_to_def: &HashMap<String, NodeId>,
) -> Vec<Error> {
    assert!(!nodes.is_empty());

    let mut errs = Vec::new();

    check_node(NodeId(0), nodes, &mut errs, node_to_type, name_to_def);

    errs
}

impl Size {
    pub(crate) fn as_bytes_count(&self) -> usize {
        match self {
            Size::_8 => 1,
            Size::_16 => 2,
            Size::_32 => 4,
            Size::_64 => 8,
        }
    }
}

impl Display for Size {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Size::_8 => "BYTE PTR",
            Size::_16 => "WORD PTR",
            Size::_32 => "DWORD PTR",
            Size::_64 => "QWORD PTR",
        };
        f.write_str(s)
    }
}
