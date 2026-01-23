use std::fmt::Display;

#[cfg(test)]
use proptest_derive::Arbitrary;

use serde::Serialize;

use crate::{
    ast::{NameToType, Node, NodeKind},
    error::Error,
    origin::{Origin, OriginKind},
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

pub fn check_node(node: &mut Node, errs: &mut Vec<Error>, name_to_type: &mut NameToType) {
    match &mut node.kind {
        crate::ast::NodeKind::Package(_) => {}
        NodeKind::VarDecl(identifier, expr) => {
            check_node(expr, errs, name_to_type);

            if *node.typ.kind == TypeKind::Any {
                node.typ = expr.typ.clone();

                name_to_type.get_mut(identifier).unwrap().0 = node.typ.clone();
            }
        }
        NodeKind::For { cond, block } => {
            assert_eq!(*node.typ.kind, TypeKind::Void);
            if let Some(cond) = cond {
                check_node(cond, errs, name_to_type);
            }

            for stmt in block {
                check_node(stmt, errs, name_to_type);
            }
        }
        crate::ast::NodeKind::FnDef { name: _, body } => match &*node.typ.kind {
            TypeKind::Function(ret_type, args) => {
                assert_ne!(*ret_type.kind, TypeKind::Any);

                if matches!(*ret_type.kind, TypeKind::Function(_, _)) {
                    unimplemented!();
                }

                for arg in args {
                    if node.origin.kind != OriginKind::Builtin {
                        assert_ne!(*arg.kind, TypeKind::Any);
                    }
                    if matches!(*arg.kind, TypeKind::Function(_, _)) {
                        unimplemented!();
                    }
                }

                for node in body {
                    check_node(node, errs, name_to_type);
                }
            }
            _ => panic!("invalid type for function definition"),
        },
        crate::ast::NodeKind::Number(_) => {
            assert_eq!(*node.typ.kind, TypeKind::Number);
            assert_ne!(node.typ.size, None);
        }
        crate::ast::NodeKind::Bool(_) => {
            assert_eq!(*node.typ.kind, TypeKind::Bool);
            assert_eq!(node.typ.size, Some(Size::_8));
        }
        crate::ast::NodeKind::Identifier(identifier) => {
            let (typ, _) = name_to_type.get(identifier).unwrap();
            assert_ne!(*typ.kind, TypeKind::Any);

            node.typ = typ.clone();
        }
        crate::ast::NodeKind::FnCall { callee, args } => {
            let (ret_type, args_type) = match &*callee.typ.kind {
                TypeKind::Function(ret_type, args_type) => (ret_type, args_type),
                _ => {
                    // Trying to call a non-function.
                    // Cannot do more type checking here, so bail.
                    return;
                }
            };

            if args.len() != args_type.len() {
                errs.push(Error::new_incompatible_arguments_count(
                    &node.origin,
                    args_type.len(),
                    args.len(),
                ));

                return;
            }

            for (i, arg) in args.iter_mut().enumerate() {
                check_node(arg, errs, name_to_type);

                let _typ = match arg.typ.merge(&args_type[i]) {
                    Err(err) => {
                        errs.push(err);
                        continue;
                    }
                    Ok(t) => t,
                };
            }

            node.typ = ret_type.clone();

            if *ret_type.kind != TypeKind::Void {
                todo!();
            }
        }
        crate::ast::NodeKind::Add(lhs, rhs)
        | crate::ast::NodeKind::Multiply(lhs, rhs)
        | crate::ast::NodeKind::Divide(lhs, rhs) => {
            check_node(lhs, errs, name_to_type);
            check_node(rhs, errs, name_to_type);

            let typ = lhs.typ.merge(&rhs.typ);
            match typ {
                Ok(typ) => node.typ = typ,
                Err(err) => {
                    errs.push(err);
                    // To avoid cascading errors, pretend the type is fine.
                    node.typ = Type::new_int();
                }
            }
        }
        crate::ast::NodeKind::Cmp(lhs, rhs) => {
            // Set by the parser.
            assert_eq!(*node.typ.kind, TypeKind::Bool);

            check_node(lhs, errs, name_to_type);
            check_node(rhs, errs, name_to_type);

            let typ = lhs.typ.merge(&rhs.typ);
            if let Err(err) = typ {
                errs.push(err);
            }
        }
        crate::ast::NodeKind::If {
            cond,
            then_block,
            else_block,
        } => {
            check_node(cond, errs, name_to_type);
            if let Some(then_block) = then_block {
                check_node(then_block, errs, name_to_type);
            }
            if let Some(else_block) = else_block {
                check_node(else_block, errs, name_to_type);
            }
        }
        crate::ast::NodeKind::Block(stmts) => {
            for node in stmts {
                check_node(node, errs, name_to_type);
            }
        }
    }
}

pub fn check_nodes(nodes: &mut [Node], name_to_type: &mut NameToType) -> Vec<Error> {
    let mut errs = Vec::new();

    for node in nodes {
        check_node(node, &mut errs, name_to_type);
    }

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
