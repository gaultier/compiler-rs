use std::fmt::Display;

#[cfg(test)]
use proptest_derive::Arbitrary;

use serde::Serialize;

use crate::{ast::Node, error::Error, origin::Origin};

#[derive(Serialize, Clone, PartialEq, Eq, Debug, PartialOrd, Ord)]
pub enum TypeKind {
    Unknown,
    Void,
    Number,
    Bool,
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
            kind: Box::new(TypeKind::Unknown),
            size: None,
            origin: Origin::new_unknown(),
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &*self.kind {
            TypeKind::Unknown => f.write_str("any"),
            TypeKind::Void => f.write_str("void"),
            TypeKind::Number => write!(f, "int"),
            TypeKind::Bool => f.write_str("bool"),
            TypeKind::Function(ret, args) => {
                f.write_str("(")?;
                for arg in args {
                    arg.fmt(f)?;
                }
                f.write_str(")")?;

                match &*ret.kind {
                    TypeKind::Unknown => panic!("invalid return type: {:#?}", ret),
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
            (TypeKind::Unknown, _) => Ok(self.clone()),
            (_, TypeKind::Unknown) => Ok(other.clone()),
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

pub struct Checker {}

impl Default for Checker {
    fn default() -> Self {
        Self::new()
    }
}

impl Checker {
    pub fn new() -> Self {
        Self {}
    }

    pub fn check_node(&mut self, node: &mut Node, errs: &mut Vec<Error>) {
        match &mut node.kind {
            crate::ast::NodeKind::Package(_) => {}
            crate::ast::NodeKind::FnDef(_) => match &*node.typ.kind {
                TypeKind::Function(ret_type, args) => {
                    assert_ne!(*ret_type.kind, TypeKind::Unknown);

                    if matches!(*ret_type.kind, TypeKind::Function(_, _)) {
                        unimplemented!();
                    }

                    for arg in args {
                        assert_ne!(*arg.kind, TypeKind::Unknown);
                        if matches!(*arg.kind, TypeKind::Function(_, _)) {
                            unimplemented!();
                        }
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
            crate::ast::NodeKind::Identifier(_) => {
                assert_ne!(&*node.typ.kind, &TypeKind::Unknown);
            }
            crate::ast::NodeKind::FnCall => {
                let (ret_type, args_type) = match &*node.children[0].typ.kind {
                    TypeKind::Function(ret_type, args_type) => {
                        assert_eq!(args_type.len(), 1);
                        (ret_type, args_type)
                    }
                    _ => panic!("unexpected function type: {:#?}", node.typ),
                };

                if node.children.len() != args_type.len() {
                    errs.push(Error::new_incompatible_arguments_count(
                        &node.origin,
                        args_type.len(),
                        node.children.len(),
                    ));

                    return;
                }

                for (i, arg) in node.children.iter().enumerate() {
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
            crate::ast::NodeKind::Add
            | crate::ast::NodeKind::Multiply
            | crate::ast::NodeKind::Divide => {
                let rhs = &node.children[0].typ;
                let lhs = &node.children[1].typ;

                let typ = lhs.merge(&rhs);
                match typ {
                    Ok(typ) => node.typ = typ,
                    Err(err) => {
                        errs.push(err);
                        // To avoid cascading errors, pretend the type is fine.
                        node.typ = Type::new_int();
                    }
                }
            }
            crate::ast::NodeKind::If(cond) => {
                self.check_node(cond, errs);
                for node in &mut node.children {
                    self.check_node(node, errs);
                }
            }
        }
    }

    pub fn check_nodes(&mut self, nodes: &mut [Node]) -> Vec<Error> {
        let mut errs = Vec::new();

        for node in nodes {
            self.check_node(node, &mut errs);
        }

        errs
    }
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
