use std::{/*collections::BTreeSet,*/ fmt::Display};

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

#[derive(Serialize, Clone, PartialEq, Eq, Debug, PartialOrd, Ord)]
pub struct Type {
    kind: Box<TypeKind>,
    size: usize,
    origin: Origin,
}

impl Default for Type {
    fn default() -> Self {
        Self {
            kind: Box::new(TypeKind::Unknown),
            size: 0,
            origin: Default::default(),
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &*self.kind {
            TypeKind::Unknown => f.write_str("any"),
            TypeKind::Void => f.write_str("void"),
            TypeKind::Number => f.write_str("u64"), // FIXME
            TypeKind::Bool => f.write_str("bool"),
            TypeKind::Function(ret, args) => {
                f.write_str("func (")?;
                for arg in args {
                    arg.fmt(f)?;
                }
                f.write_str(")")?;
                ret.fmt(f)
            }
        }?;

        Ok(())
    }
}

impl Type {
    pub(crate) fn new(kind: &TypeKind, size: usize, origin: &Origin) -> Self {
        Self {
            kind: Box::new(kind.clone()),
            size,
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

    pub(crate) fn u64() -> Self {
        Type::new(&TypeKind::Number, 8, &Origin::default())
    }

    pub(crate) fn bool() -> Self {
        Type::new(&TypeKind::Bool, 4, &Origin::default())
    }

    pub(crate) fn void() -> Self {
        Type::new(&TypeKind::Void, 0, &Origin::default())
    }

    pub(crate) fn function(return_type: &Type, args: &[Type], origin: &Origin) -> Self {
        Type::new(
            &TypeKind::Function(return_type.clone(), args.to_owned()),
            8,
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

    pub fn check(&mut self, nodes: &mut [Node]) -> Vec<Error> {
        let mut errs = Vec::new();

        let mut stack = Vec::new();

        for node in nodes {
            match node.kind {
                crate::ast::NodeKind::Number => {
                    assert_eq!(*node.typ.kind, TypeKind::Number);
                    assert_ne!(node.typ.size, 0);

                    stack.push(node);
                }
                crate::ast::NodeKind::Bool => {
                    assert_eq!(*node.typ.kind, TypeKind::Bool);
                    assert_ne!(node.typ.size, 0);

                    stack.push(node);
                }
                crate::ast::NodeKind::BuiltinPrintln => {
                    let expected_arg_type = match &*node.typ.kind {
                        TypeKind::Function(_, args) => {
                            assert_eq!(args.len(), 1);
                            &args[0]
                        }
                        _ => panic!("unexpected println type"),
                    };

                    let arg = stack.pop();
                    if arg.is_none() {
                        errs.push(Error::new_not_implemented_yet(
                            &node.origin,
                            String::from("function pointers are not supported yet"),
                        ));
                        continue;
                    }
                    let arg = arg.unwrap();

                    match *arg.typ.kind {
                        TypeKind::Number => todo!(),
                        TypeKind::Bool => todo!(),
                        _ => {
                            errs.push(Error::new_incompatible_types(
                                &arg.origin,
                                expected_arg_type,
                                &arg.typ,
                            ));
                        }
                    }
                }
                crate::ast::NodeKind::FnCall => todo!(),
                crate::ast::NodeKind::Add
                | crate::ast::NodeKind::Multiply
                | crate::ast::NodeKind::Divide => {
                    let rhs = stack.pop().unwrap();
                    let lhs = stack.pop().unwrap();

                    let typ = lhs.typ.merge(&rhs.typ);
                    match typ {
                        Ok(typ) => node.typ = typ,
                        Err(err) => {
                            errs.push(err);
                            // To avoid cascading errors, pretend the type is fine.
                            node.typ = Type::u64();
                        }
                    }
                    stack.push(node);
                }
            }
        }

        errs
    }
}
