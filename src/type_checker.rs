use std::{/*collections::BTreeSet,*/ fmt::Display};

use serde::Serialize;

use crate::{ast::Node, error::Error, origin::Origin};

#[derive(Serialize, Copy, Clone, PartialEq, Eq, Debug, PartialOrd, Ord)]
pub enum TypeKind {
    Unknown,
    Void,
    Number,
}

#[derive(Serialize, Copy, Clone, PartialEq, Eq, Debug, PartialOrd, Ord)]
pub struct Type {
    kind: TypeKind,
    size: usize,
    origin: Origin,
}

impl Default for Type {
    fn default() -> Self {
        Self {
            kind: TypeKind::Unknown,
            size: 0,
            origin: Default::default(),
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.kind {
            TypeKind::Unknown => f.write_str("any"),
            TypeKind::Void => f.write_str("void"),
            TypeKind::Number => f.write_str("u64"), // FIXME
        }?;

        Ok(())
    }
}

impl Type {
    pub(crate) fn new(kind: &TypeKind, size: usize, origin: &Origin) -> Self {
        Self {
            kind: *kind,
            size,
            origin: *origin,
        }
    }

    pub(crate) fn merge(&self, other: &Type) -> Result<Type, Error> {
        match (self.kind, other.kind) {
            (TypeKind::Unknown, _) => Ok(*self),
            (_, TypeKind::Unknown) => Ok(*other),
            (TypeKind::Void, TypeKind::Void) => Ok(*self),
            (TypeKind::Number, TypeKind::Number) => {
                if self.size == other.size {
                    Ok(*self)
                } else {
                    Err(Error::new_incompatible_types(&self.origin, self, other))
                }
            }

            (TypeKind::Void, _) | (_, TypeKind::Void) => {
                Err(Error::new_incompatible_types(&self.origin, self, other))
            }
        }
    }

    pub(crate) fn u64() -> Self {
        Type::new(&TypeKind::Number, 8, &Origin::default())
    }

    pub(crate) fn void() -> Self {
        Type::new(&TypeKind::Void, 0, &Origin::default())
    }
}

pub struct Checker {
    //types: BTreeSet<Type>,
}

impl Checker {
    pub fn new() -> Self {
        Self {
            //types: Self::builtin(),
        }
    }

    //fn builtin() -> BTreeSet<Type> {
    //    let mut res = BTreeSet::<Type>::new();
    //
    //    res.insert(Type::u64());
    //    res.insert(Type::void());
    //
    //    res
    //}

    pub fn check(&mut self, nodes: &mut [Node]) -> Vec<Error> {
        let mut errs = Vec::new();

        let mut stack = Vec::new();

        for node in nodes {
            match node.kind {
                crate::ast::NodeKind::Number => {
                    assert_eq!(node.typ.kind, TypeKind::Number);
                    assert_ne!(node.typ.size, 0);

                    stack.push(node);
                }
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
