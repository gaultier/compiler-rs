use std::{collections::BTreeSet, fmt::Display};

use serde::Serialize;

use crate::{error::Error, origin::Origin};

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
