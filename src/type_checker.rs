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

#[derive(Serialize, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Size {
    _0,
    _8,
    _16,
    _32,
    _64,
}

#[derive(Serialize, Clone, PartialEq, Eq, Debug, PartialOrd, Ord)]
pub struct Type {
    pub kind: Box<TypeKind>,
    pub size: Size,
    pub origin: Origin,
}

impl Default for Type {
    fn default() -> Self {
        Self {
            kind: Box::new(TypeKind::Unknown),
            size: Size::_0,
            origin: Default::default(),
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
    pub(crate) fn new(kind: &TypeKind, size: &Size, origin: &Origin) -> Self {
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

    pub(crate) fn make_int() -> Self {
        Type::new(&TypeKind::Number, &Size::_64, &Origin::default())
    }

    pub(crate) fn make_bool() -> Self {
        Type::new(&TypeKind::Bool, &Size::_8, &Origin::default())
    }

    pub(crate) fn make_void() -> Self {
        Type::new(&TypeKind::Void, &Size::_0, &Origin::default())
    }

    pub(crate) fn make_function(return_type: &Type, args: &[Type], origin: &Origin) -> Self {
        Type::new(
            &TypeKind::Function(return_type.clone(), args.to_owned()),
            &Size::_64,
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
                    assert_ne!(node.typ.size, Size::_0);

                    stack.push(node);
                }
                crate::ast::NodeKind::Bool => {
                    assert_eq!(*node.typ.kind, TypeKind::Bool);
                    assert_eq!(node.typ.size, Size::_8);

                    stack.push(node);
                }
                crate::ast::NodeKind::BuiltinPrintln => {
                    match &*node.typ.kind {
                        TypeKind::Function(_, args) if args.len() == 1 => {}
                        _ => panic!("unexpected println type"),
                    };
                    assert_eq!(node.typ.size, Size::_8);

                    stack.push(node);
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
                    let f = stack.pop().unwrap();

                    let (ret_type, args_type) = match &*f.typ.kind {
                        TypeKind::Function(ret_type, args_type) => {
                            assert_eq!(args_type.len(), 1);
                            (ret_type, args_type)
                        }
                        _ => panic!("unexpected function type: {:#?}", node.typ),
                    };

                    if args_count != args_type.len() {
                        errs.push(Error::new_incompatible_arguments_count(
                            &node.origin,
                            args_type.len(),
                            args_count,
                        ));

                        continue;
                    }

                    for (i, arg) in args.iter().enumerate() {
                        let _typ = match arg.typ.merge(&args_type[i]) {
                            Err(err) => {
                                errs.push(err);
                                continue;
                            }
                            Ok(t) => t,
                        };
                    }

                    node.typ = f.typ.clone();

                    if *ret_type.kind != TypeKind::Void {
                        //stack.push(ret_type);
                        todo!();
                    }
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
                            node.typ = Type::make_int();
                        }
                    }
                    stack.push(node);
                }
            }
        }

        errs
    }
}

impl Size {
    pub(crate) fn as_bytes_count(&self) -> usize {
        match self {
            Size::_0 => 0,
            Size::_8 => 1,
            Size::_16 => 2,
            Size::_32 => 4,
            Size::_64 => 8,
        }
    }

    pub(crate) fn as_bits_count(&self) -> usize {
        match self {
            Size::_0 => 0,
            Size::_8 => 8,
            Size::_16 => 16,
            Size::_32 => 32,
            Size::_64 => 64,
        }
    }

    pub fn as_asm_addressing_str(&self) -> &'static str {
        match self {
            Size::_0 => panic!("invalid addressing size"),
            Size::_8 => "BYTE PTR",
            Size::_16 => "WORD PTR",
            Size::_32 => "DWORD PTR",
            Size::_64 => "QWORD PTR",
        }
    }
}
