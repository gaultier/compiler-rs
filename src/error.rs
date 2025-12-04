use miniserde::{Deserialize, Serialize};

use crate::origin::Origin;

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
pub enum ErrorKind {
    UnknownToken,
    InvalidLiteralNumber,
    ParseStatement,
    MissingNewline,
}

#[derive(Serialize, Deserialize)]
pub struct Error {
    pub kind: ErrorKind,
    pub origin: Origin,
    pub explanation: String,
}

impl Error {
    pub(crate) fn new(kind: ErrorKind, origin: Origin, explanation: String) -> Self {
        Self {
            kind,
            origin,
            explanation,
        }
    }
}
