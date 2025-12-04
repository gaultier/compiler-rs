use miniserde::Serialize;

use crate::origin::Origin;

#[derive(Serialize, Debug, PartialEq, Eq)]
pub enum ErrorKind {
    UnknownToken,
    InvalidLiteralNumber,
    ParseStatement,
    MissingNewline,
    ParseFactorMissingRhs,
}

#[derive(Serialize)]
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
