use serde::{Deserialize, Serialize};

use crate::origin::Origin;

#[derive(Serialize, Deserialize)]
pub enum ErrorKind {
    UnknownToken,
    InvalidLiteralNumber,
}

#[derive(Serialize, Deserialize)]
pub struct Error {
    pub kind: ErrorKind,
    pub origin: Origin,
}

impl Error {
    pub(crate) fn new(kind: ErrorKind, origin: Origin) -> Self {
        Self { kind, origin }
    }
}
