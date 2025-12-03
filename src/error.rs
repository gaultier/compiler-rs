use crate::origin::Origin;

pub enum ErrorKind {
    UnknownToken,
    InvalidLiteralNumber,
}
pub struct Error {
    pub kind: ErrorKind,
    pub origin: Origin,
}

impl Error {
    pub(crate) fn new(kind: ErrorKind, origin: Origin) -> Self {
        Self { kind, origin }
    }
}
