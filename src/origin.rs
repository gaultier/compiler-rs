use std::{collections::HashMap, fmt::Display};

use serde::Serialize;

pub type FileId = u32;

#[derive(PartialEq, Eq, Debug, Serialize, Copy, Clone, PartialOrd, Ord)]
pub enum OriginKind {
    File(FileId),
    Builtin,
    SynthFromCodegen,
    Unknown, // Only used for the 'unknown' type.
}

#[derive(PartialEq, Eq, Debug, Serialize, Copy, Clone, PartialOrd, Ord)]
pub struct Origin {
    pub line: u32,
    pub column: u32,
    pub offset: u32,
    pub len: u32,
    pub kind: OriginKind,
}

pub struct OriginFormatter<'a> {
    origin: Origin,
    file_name: Option<&'a str>,
}

impl<'a> Display for OriginFormatter<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.origin.kind {
            OriginKind::File(_) => {
                let file_name: &str = self.file_name.unwrap();
                f.write_str(file_name)
            }
            OriginKind::Builtin => f.write_str("builtin"),
            OriginKind::SynthFromCodegen => f.write_str("synth_codegen"),
            OriginKind::Unknown => f.write_str("unknown"),
        }?;
        write!(
            f,
            ":{}:{}:{}",
            self.origin.line, self.origin.column, self.origin.offset
        )
    }
}

impl Origin {
    pub(crate) fn display<'a>(
        &self,
        file_id_to_name: &'a HashMap<FileId, String>,
    ) -> OriginFormatter<'a> {
        OriginFormatter {
            origin: *self,
            file_name: if let OriginKind::File(file_id) = self.kind {
                file_id_to_name.get(&file_id).map(|s| s.as_str())
            } else {
                None
            },
        }
    }

    pub(crate) fn new(line: u32, column: u32, offset: u32, len: u32, file_id: FileId) -> Self {
        Self {
            line,
            column,
            offset,
            len,
            kind: OriginKind::File(file_id),
        }
    }

    pub(crate) fn new_synth_codegen() -> Self {
        Origin {
            line: 0,
            column: 0,
            offset: 0,
            len: 0,
            kind: OriginKind::SynthFromCodegen,
        }
    }

    pub(crate) fn new_builtin() -> Self {
        Origin {
            line: 0,
            column: 0,
            offset: 0,
            len: 0,
            kind: OriginKind::Builtin,
        }
    }

    pub(crate) fn new_unknown() -> Self {
        Origin {
            line: 0,
            column: 0,
            offset: 0,
            len: 0,
            kind: OriginKind::Unknown,
        }
    }
}
