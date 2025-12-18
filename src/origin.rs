use std::{collections::HashMap, io::Write};

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

impl Origin {
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

    pub fn write<W: Write>(
        &self,
        w: &mut W,
        file_id_to_names: &HashMap<FileId, String>,
    ) -> std::io::Result<()> {
        self.kind.write(w, file_id_to_names)?;
        write!(w, ":{}:{}:{}", self.line, self.column, self.offset)?;

        Ok(())
    }
}

impl OriginKind {
    pub fn write<W: Write>(
        &self,
        w: &mut W,
        file_id_to_names: &HashMap<FileId, String>,
    ) -> std::io::Result<()> {
        match self {
            OriginKind::File(file_id) => {
                // TODO: file name.
                let file_name: &str = file_id_to_names
                    .get(&file_id)
                    .map(|s| s.as_str())
                    .unwrap_or_else(|| "<?>");
                w.write_all(file_name.as_bytes())
            }
            OriginKind::Builtin => w.write_all(b"builtin"),
            OriginKind::SynthFromCodegen => w.write_all(b"synth_codegen"),
            OriginKind::Unknown => w.write_all(b"unknown"),
        }
    }
}
