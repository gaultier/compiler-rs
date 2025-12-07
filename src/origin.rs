use std::{collections::HashMap, io::Write};

use serde::Serialize;

pub type FileId = u32;

#[derive(PartialEq, Eq, Debug, Serialize, Copy, Clone)]
pub struct Origin {
    pub line: u32,
    pub column: u32,
    pub offset: u32,
    pub len: u32,
    pub file_id: FileId,
}

impl Origin {
    pub(crate) fn new(line: u32, column: u32, offset: u32, len: u32, file_id: FileId) -> Self {
        Self {
            line,
            column,
            offset,
            len,
            file_id,
        }
    }

    pub fn write<W: Write>(
        &self,
        w: &mut W,
        file_id_to_names: &HashMap<FileId, String>,
    ) -> std::io::Result<()> {
        // TODO: file name.
        let file_name = &file_id_to_names[&self.file_id];
        write!(
            w,
            "{}:{}:{}:{}",
            file_name, self.line, self.column, self.offset
        )?;

        Ok(())
    }
}
