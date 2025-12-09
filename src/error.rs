use std::{collections::HashMap, io::Write};

use serde::Serialize;

use crate::origin::{FileId, Origin};

#[derive(Serialize, Debug, PartialEq, Eq, Clone, Copy)]
pub enum ErrorKind {
    UnknownToken,
    InvalidLiteralNumber,
    ParseStatement,
    MissingNewline,
    ParseTermMissingRhs,
    ParseFactorMissingRhs,
}

#[derive(Serialize, Debug, Clone)]
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

    pub fn write<W: Write>(
        &self,
        w: &mut W,
        input: &str,
        file_id_to_names: &HashMap<FileId, String>,
    ) -> std::io::Result<()> {
        self.origin.write(w, file_id_to_names)?;

        w.write_all(b": Error: ")?;

        match self.kind {
            ErrorKind::UnknownToken => w.write_all(b"unknown token")?,
            ErrorKind::InvalidLiteralNumber => w.write_all(b"invalid number literal")?,
            ErrorKind::ParseStatement => w.write_all(b"invalid parse statement")?,
            ErrorKind::MissingNewline => w.write_all(b"missing newline")?,
            ErrorKind::ParseFactorMissingRhs => {
                w.write_all(b"missing right operand in + or - operation")?
            }
            ErrorKind::ParseTermMissingRhs => {
                w.write_all(b"missing right operand in * or / operation")?
            }
        };

        w.write_all(b": ")?;

        {
            let start = self.origin.offset as usize;
            let end = self.origin.offset as usize + self.origin.len as usize;

            // TODO: limit context length.
            let mut excerpt_start = start;
            while excerpt_start > 0 {
                excerpt_start -= 1;
                if input.as_bytes()[excerpt_start] == b'\n' {
                    excerpt_start += 1;
                    break;
                }
            }

            let mut excerpt_end = end;
            while excerpt_end < input.len() {
                excerpt_end += 1;
                if input.as_bytes()[excerpt_end] == b'\n' {
                    excerpt_end -= 1;
                    break;
                }
            }

            let excerpt_before = &input[excerpt_start..start].trim_ascii_start();
            let excerpt = &input[start..end];
            let excerpt_after = &input[end..excerpt_end].trim_ascii_end();

            w.write_all(excerpt_before.as_bytes())?;
            w.write_all(b"\x1B[4m")?;
            w.write_all(excerpt.as_bytes())?;
            w.write_all(b"\x1B[0m")?;
            w.write_all(excerpt_after.as_bytes())?;
        }

        if !self.explanation.is_empty() {
            w.write_all(self.explanation.as_bytes())?;
            w.write_all(b"\n")?;
        }
        w.write_all(b"\n")?;

        Ok(())
    }
}
