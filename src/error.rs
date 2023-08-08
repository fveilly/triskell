use std::error::Error;
use std::fmt::{Display, Formatter, Result};

#[derive(Debug, PartialEq)]
pub enum TriskellError {
    NotEnoughMemory,
}

impl Display for TriskellError {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            TriskellError::NotEnoughMemory => write!(f, "Not enough memory available"),
        }
    }
}

impl Error for TriskellError {}