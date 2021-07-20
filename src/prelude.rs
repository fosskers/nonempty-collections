//! This prelude re-exports the various traits from this crate.
//!
//! Intended to be imported as:
//!
//! ```
//! use nonempty_collections::prelude::*;
//! ```

pub use crate::iter::FromNonEmptyIterator;
pub use crate::iter::IntoNonEmptyIterator;
pub use crate::iter::NonEmptyIterator;
pub use crate::{nem, nes, nev};
