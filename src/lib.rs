//! Non-empty variants of the standard collections.
//!
//! Non-emptiness can be a powerful guarantee. If your main use of `Vec` is as
//! an `Iterator`, then you may not need to distinguish on emptiness. But there
//! are indeed times when the `Vec` you receive as as function argument needs to
//! be non-empty or your function can't proceed. Similarly, there are times when
//! the `Vec` you return to a calling user needs to promise it actually contains
//! something.
//!
//! With `NEVec`, you're freed from the boilerplate of constantly needing to
//! check `is_empty()` or pattern matching before proceeding, or erroring if you
//! can't. So overall, code, type signatures, and logic become cleaner.
//!
//! Consider that unlike `Vec`, [`NEVec::first`] and [`NEVec::last`] don't
//! return in `Option`, they always succeed.
//!
//! # Examples
//!
//! The simplest way to construct a [`NEVec`] is via the [`nev`] macro:
//!
//! ```
//! use nonempty_collections::{NEVec, nev};
//!
//! let l: NEVec<u32> = nev![1, 2, 3];
//! assert_eq!(l.head, 1);
//! ```
//!
//! Unlike the familiar `vec!` macro, `nev!` requires at least one element:
//!
//! ```
//! use nonempty_collections::nev;
//!
//! let l = nev![1];
//!
//! // Doesn't compile!
//! // let l = nev![];
//! ```
//!
//! Like `Vec`, you can also construct a [`NEVec`] the old fashioned way with
//! [`NEVec::new`] or its constructor:
//!
//! ```
//! use nonempty_collections::NEVec;
//!
//! let mut l = NEVec { head: 42, tail: vec![36, 58] };
//! assert_eq!(l.head, 42);
//!
//! l.push(9001);
//! assert_eq!(l.last(), &9001);
//! ```
//!
//! And if necessary, you're free to convert to and from `Vec`:
//!
//! ```
//! use nonempty_collections::{NEVec, nev};
//!
//! let l: NEVec<u32> = nev![42, 36, 58, 9001];
//! let v: Vec<u32> = l.into();
//! assert_eq!(v, vec![42, 36, 58, 9001]);
//!
//! let u: Option<NEVec<u32>> = NEVec::from_vec(v);
//! assert_eq!(Some(nev![42, 36, 58, 9001]), u);
//! ```
//!
//! # Caveats
//!
//! Since `NEVec` must have a least one element, it is not possible to
//! implement the `FromInterator` trait for it. We can't know, in general, if
//! any given `Iterator` actually contains something.
//!
//! # Features
//!
//! * `serde`: `serde` support.

#![warn(missing_docs)]

pub mod iter;
mod map;
mod set;
mod vector;

pub use map::NEMap;
pub use set::NESet;
pub use vector::NEVec;
