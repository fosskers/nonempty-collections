//! Non-empty variants of the standard collections.
//!
//! Non-emptiness can be a powerful guarantee. If your main use of `Vec` is as
//! an `Iterator`, then you may not need to distinguish on emptiness. But there
//! are indeed times when the `Vec` you receive as a function argument needs to
//! be non-empty or your function can't proceed. Similarly, there are times when
//! the `Vec` you return to a calling user needs to promise it actually contains
//! something.
//!
//! With `NEVec`, you're freed from the boilerplate of constantly needing to
//! check `is_empty()` or pattern matching before proceeding, or erroring if you
//! can't. So overall, code, type signatures, and logic become cleaner.
//!
//! Consider that unlike `Vec`, [`NEVec::first`] and [`NEVec::last`] don't
//! return in `Option`; they always succeed.
//!
//! Alongside [`NEVec`] are its cousins [`NEMap`] and [`NESet`]; Hash Maps and
//! Hash Sets which are guaranteed to contain at least one item.
//!
//! # Examples
//!
//! The simplest way to construct these non-empty collections is via their
//! macros: [`nev`], [`nes`], and [`nem`]:
//!
//! ```
//! use nonempty_collections::*;
//!
//! let v: NEVec<u32> = nev![1, 2, 3];
//! let s: NESet<u32> = nes![1, 2, 2, 3]; // 1 2 3
//! let m: NEMap<&str, bool> = nem!["a" => true, "b" => false];
//! assert_eq!(1, v.head);
//! assert_eq!(3, s.len());
//! assert!(m.get("a").unwrap());
//! ```
//!
//! Unlike the familiar `vec!` macro, `nev!` and friends require at least one
//! element:
//!
//! ```
//! use nonempty_collections::nev;
//!
//! let v = nev![1];
//!
//! // Doesn't compile!
//! // let v = nev![];
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
//! # Iterators
//!
//! This library extends the notion of non-emptiness to Iterators, and provides
//! the [`NonEmptyIterator`] trait. This has some interesting consequences:
//!
//! - Functions like `map` preserve non-emptiness.
//! - Functions like `max` always have a result.
//! - A non-empty Iterator chain can be `collect`ed back into a non-empty structure.
//! - You can chain many operations together without having to double-check for emptiness.
//!
//! ```
//! use nonempty_collections::*;
//!
//! let v: NEVec<_> = nev![1, 2, 3].into_nonempty_iter().map(|n| n + 1).collect();
//! assert_eq!(2, v.head);
//! ```
//!
//! # Caveats
//!
//! Since `NEVec`, `NEMap`, and `NESet` must have a least one element, it is not
//! possible to implement the [`FromIterator`] trait for them. We can't know, in
//! general, if any given standard-library [`Iterator`] actually contains
//! something.
//!
//! # Features
//!
//! * `serde`: `serde` support.

#![warn(missing_docs)]

pub mod iter;
pub mod map;
pub mod set;
pub mod slice;
pub mod vector;

pub use iter::FromNonEmptyIterator;
pub use iter::IntoNonEmptyIterator;
pub use iter::NonEmptyIterator;
pub use map::NEMap;
pub use set::NESet;
pub use slice::NESlice;
pub use vector::NEVec;
