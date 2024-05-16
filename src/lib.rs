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
//! Alongside [`NEVec`] are its cousins [`NESlice`], [`NEMap`], and [`NESet`],
//! which are all guaranteed to contain at least one item.
//!
//! # Examples
//!
//! The simplest way to construct these non-empty collections is via their
//! macros: [`nev!`], [`nes!`], and [`nem!`]:
//!
//! ```
//! use nonempty_collections::*;
//!
//! let v: NEVec<u32> = nev![1, 2, 3];
//! let s: NESet<u32> = nes![1, 2, 2, 3]; // 1 2 3
//! let m: NEMap<&str, bool> = nem!["a" => true, "b" => false];
//! assert_eq!(&1, v.first());
//! assert_eq!(3, s.len().get());
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
//! ```
//!
//! A value must be provided:
//!
//! ```compile_fail
//! let v = nev![]; // Doesn't compile!
//! ```
//!
//! Like `Vec`, you can also construct a [`NEVec`] the old fashioned way with
//! [`NEVec::new`] or its constructor:
//!
//! ```
//! use nonempty_collections::NEVec;
//!
//! let mut l = NEVec::from_vec(vec![42, 36, 58]).unwrap();
//! assert_eq!(&42, l.first());
//!
//! l.push(9001);
//! assert_eq!(l.last(), &9001);
//! ```
//!
//! And if necessary, you're free to convert to and from `Vec`:
//!
//! ```
//! use nonempty_collections::nev;
//! use nonempty_collections::NEVec;
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
//! - A non-empty Iterator chain can be `collect`ed back into a non-empty
//!   structure.
//! - You can chain many operations together without having to double-check for
//!   emptiness.
//!
//! ```
//! use nonempty_collections::*;
//!
//! let v: NEVec<_> = nev![1, 2, 3].into_nonempty_iter().map(|n| n + 1).collect();
//! assert_eq!(&2, v.first());
//! ```
//!
//! Consider also [`IteratorExt::to_nonempty_iter`] for converting any given
//! [`Iterator`] into a non-empty one, if it contains at least one item.
//!
//! # Arrays
//!
//! Since fixed-size arrays are by definition already not empty, they aren't
//! given a special wrapper type like [`crate::NEVec`]. Instead, we enable them
//! to be easily iterated over in a compatible way:
//!
//! ```
//! use nonempty_collections::*;
//!
//! let a: [u32; 4] = [1, 2, 3, 4];
//! let v: NEVec<_> = a.into_nonempty_iter().map(|n| n + 1).collect();
//! assert_eq!(nev![2, 3, 4, 5], v);
//! ```
//! See [`NonEmptyArrayExt`] for more conversions.
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
//! * `indexmap`: support for non-empty [`IndexMap`](https://docs.rs/indexmap/latest/indexmap/)

pub mod array;
#[cfg(feature = "either")]
pub mod either;
#[cfg(feature = "indexmap")]
pub mod index_map;
pub mod iter;
#[cfg(feature = "itertools")]
pub mod itertools;
pub mod map;
pub mod set;
pub mod slice;
pub mod vector;

pub use array::ArrayNonEmptyIterator;
pub use array::NonEmptyArrayExt;
#[cfg(feature = "either")]
pub use either::NEEither;
#[cfg(feature = "indexmap")]
pub use index_map::NEIndexMap;
pub use iter::FromNonEmptyIterator;
pub use iter::IntoIteratorExt;
pub use iter::IntoNonEmptyIterator;
pub use iter::IteratorExt;
pub use iter::NonEmptyIterator;
#[cfg(feature = "itertools")]
pub use itertools::NonEmptyItertools;
pub use map::NEMap;
pub use set::NESet;
pub use slice::NESlice;
pub use vector::NEVec;

pub use nem as ne_hashmap;
pub use nes as ne_hashset;
pub use nev as ne_vec;
