//! Extension of [`either::Either`] to provide support for [`NonEmptyIterator`].
//!
//! ```
//! use nonempty_collections::*;
//! fn get_data(input: usize) -> NEEither<[usize; 1], [usize; 3]> {
//!     if input == 0 {
//!         NEEither::Left([0])
//!     } else {
//!         NEEither::Right([2, 1, 4])
//!     }
//! }
//!
//! assert_eq!(
//!     nev![0],
//!     get_data(0).into_nonempty_iter().collect::<NEVec<_>>()
//! );
//! ```

// Implementation note:
// In an ideal world there is no need for `NEEither` and we could just implement
// `NonEmptyIterator` for `Either`. However, the following holds:
//  - `NonEmptyIterator` requires an implementation of `IntoIterator`
//  - `Either` conditionally implements `Iterator`
//  - Rust has blanket implementation `impl<I: Iterator> IntoIterator for I`
// Therefore we cannot implement (`Into`)`NonEmptyIterator` for `Either<L, R>`
// except if we add bounds similar to `L: NonEmptyIterator + Iterator` and `R:
// NonEmptyIterator + Iterator`, which our implementations of `NonEmptyIterator`
// don't satisfy as that would break encapsulation.

use either::Either;

use crate::IntoNonEmptyIterator;
use crate::NonEmptyIterator;

#[cfg(feature = "schemars")]
use ::{
    schemars::{JsonSchema, Schema, SchemaGenerator},
    std::borrow::Cow,
};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// Non-empty variant of [`either::Either`] that implements
/// [`NonEmptyIterator`].
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum NEEither<L, R> {
    /// A value of type `L`.
    Left(L),
    /// A value of type `R`.
    Right(R),
}

impl<L, R> NEEither<L, R> {
    /// Convert the inner value to a `NonEmptyIterator`.
    ///
    /// This requires the `Left` and `Right` non-empty iterators to have the
    /// same item type.
    ///
    /// ```
    /// use nonempty_collections::*;
    /// let left: NEEither<_, NESet<usize>> = NEEither::Left(nev![1, 2, 3]);
    /// let right: NEEither<NEVec<usize>, _> = NEEither::Right(nes![4]);
    ///
    /// let combined = left.into_nonempty_iter().chain(right).collect::<NEVec<_>>();
    /// let expected = nev![1, 2, 3, 4];
    /// assert_eq!(expected, combined);
    /// ```
    pub fn into_nonempty_iter(self) -> NEEither<L::IntoNEIter, R::IntoNEIter>
    where
        L: IntoNonEmptyIterator,
        R: IntoNonEmptyIterator<Item = L::Item>,
    {
        match self {
            NEEither::Left(left) => NEEither::Left(left.into_nonempty_iter()),
            NEEither::Right(right) => NEEither::Right(right.into_nonempty_iter()),
        }
    }
}

impl<L, R> NonEmptyIterator for NEEither<L, R>
where
    L: NonEmptyIterator + IntoIterator,
    R: NonEmptyIterator + IntoIterator<Item = L::Item>,
{
}

impl<L, R> IntoIterator for NEEither<L, R>
where
    L: IntoIterator,
    R: IntoIterator<Item = L::Item>,
{
    type Item = L::Item;

    type IntoIter = Either<L::IntoIter, R::IntoIter>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            NEEither::Left(left) => Either::Left(left.into_iter()),
            NEEither::Right(right) => Either::Right(right.into_iter()),
        }
    }
}

#[cfg(feature = "schemars")]
impl<L: JsonSchema, R: JsonSchema> JsonSchema for NEEither<L, R> {
    fn schema_name() -> Cow<'static, str> {
        Either::<L, R>::schema_name()
    }

    fn json_schema(generator: &mut SchemaGenerator) -> Schema {
        Either::<L, R>::json_schema(generator)
    }

    fn inline_schema() -> bool {
        Either::<L, R>::inline_schema()
    }
}

#[cfg(all(test, feature = "serde"))]
mod serde_tests {
    use super::{Either, NEEither};

    #[test]
    fn json() {
        let ne_either: NEEither<i32, f32> = NEEither::Left(123);
        let ne_either_json = serde_json::to_string(&ne_either).unwrap();
        let either: Either<i32, f32> = serde_json::from_str(&ne_either_json).unwrap();
        let either_json = serde_json::to_string(&either).unwrap();

        assert_eq!(&ne_either_json, &either_json);

        let ne_either_2: NEEither<i32, f32> = serde_json::from_str(&either_json).unwrap();

        assert_eq!(&ne_either, &ne_either_2);
    }
}
