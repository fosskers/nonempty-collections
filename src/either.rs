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

use crate::IntoNonEmptyIterator;
use crate::NonEmptyIterator;
use either::Either;

/// Non-empty variant of [`either::Either`] that implements
/// [`NonEmptyIterator`].
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
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
