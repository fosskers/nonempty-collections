//! Extension of [`either::Either`] to provide support for [`NonEmptyIterator`].
use either::Either;

use crate::NonEmptyIterator;

/// Non-empty variant of [`either::Either`] that implements
/// [`NonEmptyIterator`].
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum NEEither<L, R> {
    /// A value of type `L`.
    Left(L),
    /// A value of type `R`.
    Right(R),
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
