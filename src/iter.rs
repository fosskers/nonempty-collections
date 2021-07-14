//! Non-empty iterators.

/// An [`Iterator`] that is guaranteed to have at least one item.
pub trait NonEmptyIterator {
    type Item;
    type Iter: Iterator;

    fn first(self) -> (Self::Item, Self::Iter);
}
