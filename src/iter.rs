//! Non-empty iterators.

/// An [`Iterator`] that is guaranteed to have at least one item.
pub trait NonEmptyIterator: Iterator {
    /// The first element of the `Iterator`.
    ///
    /// **Invariant:** This method is expected to advance the `Iterator`!
    fn initial(&mut self) -> Self::Item;
}
