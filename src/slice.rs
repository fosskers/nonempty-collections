//! Non-empty Slices.

use crate::iter::{IntoNonEmptyIterator, NonEmptyIterator};
use std::{
    iter::{Chain, Once, Skip},
    num::NonZeroUsize,
};

/// A non-empty slice. Like [`crate::NEVec`], but guaranteed to have borrowed
/// contents.
///
/// [`NESlice::from_slice`] is the simplest way to construct this from borrowed data.
///
/// Unfortunately there is no macro for this, but if you want one, just use
/// `nev!` and handle the ownership manually. Also consider
/// [`crate::NEVec::as_nonempty_slice`].
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NESlice<'a, T> {
    /// The element of the non-empty slice. Always exists.
    pub head: &'a T,

    /// The remaining elements of the non-empty slice, perhaps empty.
    pub tail: &'a [T],
}

impl<'a, T> NESlice<'a, T> {
    /// Create a new non-empty slice with an initial element.
    pub fn new(head: &'a T, tail: &'a [T]) -> Self {
        Self { head, tail }
    }

    /// Get the first element. Never fails.
    pub const fn first(&self) -> &T {
        &self.head
    }

    /// Using `from_slice` gives a proof that the input slice is non-empty in
    /// the `Some` branch.
    pub fn from_slice(slice: &'a [T]) -> Option<Self> {
        slice.split_first().map(|(head, tail)| Self { head, tail })
    }

    /// Get the length of the slice.
    pub fn len(&self) -> NonZeroUsize {
        let len = self.tail.len();
        unsafe { NonZeroUsize::new_unchecked(len + 1) }
    }

    /// Generates a standard iterator.
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            head: &self.head,
            iter: std::iter::once(self.head).chain(self.tail.iter()),
        }
    }
}

impl<'a, T> IntoNonEmptyIterator for NESlice<'a, T> {
    type Item = &'a T;

    type IntoIter = Iter<'a, T>;

    fn into_nonempty_iter(self) -> Self::IntoIter {
        Iter {
            head: &self.head,
            iter: std::iter::once(self.head).chain(self.tail.iter()),
        }
    }
}

/// A non-empty iterator over the values of an [`NESlice`].
#[derive(Debug)]
pub struct Iter<'a, T: 'a> {
    head: &'a T,
    iter: Chain<Once<&'a T>, std::slice::Iter<'a, T>>,
}

impl<'a, T> NonEmptyIterator for Iter<'a, T> {
    type Item = &'a T;
    type IntoIter = Skip<Chain<Once<&'a T>, std::slice::Iter<'a, T>>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    fn first(self) -> (Self::Item, Self::IntoIter) {
        (self.head, self.iter.skip(1))
    }
}

impl<'a, T> IntoIterator for Iter<'a, T> {
    type Item = &'a T;

    type IntoIter = Chain<Once<&'a T>, std::slice::Iter<'a, T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter
    }
}

#[cfg(test)]
mod tests {
    use crate::NESlice;

    #[test]
    fn test_from_conversion() {
        let slice = [1, 2, 3, 4, 5];

        let nonempty_slice = NESlice::from_slice(&slice);

        let nonempty_slice = nonempty_slice.unwrap();
        assert_eq!(nonempty_slice.head, &1);
        assert_eq!(nonempty_slice.tail, &[2, 3, 4, 5]);
    }

    #[test]
    fn test_iter_syntax() {
        let slice = [0, 1, 2, 3];
        let nonempty = NESlice::from_slice(&slice);
        for n in &nonempty {
            assert_eq!(*n, *n); // Prove that we're dealing with references.
        }
    }
    #[test]
    fn test_into_nonempty_iter() {
        use crate::{IntoNonEmptyIterator, NonEmptyIterator};

        let slice = [0, 1, 2, 3];
        let nonempty = NESlice::new(&slice[0], &slice[1..]);
        for (i, n) in nonempty.into_nonempty_iter().enumerate() {
            assert_eq!(i as i32, *n);
        }
    }
}
