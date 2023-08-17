//! Non-empty Slices.
use crate::iter::{FromNonEmptyIterator, IntoNonEmptyIterator, NonEmptyIterator};
use std::iter::{Chain, Once, Skip};

/// Non-empty slice
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NESlice<'a, T> {
    /// The element of the non-empty Vector. Always exists.
    pub head: &'a T,

    /// The remaining elements of the non-empty Vector, perhaps empty.
    pub tail: &'a [T],
}

impl<'a, T> NESlice<'a, T> {
    /// Get the first element. Never fails.
    pub const fn first(&self) -> &T {
        &self.head
    }

    /// Using `from_slice` gives a proof that the input slice is non-empty in the Some
    /// branch
    pub fn from_slice(slice: &'a [T]) -> Option<Self> {
        slice.split_first().map(|(head, tail)| Self { head, tail })
    }

    /// Get the length of the slice.
    pub fn len(&self) -> usize {
        self.tail.len() + 1
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
}
