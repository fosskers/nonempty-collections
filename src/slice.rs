//! Non-empty Slices.

use crate::iter::{IntoIteratorProxy, IntoNonEmptyIterator, NonEmptyIterator};
use std::iter::{Chain, Once, Skip};
use std::num::NonZeroUsize;

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
        self.head
    }

    /// Using `from_slice` gives a proof that the input slice is non-empty in
    /// the `Some` branch.
    pub fn from_slice(slice: &'a [T]) -> Option<Self> {
        slice.split_first().map(|(head, tail)| Self { head, tail })
    }

    /// Get the length of the slice.
    pub fn len(&self) -> NonZeroUsize {
        NonZeroUsize::MIN.saturating_add(self.tail.len())
    }

    /// No, this slice is not empty.
    #[deprecated(note = "A NESlice is never empty.")]
    pub const fn is_empty(&self) -> bool {
        false
    }

    /// Generates a standard iterator.
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            head: self.head,
            iter: std::iter::once(self.head).chain(self.tail.iter()),
        }
    }

    /// Returns a non-empty iterator over `chunk_size` elements of the `NESlice`
    /// at a time, starting at the beginning of the `NESlice`.
    ///
    /// ```
    /// use nonempty_collections::*;
    /// use std::num::NonZeroUsize;
    ///
    /// let v = nev![1,2,3,4,5,6];
    /// let s = v.as_nonempty_slice();
    /// let n = NonZeroUsize::new(2).unwrap();
    /// let r = s.nonempty_chunks(n).collect::<NEVec<_>>();
    ///
    /// let a = nev![1,2];
    /// let b = nev![3,4];
    /// let c = nev![5,6];
    ///
    /// assert_eq!(r, nev![a.as_nonempty_slice(), b.as_nonempty_slice(), c.as_nonempty_slice()]);
    /// ```
    pub fn nonempty_chunks(&'a self, chunk_size: NonZeroUsize) -> NEChunks<'a, T> {
        NEChunks {
            window: chunk_size,
            head: self.head,
            tail: self.tail,
            index: 0,
        }
    }
}

impl<'a, T> IntoNonEmptyIterator for NESlice<'a, T> {
    type Item = &'a T;

    type IntoIter = Iter<'a, T>;

    fn into_nonempty_iter(self) -> Self::IntoIter {
        Iter {
            head: self.head,
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

/// A non-empty Iterator of [`NESlice`] chunks.
pub struct NEChunks<'a, T> {
    pub(crate) window: NonZeroUsize,
    pub(crate) head: &'a T,
    pub(crate) tail: &'a [T],
    pub(crate) index: usize,
}

type SliceFilter<'a, T> = fn(&'a [T]) -> Option<NESlice<'a, T>>;

impl<'a, T> NonEmptyIterator for NEChunks<'a, T> {
    type Item = NESlice<'a, T>;
    type IntoIter = std::iter::FilterMap<std::slice::Chunks<'a, T>, SliceFilter<'a, T>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index == 0 {
            let end = (self.window.get() - 1).min(self.tail.len());

            let slice = NESlice {
                head: self.head,
                tail: &self.tail[0..end],
            };

            // 2024-03-18: This is a workaround for edge case of 1 element slice, thus the index
            // does not get incremented as end is 0, thus the next iteration will return the same
            // slice gain and again.
            self.index = end + 1;

            Some(slice)
        } else if self.index >= (self.tail.len() + 1) {
            None
        } else {
            // Ensure we never go out of bounds
            let end = (self.index - 1 + self.window.get()).min(self.tail.len());
            let slc: &'a [T] = &self.tail[self.index - 1..end];

            match slc {
                [] => None,
                [head, tail @ ..] => {
                    let slice = NESlice { head, tail };
                    self.index = end + 1;
                    Some(slice)
                }
            }
        }
    }

    fn first(self) -> (Self::Item, Self::IntoIter) {
        let end = (self.window.get() - 1).min(self.tail.len());

        let slice = NESlice {
            head: self.head,
            tail: &self.tail[0..end],
        };

        let tail: &'a [T] = &self.tail[end..];

        let rest = tail
            .chunks(self.window.get())
            .filter_map(NESlice::from_slice as SliceFilter<'a, T>);

        (slice, rest)
    }
}

impl<'a, T> IntoIterator for NEChunks<'a, T> {
    type Item = NESlice<'a, T>;

    type IntoIter = IntoIteratorProxy<NEChunks<'a, T>>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIteratorProxy { iter: self }
    }
}

#[cfg(test)]
mod tests {
    use std::num::NonZeroUsize;

    use crate::{nev, slice::NEChunks, NESlice, NEVec, NonEmptyIterator};

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
        if let Some(nonempty) = NESlice::from_slice(&slice) {
            for n in nonempty.iter() {
                assert_eq!(*n, *n); // Prove that we're dealing with references.
            }
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

    #[test]
    fn chunks() {
        let v = nev![1, 2, 3, 4, 5, 6, 7];

        let n = NonZeroUsize::new(3).unwrap();
        let a: Vec<_> = v.nonempty_chunks(n).collect();

        assert_eq!(
            a,
            vec![
                nev![1, 2, 3].as_nonempty_slice(),
                nev![4, 5, 6].as_nonempty_slice(),
                nev![7].as_nonempty_slice()
            ]
        );

        let n = NonZeroUsize::new(1).unwrap();
        let b: Vec<_> = v.nonempty_chunks(n).collect();

        assert_eq!(
            b,
            vec![
                nev![1].as_nonempty_slice(),
                nev![2].as_nonempty_slice(),
                nev![3].as_nonempty_slice(),
                nev![4].as_nonempty_slice(),
                nev![5].as_nonempty_slice(),
                nev![6].as_nonempty_slice(),
                nev![7].as_nonempty_slice(),
            ]
        );
    }

    #[test]
    fn chunks_len() {
        let v = nev![1, 2, 3];
        let n = NonZeroUsize::new(3).unwrap();
        let c = v.nonempty_chunks(n).count().get();
        assert_eq!(c, 1);

        let v = nev![1, 2, 3];
        let n = NonZeroUsize::new(5).unwrap();
        let c = v.nonempty_chunks(n).count().get();
        assert_eq!(c, 1);

        let v = nev![1, 2, 3, 4];
        let n = NonZeroUsize::new(3).unwrap();
        let c = v.nonempty_chunks(n).count().get();
        assert_eq!(c, 2);
    }

    // A test to reproduce index out of range errors
    // and ensure that the `NEChunks` iterator works
    // as expected.
    #[test]
    fn chunks_into_iter_with_chunk_size_over_len() {
        let v = nev![1, 2, 3];
        let n = NonZeroUsize::new(4).unwrap();
        let c = v.nonempty_chunks(n);

        // Iterating over should not produce any errors.
        for slice in c {
            let _: NESlice<'_, i32> = slice;
        }

        let v = nev![1, 2, 3];
        let n = NonZeroUsize::new(4).unwrap();
        let c: NEVec<_> = v.nonempty_chunks(n).collect();

        assert_eq!(1, c.len().get());
        assert_eq!(&v.as_nonempty_slice(), c.first());
    }

    // A test to ensure the correctness of the `NEChunks` iterator
    #[test]
    fn chunks_into_iter_should_return_elements_exactly_once() {
        let v = nev![1, 2, 3, 4, 5, 6, 57];
        let n = NonZeroUsize::new(3).unwrap();
        let c: NEChunks<'_, i32> = v.nonempty_chunks(n);

        let mut r: Vec<NESlice<i32>> = vec![];

        for slice in c {
            let _: NESlice<'_, i32> = slice;
            r.push(slice);
        }

        assert_eq!(
            r,
            vec![
                nev![1, 2, 3].as_nonempty_slice(),
                nev![4, 5, 6].as_nonempty_slice(),
                nev![57].as_nonempty_slice(),
            ]
        );
    }

    // This test cover an edge case non supported by the `chunks` method
    // when the slice has only one element.
    #[test]
    fn chunks_into_iter_edge_case_single_element() {
        let v = nev![1];
        let n = NonZeroUsize::new(3).unwrap();
        let c: NEChunks<'_, i32> = v.nonempty_chunks(n);

        let mut iter = c.into_iter();

        assert_eq!(1, iter.next().unwrap().len().get());
        assert!(iter.next().is_none());
    }
}
