//! Non-empty Slices.

use core::fmt;
use std::iter::FilterMap;
use std::num::NonZeroUsize;
use std::ops::Index;
use std::slice::Chunks;

use crate::iter::IntoNonEmptyIterator;
use crate::iter::NonEmptyIterator;

/// A non-empty slice. Like [`crate::NEVec`], but guaranteed to have borrowed
/// contents.
///
/// [`NESlice::from_slice`] is the simplest way to construct this from borrowed
/// data.
///
/// Unfortunately there is no macro for this, but if you want one, just use
/// `nev!` and handle the ownership manually. Also consider
/// [`crate::NEVec::as_nonempty_slice`].
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NESlice<'a, T> {
    inner: &'a [T],
}

impl<'a, T> NESlice<'a, T> {
    /// Get the first element. Never fails.
    #[must_use]
    pub const fn first(&self) -> &T {
        &self.inner[0]
    }

    /// Using `from_slice` gives a proof that the input slice is non-empty in
    /// the `Some` branch.
    #[must_use]
    pub const fn from_slice(slice: &'a [T]) -> Option<Self> {
        if slice.is_empty() {
            None
        } else {
            Some(NESlice { inner: slice })
        }
    }

    #[must_use]
    pub(crate) const fn from_slice_unchecked(slice: &'a [T]) -> Self {
        NESlice { inner: slice }
    }

    /// Get the length of the slice.
    #[must_use]
    pub fn len(&self) -> NonZeroUsize {
        debug_assert!(!self.inner.is_empty());
        unsafe { NonZeroUsize::new_unchecked(self.inner.len()) }
    }

    /// No, this slice is not empty.
    #[deprecated(note = "A NESlice is never empty.")]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        false
    }

    /// Generates a standard iterator.
    #[must_use]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            iter: self.inner.iter(),
        }
    }

    /// Returns a non-empty iterator over `chunk_size` elements of the `NESlice`
    /// at a time, starting at the beginning of the `NESlice`.
    ///
    /// ```
    /// use std::num::NonZeroUsize;
    ///
    /// use nonempty_collections::*;
    ///
    /// let v = nev![1, 2, 3, 4, 5, 6];
    /// let s = v.as_nonempty_slice();
    /// let n = NonZeroUsize::new(2).unwrap();
    /// let r = s.nonempty_chunks(n).collect::<NEVec<_>>();
    ///
    /// let a = nev![1, 2];
    /// let b = nev![3, 4];
    /// let c = nev![5, 6];
    ///
    /// assert_eq!(
    ///     r,
    ///     nev![
    ///         a.as_nonempty_slice(),
    ///         b.as_nonempty_slice(),
    ///         c.as_nonempty_slice()
    ///     ]
    /// );
    /// ```
    #[must_use]
    pub fn nonempty_chunks(&'a self, chunk_size: NonZeroUsize) -> NEChunks<'a, T> {
        NEChunks {
            inner: self.inner.chunks(chunk_size.get()),
        }
    }
}

impl<'a, T> IntoIterator for NESlice<'a, T> {
    type Item = &'a T;

    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.iter()
    }
}

impl<'a, T> IntoNonEmptyIterator for NESlice<'a, T> {
    type IntoNEIter = Iter<'a, T>;

    fn into_nonempty_iter(self) -> Self::IntoNEIter {
        Iter {
            iter: self.inner.iter(),
        }
    }
}

impl<T> Index<usize> for NESlice<'_, T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        &self.inner[index]
    }
}

/// A non-empty iterator over the values of an [`NESlice`].
#[derive(Debug)]
pub struct Iter<'a, T: 'a> {
    iter: std::slice::Iter<'a, T>,
}

impl<T> NonEmptyIterator for Iter<'_, T> {}

impl<'a, T> IntoIterator for Iter<'a, T> {
    type Item = &'a T;

    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter
    }
}

/// A non-empty Iterator of [`NESlice`] chunks.
pub struct NEChunks<'a, T> {
    pub(crate) inner: Chunks<'a, T>,
}

type SliceFilter<'a, T> = fn(&'a [T]) -> Option<NESlice<'a, T>>;

impl<T> NonEmptyIterator for NEChunks<'_, T> {}

impl<'a, T> IntoIterator for NEChunks<'a, T> {
    type Item = NESlice<'a, T>;

    type IntoIter = FilterMap<Chunks<'a, T>, SliceFilter<'a, T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.filter_map(|x| NESlice::from_slice(x))
    }
}

impl<T: fmt::Debug> fmt::Debug for NEChunks<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use std::num::NonZeroUsize;

    use crate::nev;
    use crate::slice::NEChunks;
    use crate::NESlice;
    use crate::NEVec;
    use crate::NonEmptyIterator;

    #[test]
    fn test_from_conversion() {
        let slice = [1, 2, 3, 4, 5];
        let nonempty_slice = NESlice::from_slice(&slice);
        let nonempty_slice = nonempty_slice.unwrap();

        assert_eq!(nonempty_slice.inner, &[1, 2, 3, 4, 5]);
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
        use crate::IntoNonEmptyIterator;
        use crate::NonEmptyIterator;
        let slice = [0usize, 1, 2, 3];
        let nonempty = NESlice::from_slice(&slice).unwrap();
        for (i, n) in nonempty.into_nonempty_iter().enumerate() {
            assert_eq!(i, *n);
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

    // This test covers an edge case non supported by the `chunks` method
    // when the slice has only one element.
    #[test]
    fn chunks_into_iter_edge_case_single_element() {
        let v = nev![1];
        let n = NonZeroUsize::new(3).unwrap();
        let c: NEChunks<'_, i32> = v.nonempty_chunks(n);

        let mut iter = c.into_iter();

        let next = iter.next().unwrap();
        println!("{next:?}");

        assert_eq!(1, next.len().get());
        assert!(iter.next().is_none());
    }
}
