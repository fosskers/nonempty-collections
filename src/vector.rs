//! Non-empty Vectors.

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::iter::{FromNonEmptyIterator, IntoNonEmptyIterator, NonEmptyIterator};
use crate::slice::NEChunks;
use std::cmp::Ordering;
use std::num::NonZeroUsize;

/// Like the [`vec!`] macro, but enforces at least one argument. A nice short-hand
/// for constructing [`NEVec`] values.
///
/// ```
/// use nonempty_collections::{NEVec, nev};
///
/// let v = nev![1, 2, 3];
/// assert_eq!(v.into_iter().collect::<Vec<_>>(), vec![1,2,3]);
///
/// let v = nev![1];
/// assert_eq!(v.into_iter().collect::<Vec<_>>(), vec![1]);
///
/// // Doesn't compile!
/// // let v = nev![];
/// ```
///
/// Consider also [`crate::nem!`] and [`crate::nes!`].
#[macro_export]
macro_rules! nev {
    ($h:expr, $( $x:expr ),*) => {{
        let mut v = $crate::NEVec::new($h);
        $( v.push($x); )*
        v
    }};
    ($h:expr) => {
        $crate::NEVec::new($h)
    }
}

/// A non-empty, growable Vector.
///
/// The first element can always be accessed in constant time. Similarly,
/// certain functions like [`NEVec::first`] and [`NEVec::last`] always succeed:
///
/// ```
/// use nonempty_collections::nev;
///
/// let s = nev!["Fëanor", "Fingolfin", "Finarfin"];
/// assert_eq!(&"Fëanor", s.first());      // There is always a first element.
/// assert_eq!(&"Finarfin", s.last()); // There is always a last element.
/// ```
#[cfg_attr(
    feature = "serde",
    derive(Deserialize, Serialize),
    serde(bound(serialize = "T: Clone + Serialize")),
    serde(into = "Vec<T>", try_from = "Vec<T>")
)]
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NEVec<T> {
    inner: Vec<T>,
}

impl<T> NEVec<T> {
    /// Create a new non-empty list with an initial element.
    pub fn new(head: T) -> Self {
        NEVec { inner: vec![head] }
    }

    /// Creates a new `NEVec` with a single element and specified capacity.
    pub fn with_capacity(capacity: usize, head: T) -> Self {
        let mut inner = Vec::with_capacity(capacity);
        inner.push(head);
        NEVec { inner }
    }

    /// Get the first element. Never fails.
    pub fn first(&self) -> &T {
        unsafe { self.inner.get_unchecked(0) }
    }

    /// Get the mutable reference to the first element. Never fails.
    ///
    /// # Examples
    ///
    /// ```
    /// use nonempty_collections::nev;
    ///
    /// let mut v = nev![42];
    /// let head = v.first_mut();
    /// *head += 1;
    /// assert_eq!(v.first(), &43);
    ///
    /// let mut v = nev![1, 4, 2, 3];
    /// let head = v.first_mut();
    /// *head *= 42;
    /// assert_eq!(v.first(), &42);
    /// ```
    pub fn first_mut(&mut self) -> &mut T {
        unsafe { self.inner.get_unchecked_mut(0) }
    }

    /// Push an element to the end of the list.
    pub fn push(&mut self, e: T) {
        self.inner.push(e)
    }

    /// Pop an element from the end of the list. Is a no-op when [`len()`] is 1.
    ///
    /// ```
    /// use nonempty_collections::nev;
    ///
    /// let mut v = nev![1, 2];
    /// assert_eq!(Some(2), v.pop());
    /// assert_eq!(None, v.pop());
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        if self.len() > NonZeroUsize::MIN {
            self.inner.pop()
        } else {
            None
        }
    }

    /// Inserts an element at position index within the vector, shifting all
    /// elements after it to the right.
    ///
    /// # Panics
    ///
    /// Panics if index > len.
    ///
    /// # Examples
    ///
    /// ```
    /// use nonempty_collections::nev;
    ///
    /// let mut v = nev![1, 2, 3];
    /// v.insert(1, 4);
    /// assert_eq!(v, nev![1, 4, 2, 3]);
    /// v.insert(4, 5);
    /// assert_eq!(v, nev![1, 4, 2, 3, 5]);
    /// v.insert(0, 42);
    /// assert_eq!(v, nev![42, 1, 4, 2, 3, 5]);
    /// ```
    pub fn insert(&mut self, index: usize, element: T) {
        self.inner.insert(index, element);
    }

    /// Get the length of the list.
    pub fn len(&self) -> NonZeroUsize {
        unsafe { NonZeroUsize::new_unchecked(self.inner.len()) }
    }

    /// A `NEVec` is never empty.
    #[deprecated(since = "0.1.0", note = "A NEVec is never empty.")]
    pub const fn is_empty(&self) -> bool {
        false
    }

    /// Get the capacity of the list.
    pub fn capacity(&self) -> usize {
        self.inner.capacity() + 1
    }

    /// Get the last element. Never fails.
    pub fn last(&self) -> &T {
        self.inner.last().unwrap()
    }

    /// Get the last element mutably.
    pub fn last_mut(&mut self) -> &mut T {
        self.inner.last_mut().unwrap()
    }

    /// Check whether an element is contained in the list.
    ///
    /// ```
    /// use nonempty_collections::nev;
    ///
    /// let mut l = nev![42, 36, 58];
    ///
    /// assert!(l.contains(&42));
    /// assert!(!l.contains(&101));
    /// ```
    pub fn contains(&self, x: &T) -> bool
    where
        T: PartialEq,
    {
        self.inner.contains(x)
    }

    /// Get an element by index.
    pub fn get(&self, index: usize) -> Option<&T> {
        self.inner.get(index)
    }

    /// Get an element by index, mutably.
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.inner.get_mut(index)
    }

    /// Truncate the list to a certain size.
    pub fn truncate(&mut self, len: NonZeroUsize) {
        self.inner.truncate(len.get());
    }

    /// ```
    /// use nonempty_collections::*;
    ///
    /// let mut l = nev![42, 36, 58];
    ///
    /// let mut iter = l.iter();
    /// let (first, mut rest_iter) = iter.next();
    ///
    /// assert_eq!(first, &42);
    /// assert_eq!(rest_iter.next(), Some(&36));
    /// assert_eq!(rest_iter.next(), Some(&58));
    /// assert_eq!(rest_iter.next(), None);
    /// ```
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            iter: self.inner.iter(),
        }
    }

    /// ```
    /// use nonempty_collections::*;
    ///
    /// let mut l = nev![42, 36, 58];
    ///
    /// for i in l.iter_mut().into_iter() {
    ///     *i *= 10;
    /// }
    ///
    /// let mut iter = l.iter();
    /// let (first, mut rest_iter) = iter.next();
    ///
    /// assert_eq!(first, &420);
    /// assert_eq!(rest_iter.next(), Some(&360));
    /// assert_eq!(rest_iter.next(), Some(&580));
    /// assert_eq!(rest_iter.next(), None);
    /// ```
    ///
    /// # Panics
    ///
    /// If you manually advance this iterator and then call
    /// [`NonEmptyIterator::first`], then you're in for a surprise.
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut {
            inner: self.inner.iter_mut(),
        }
    }

    /// Creates a new non-empty vec by cloning the elments from the slice if it
    /// is non-empty, returns `None` otherwise.
    ///
    /// Often we have a `Vec` (or slice `&[T]`) but want to ensure that it is
    /// `NEVec` before proceeding with a computation. Using `from_slice` will
    /// give us a proof that we have a `NEVec` in the `Some` branch, otherwise
    /// it allows the caller to handle the `None` case.
    ///
    /// # Example use
    ///
    /// ```
    /// use nonempty_collections::{nev, NEVec};
    ///
    /// let v_vec = NEVec::from_slice(&[1, 2, 3, 4, 5]);
    /// assert_eq!(v_vec, Some(nev![1, 2, 3, 4, 5]));
    ///
    /// let empty_vec: Option<NEVec<&u32>> = NEVec::from_slice(&[]);
    /// assert!(empty_vec.is_none());
    /// ```
    pub fn from_slice(slice: &[T]) -> Option<NEVec<T>>
    where
        T: Clone,
    {
        if slice.is_empty() {
            None
        } else {
            Some(NEVec {
                inner: slice.to_vec(),
            })
        }
    }

    /// Often we have a `Vec` (or slice `&[T]`) but want to ensure that it is
    /// `NEVec` before proceeding with a computation. Using `from_vec` will give
    /// us a proof that we have a `NEVec` in the `Some` branch, otherwise it
    /// allows the caller to handle the `None` case.
    ///
    /// This version will consume the `Vec` you pass in. If you would rather
    /// pass the data as a slice then use `NEVec::from_slice`.
    ///
    /// # Example Use
    ///
    /// ```
    /// use nonempty_collections::{nev, NEVec};
    ///
    /// let v_vec = NEVec::from_vec(vec![1, 2, 3, 4, 5]);
    /// assert_eq!(v_vec, Some(nev![1, 2, 3, 4, 5]));
    ///
    /// let empty_vec: Option<NEVec<&u32>> = NEVec::from_vec(vec![]);
    /// assert!(empty_vec.is_none());
    /// ```
    pub fn from_vec(vec: Vec<T>) -> Option<NEVec<T>> {
        if vec.is_empty() {
            None
        } else {
            Some(NEVec { inner: vec })
        }
    }

    /// Deconstruct a `NEVec` into its head and tail. This operation never fails
    /// since we are guaranteed to have a head element.
    ///
    /// # Example Use
    ///
    /// ```
    /// use nonempty_collections::nev;
    ///
    /// let mut v = nev![1, 2, 3, 4, 5];
    ///
    /// // Guaranteed to have the head and we also get the tail.
    /// assert_eq!(v.split_first(), (&1, &[2, 3, 4, 5][..]));
    ///
    /// let v = nev![1];
    ///
    /// // Guaranteed to have the head element.
    /// assert_eq!(v.split_first(), (&1, &[][..]));
    /// ```
    pub fn split_first(&self) -> (&T, &[T]) {
        self.inner.split_first().unwrap()
    }

    /// Deconstruct a `NEVec` into its first, last, and
    /// middle elements, in that order.
    ///
    /// If there is only one element then first == last.
    ///
    /// # Example Use
    ///
    /// ```
    /// use nonempty_collections::nev;
    ///
    /// let mut v = nev![1, 2, 3, 4, 5];
    ///
    /// // Guaranteed to have the last element and the elements
    /// // preceding it.
    /// assert_eq!(v.split(), (&1, &[2, 3, 4][..], &5));
    ///
    /// let v = nev![1];
    ///
    /// // Guaranteed to have the last element.
    /// assert_eq!(v.split(), (&1, &[][..], &1));
    /// ```
    pub fn split(&self) -> (&T, &[T], &T) {
        let (first, rest) = self.split_first();
        if let Some((last, middle)) = rest.split_last() {
            (first, middle, last)
        } else {
            (first, &[], first)
        }
    }

    /// Append a `Vec` to the tail of the `NEVec`.
    ///
    /// # Example Use
    ///
    /// ```
    /// use nonempty_collections::nev;
    ///
    /// let mut v = nev![1];
    /// let mut vec = vec![2, 3, 4, 5];
    /// v.append(&mut vec);
    ///
    /// let mut expected = nev![1, 2, 3, 4, 5];
    /// assert_eq!(v, expected);
    /// ```
    pub fn append(&mut self, other: &mut Vec<T>) {
        self.inner.append(other)
    }

    /// Binary searches this sorted non-empty vector for a given element.
    ///
    /// If the value is found then `Result::Ok` is returned, containing the
    /// index of the matching element. If there are multiple matches, then any
    /// one of the matches could be returned.
    ///
    /// If the value is not found then `Result::Err` is returned, containing the
    /// index where a matching element could be inserted while maintaining
    /// sorted order.
    ///
    /// # Examples
    ///
    /// ```
    /// use nonempty_collections::nev;
    ///
    /// let v = nev![0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55];
    /// assert_eq!(v.binary_search(&0),   Ok(0));
    /// assert_eq!(v.binary_search(&13),  Ok(9));
    /// assert_eq!(v.binary_search(&4),   Err(7));
    /// assert_eq!(v.binary_search(&100), Err(13));
    /// let r = v.binary_search(&1);
    /// assert!(match r { Ok(1..=4) => true, _ => false, });
    /// ```
    ///
    /// If you want to insert an item to a sorted non-empty vector, while
    /// maintaining sort order:
    ///
    /// ```
    /// use nonempty_collections::nev;
    ///
    /// let mut v = nev![0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55];
    /// let num = 42;
    /// let idx = v.binary_search(&num).unwrap_or_else(|x| x);
    /// v.insert(idx, num);
    /// assert_eq!(v, nev![0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 42, 55]);
    /// ```
    pub fn binary_search(&self, x: &T) -> Result<usize, usize>
    where
        T: Ord,
    {
        self.binary_search_by(|p| p.cmp(x))
    }

    /// Binary searches this sorted non-empty with a comparator function.
    ///
    /// The comparator function should implement an order consistent with the
    /// sort order of the underlying slice, returning an order code that
    /// indicates whether its argument is Less, Equal or Greater the desired
    /// target.
    ///
    /// If the value is found then `Result::Ok` is returned, containing the
    /// index of the matching element. If there are multiple matches, then any
    /// one of the matches could be returned. If the value is not found then
    /// `Result::Err` is returned, containing the index where a matching element
    /// could be inserted while maintaining sorted order.
    ///
    /// # Examples
    ///
    /// Looks up a series of four elements. The first is found, with a uniquely
    /// determined position; the second and third are not found; the fourth
    /// could match any position from 1 to 4.
    ///
    /// ```
    /// use nonempty_collections::nev;
    ///
    /// let v = nev![0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55];
    /// let seek = 0;
    /// assert_eq!(v.binary_search_by(|probe| probe.cmp(&seek)), Ok(0));
    /// let seek = 13;
    /// assert_eq!(v.binary_search_by(|probe| probe.cmp(&seek)), Ok(9));
    /// let seek = 4;
    /// assert_eq!(v.binary_search_by(|probe| probe.cmp(&seek)), Err(7));
    /// let seek = 100;
    /// assert_eq!(v.binary_search_by(|probe| probe.cmp(&seek)), Err(13));
    /// let seek = 1;
    /// let r = v.binary_search_by(|probe| probe.cmp(&seek));
    /// assert!(match r { Ok(1..=4) => true, _ => false, });
    /// ```
    pub fn binary_search_by<'a, F>(&'a self, f: F) -> Result<usize, usize>
    where
        F: FnMut(&'a T) -> Ordering,
    {
        self.inner.binary_search_by(f)
    }

    /// Binary searches this sorted non-empty vector with a key extraction
    /// function.
    ///
    /// Assumes that the vector is sorted by the key.
    ///
    /// If the value is found then `Result::Ok` is returned, containing the
    /// index of the matching element. If there are multiple matches, then any
    /// one of the matches could be returned. If the value is not found then
    /// `Result::Err` is returned, containing the index where a matching element
    /// could be inserted while maintaining sorted order.
    ///
    /// # Examples
    ///
    /// Looks up a series of four elements in a non-empty vector of pairs sorted
    /// by their second elements. The first is found, with a uniquely determined
    /// position; the second and third are not found; the fourth could match any
    /// position in [1, 4].
    ///
    /// ```
    /// use nonempty_collections::nev;
    ///
    /// let v = nev![
    ///     (0, 0), (2, 1), (4, 1), (5, 1), (3, 1),
    ///     (1, 2), (2, 3), (4, 5), (5, 8), (3, 13),
    ///     (1, 21), (2, 34), (4, 55)
    /// ];
    ///
    /// assert_eq!(v.binary_search_by_key(&0, |&(a,b)| b),  Ok(0));
    /// assert_eq!(v.binary_search_by_key(&13, |&(a,b)| b),  Ok(9));
    /// assert_eq!(v.binary_search_by_key(&4, |&(a,b)| b),   Err(7));
    /// assert_eq!(v.binary_search_by_key(&100, |&(a,b)| b), Err(13));
    /// let r = v.binary_search_by_key(&1, |&(a,b)| b);
    /// assert!(match r { Ok(1..=4) => true, _ => false, });
    /// ```
    pub fn binary_search_by_key<'a, B, F>(&'a self, b: &B, mut f: F) -> Result<usize, usize>
    where
        B: Ord,
        F: FnMut(&'a T) -> B,
    {
        self.binary_search_by(|k| f(k).cmp(b))
    }

    /// Sorts the `NEVec` in place.
    ///
    /// See also [`slice::sort`].
    ///
    /// ```
    /// use nonempty_collections::nev;
    ///
    /// let mut n = nev![5,4,3,2,1];
    /// n.sort();
    /// assert_eq!(nev![1,2,3,4,5], n);
    ///
    /// // Naturally, sorting a sorted result should be the same.
    /// n.sort();
    /// assert_eq!(nev![1,2,3,4,5], n);
    /// ```
    pub fn sort(&mut self)
    where
        T: Ord,
    {
        self.inner.sort()
    }

    /// Like [`NEVec::sort`], but sorts the `NEVec` with a given comparison
    /// function.
    ///
    /// See also [`slice::sort_by`].
    ///
    /// ```
    /// use nonempty_collections::nev;
    ///
    /// let mut n = nev!["Sirion", "Gelion", "Narog"];
    /// n.sort_by(|a, b| b.cmp(&a));
    /// assert_eq!(nev!["Sirion", "Narog", "Gelion"], n);
    /// ```
    pub fn sort_by<F>(&mut self, mut compare: F)
    where
        F: FnMut(&T, &T) -> Ordering,
    {
        if self.tail.is_empty().not() {
            let zero: &T = &self.tail[0];

            let (ix, smallest) =
                self.tail
                    .iter()
                    .enumerate()
                    .fold((0, zero), |(ix, smallest), (ix_curr, curr)| {
                        if matches!(compare(curr, smallest), Ordering::Less) {
                            (ix_curr, curr)
                        } else {
                            (ix, smallest)
                        }
                    });

            if matches!(compare(&self.head, smallest), Ordering::Greater) {
                std::mem::swap(&mut self.head, self.tail.index_mut(ix));
            }

            self.tail.sort_by(compare);
        }
    }

    /// Like [`NEVec::sort`], but sorts the `NEVec` after first transforming
    /// each element into something easily comparable. Beware of expensive key
    /// functions, as the results of each call are not cached.
    ///
    /// See also [`slice::sort_by_key`].
    ///
    /// ```
    /// use nonempty_collections::nev;
    ///
    /// let mut n = nev![-5i32, 4, 1, -3, 2];
    /// n.sort_by_key(|k| k.abs());
    /// assert_eq!(nev![1, 2, -3, 4, -5], n);
    /// ```
    pub fn sort_by_key<K, F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> K,
        K: Ord,
    {
        self.sort_by(|a, b| f(a).cmp(&f(b)));
    }

    /// Yields a `NESlice`.
    pub fn as_nonempty_slice(&self) -> crate::NESlice<'_, T> {
        crate::NESlice::from_slice_unchecked(self.inner.as_slice())
    }

    /// Removes all but the first of consecutive elements in the vector that resolve to the same
    /// key.
    ///
    /// If the vector is sorted, this removes all duplicates.
    ///
    /// # Examples
    ///
    /// ```
    /// use nonempty_collections::nev;
    /// let mut v = nev![10, 20, 21, 30, 20];
    ///
    /// v.dedup_by_key(|i| *i / 10);
    ///
    /// assert_eq!(nev![10, 20, 30, 20], v);
    /// ```
    pub fn dedup_by_key<F, K>(&mut self, mut key: F)
    where
        F: FnMut(&mut T) -> K,
        K: PartialEq,
    {
        self.dedup_by(|a, b| key(a) == key(b))
    }

    /// Removes all but the first of consecutive elements in the vector satisfying a given equality
    /// relation.
    ///
    /// The `same_bucket` function is passed references to two elements from the vector and
    /// must determine if the elements compare equal. The elements are passed in opposite order
    /// from their order in the slice, so if `same_bucket(a, b)` returns `true`, `a` is removed.
    ///
    /// If the vector is sorted, this removes all duplicates.
    ///
    /// # Examples
    ///
    /// ```
    /// use nonempty_collections::nev;
    /// let mut v = nev!["foo", "Foo", "foo", "bar", "Bar", "baz", "bar"];
    ///
    /// v.dedup_by(|a, b| a.eq_ignore_ascii_case(b));
    ///
    /// assert_eq!(nev!["foo", "bar", "baz", "bar"], v);
    /// ```
    pub fn dedup_by<F>(&mut self, same_bucket: F)
    where
        F: FnMut(&mut T, &mut T) -> bool,
    {
        self.inner.dedup_by(same_bucket)
    }

    /// Returns a non-empty iterator over `chunk_size` elements of the `NEVec`
    /// at a time, starting at the beginning of the `NEVec`.
    ///
    /// ```
    /// use nonempty_collections::*;
    /// use std::num::NonZeroUsize;
    ///
    /// let v = nev![1,2,3,4,5,6];
    /// let n = NonZeroUsize::new(2).unwrap();
    /// let r = v.nonempty_chunks(n).collect::<NEVec<_>>();
    ///
    /// let a = nev![1,2];
    /// let b = nev![3,4];
    /// let c = nev![5,6];
    ///
    /// assert_eq!(r, nev![a.as_nonempty_slice(), b.as_nonempty_slice(), c.as_nonempty_slice()]);
    /// ```
    pub fn nonempty_chunks(&self, chunk_size: NonZeroUsize) -> NEChunks<'_, T> {
        NEChunks {
            inner: self.inner.chunks(chunk_size.get()),
        }
    }

    /// Returns the index of the partition point according to the given predicate
    /// (the index of the first element of the second partition).
    ///
    /// The vector is assumed to be partitioned according to the given predicate.
    /// This means that all elements for which the predicate returns true are at the start of the vector
    /// and all elements for which the predicate returns false are at the end.
    /// For example, `[7, 15, 3, 5, 4, 12, 6]` is partitioned under the predicate `x % 2 != 0`
    /// (all odd numbers are at the start, all even at the end).
    ///
    /// If this vector is not partitioned, the returned result is unspecified and meaningless,
    /// as this method performs a kind of binary search.
    ///
    /// See also [`NEVec::binary_search`], [`NEVec::binary_search_by`], and
    /// [`NEVec::binary_search_by_key`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use nonempty_collections::*;
    /// #
    /// let v = nev![1, 2, 3, 3, 5, 6, 7];
    /// let i = v.partition_point(|&x| x < 5);
    ///
    /// assert_eq!(i, 4);
    /// ```
    ///
    /// If all elements of the non-empty vector match the predicate, then the
    /// length of the vector will be returned:
    ///
    /// ```
    /// # use nonempty_collections::*;
    /// #
    /// let a = nev![2, 4, 8];
    /// assert_eq!(a.partition_point(|&x| x < 100), a.len().get());
    /// ```
    ///
    /// If you want to insert an item to a sorted vector, while maintaining
    /// sort order:
    ///
    /// ```
    /// # use nonempty_collections::*;
    /// #
    /// let mut s = nev![0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55];
    /// let num = 42;
    /// let idx = s.partition_point(|&x| x < num);
    /// s.insert(idx, num);
    /// assert_eq!(s, nev![0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 42, 55]);
    /// ```
    #[must_use]
    pub fn partition_point<P>(&self, mut pred: P) -> usize
    where
        P: FnMut(&T) -> bool,
    {
        self.binary_search_by(|x| {
            if pred(x) {
                Ordering::Less
            } else {
                Ordering::Greater
            }
        })
        .unwrap_or_else(|i| i)
    }
}

impl<T: PartialEq> NEVec<T> {
    /// Removes consecutive repeated elements in the vector according to the
    /// [`PartialEq`] trait implementation.
    ///
    /// If the vector is sorted, this removes all duplicates.
    ///
    /// # Examples
    ///
    /// ```
    /// use nonempty_collections::nev;
    /// let mut v = nev![1, 1, 1, 2, 3, 2, 2, 1];
    /// v.dedup();
    /// assert_eq!(nev![1, 2, 3, 2, 1], v);
    /// ```
    pub fn dedup(&mut self) {
        self.dedup_by(|a, b| a == b)
    }
}

impl<T> From<NEVec<T>> for Vec<T> {
    /// Turns a non-empty list into a Vec.
    fn from(nonempty: NEVec<T>) -> Vec<T> {
        nonempty.inner
    }
}

impl<T> From<(T, Vec<T>)> for NEVec<T> {
    /// Turns a pair of an element and a Vec into
    /// a NEVec.
    fn from((head, tail): (T, Vec<T>)) -> Self {
        let mut vec = vec![head];
        vec.extend(tail);
        NEVec { inner: vec }
    }
}

/// ```
/// use nonempty_collections::*;
///
/// let v0 = nev![1, 2, 3];
/// let v1: NEVec<_> = v0.iter().cloned().collect();
/// assert_eq!(v0, v1);
/// ```
impl<T> FromNonEmptyIterator<T> for NEVec<T> {
    fn from_nonempty_iter<I>(iter: I) -> Self
    where
        I: IntoNonEmptyIterator<Item = T>,
    {
        NEVec {
            inner: iter.into_nonempty_iter().into_iter().collect(),
        }
    }
}

/// A non-empty iterator over the values of an [`NEVec`].
#[derive(Debug)]
pub struct Iter<'a, T: 'a> {
    iter: std::slice::Iter<'a, T>,
}

impl<'a, T> NonEmptyIterator for Iter<'a, T> {}

impl<'a, T> IntoIterator for Iter<'a, T> {
    type Item = &'a T;

    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter
    }
}

/// A non-empty iterator over mutable values from an [`NEVec`].
#[derive(Debug)]
pub struct IterMut<'a, T: 'a> {
    inner: std::slice::IterMut<'a, T>,
}

impl<'a, T> NonEmptyIterator for IterMut<'a, T> {}

impl<'a, T> IntoIterator for IterMut<'a, T> {
    type Item = &'a mut T;

    type IntoIter = std::slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner
    }
}

/// An owned non-empty iterator over values from an [`NEVec`].
pub struct IntoIter<T> {
    inner: std::vec::IntoIter<T>,
}

impl<T> NonEmptyIterator for IntoIter<T> {}

impl<T> IntoIterator for IntoIter<T> {
    type Item = T;

    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner
    }
}

impl<T> IntoNonEmptyIterator for NEVec<T> {
    type Item = T;

    type IntoIter = IntoIter<T>;

    fn into_nonempty_iter(self) -> Self::IntoIter {
        IntoIter {
            inner: self.inner.into_iter(),
        }
    }
}

impl<T> IntoIterator for NEVec<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.into_iter()
    }
}

impl<'a, T> IntoIterator for &'a NEVec<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.iter()
    }
}

impl<T> std::ops::Index<usize> for NEVec<T> {
    type Output = T;

    /// ```
    /// use nonempty_collections::nev;
    ///
    /// let v = nev![1, 2, 3, 4, 5];
    ///
    /// assert_eq!(v[0], 1);
    /// assert_eq!(v[1], 2);
    /// assert_eq!(v[3], 4);
    /// ```
    fn index(&self, index: usize) -> &T {
        self.inner.index(index)
    }
}

impl<T> std::ops::IndexMut<usize> for NEVec<T> {
    fn index_mut(&mut self, index: usize) -> &mut T {
        self.inner.index_mut(index)
    }
}

impl<T> TryFrom<Vec<T>> for NEVec<T> {
    type Error = crate::Error;

    fn try_from(vec: Vec<T>) -> Result<Self, Self::Error> {
        NEVec::from_vec(vec).ok_or(crate::Error::Empty)
    }
}

impl<T> Extend<T> for NEVec<T> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>,
    {
        self.tail.extend(iter)
    }
}

#[cfg(test)]
mod tests {
    use crate::{nev, NEVec};

    struct Foo {
        user: String,
    }

    #[test]
    fn macro_usage() {
        let a = Foo {
            user: "a".to_string(),
        };
        let b = Foo {
            user: "b".to_string(),
        };

        let v = nev![a, b];
        assert_eq!("a", v.first().user);
    }

    #[test]
    fn test_from_conversion() {
        let result = NEVec::from((1, vec![2, 3, 4, 5]));
        let expected = NEVec {
            inner: vec![1, 2, 3, 4, 5],
        };
        assert_eq!(result, expected);
    }

    #[test]
    fn test_into_iter() {
        let nonempty = NEVec::from((0, vec![1, 2, 3]));
        for (i, n) in nonempty.into_iter().enumerate() {
            assert_eq!(i as i32, n);
        }
    }

    #[test]
    fn test_iter_syntax() {
        let nonempty = NEVec::from((0, vec![1, 2, 3]));
        for n in &nonempty {
            assert_eq!(*n, *n); // Prove that we're dealing with references.
        }
        for _ in nonempty {}
    }

    #[cfg(feature = "serde")]
    mod serialize {
        use crate::NEVec;
        use serde::{Deserialize, Serialize};

        #[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
        pub struct SimpleSerializable(pub i32);

        #[test]
        fn test_simple_round_trip() -> Result<(), Box<dyn std::error::Error>> {
            // Given
            let mut v = NEVec::new(SimpleSerializable(42));
            v.push(SimpleSerializable(777));
            let expected_value = v.clone();

            // When
            let res =
                serde_json::from_str::<'_, NEVec<SimpleSerializable>>(&serde_json::to_string(&v)?)?;

            // Then
            assert_eq!(res, expected_value);

            Ok(())
        }
    }

    #[test]
    fn test_result_collect() {
        use crate::{IntoNonEmptyIterator, NonEmptyIterator};

        let nonempty = nev![2, 4, 8];
        let output = nonempty
            .into_nonempty_iter()
            .map(|n| {
                if n % 2 == 0 {
                    Ok(n)
                } else {
                    Err("odd number!")
                }
            })
            .collect::<Result<NEVec<u32>, &'static str>>();

        assert_eq!(output, Ok(nev![2, 4, 8]));

        let nonempty = nev![2, 1, 8];
        let output = nonempty
            .into_nonempty_iter()
            .map(|n| {
                if n % 2 == 0 {
                    Ok(n)
                } else {
                    Err("odd number!")
                }
            })
            .collect::<Result<NEVec<u32>, &'static str>>();

        assert_eq!(output, Err("odd number!"));
    }

    #[test]
    fn test_as_slice() {
        let nonempty = NEVec::from((0, vec![1, 2, 3]));
        assert_eq!(
            nonempty.as_nonempty_slice(),
            crate::NESlice::from_slice(&[0, 1, 2, 3]).unwrap()
        );
    }

    #[test]
    fn sorting() {
        let mut n = nev![1, 5, 4, 3, 2, 1];
        n.sort();
        assert_eq!(nev![1, 1, 2, 3, 4, 5], n);

        let mut m = nev![1];
        m.sort();
        assert_eq!(nev![1], m);
    }

    #[test]
    fn extend() {
        let mut n = nev![1, 2, 3];
        let v = vec![4, 5, 6];
        n.extend(v);

        assert_eq!(n, nev![1, 2, 3, 4, 5, 6]);
    }
}
