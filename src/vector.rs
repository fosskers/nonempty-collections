//! Non-empty Vectors.

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::iter::{FromNonEmptyIterator, IntoNonEmptyIterator, NonEmptyIterator};
use std::cmp::Ordering;
use std::iter::{Chain, Once, Skip};
use std::ops::{IndexMut, Not};

/// Like the [`vec!`] macro, but enforces at least one argument. A nice short-hand
/// for constructing [`NEVec`] values.
///
/// ```
/// use nonempty_collections::{NEVec, nev};
///
/// let v = nev![1, 2, 3];
/// assert_eq!(v, NEVec { head: 1, tail: vec![2, 3] });
///
/// let v = nev![1];
/// assert_eq!(v, NEVec { head: 1, tail: Vec::new() });
///
/// // Doesn't compile!
/// // let v = nev![];
/// ```
#[macro_export]
macro_rules! nev {
    ($h:expr, $( $x:expr ),*) => {{
        let mut tail = Vec::new();
        $( tail.push($x); )*
        $crate::NEVec { head: $h, tail }
    }};
    ($h:expr) => {
        $crate::NEVec { head: $h, tail: Vec::new() }
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
/// assert_eq!("Fëanor", s.head);      // There is always a first element.
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
    /// The element of the non-empty Vector. Always exists.
    pub head: T,

    /// The remaining elements of the non-empty Vector, perhaps empty.
    pub tail: Vec<T>,
}

impl<T> NEVec<T> {
    /// Create a new non-empty list with an initial element.
    pub const fn new(head: T) -> Self {
        NEVec {
            head,
            tail: Vec::new(),
        }
    }

    /// Get the first element. Never fails.
    pub const fn first(&self) -> &T {
        &self.head
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
        &mut self.head
    }

    /// Get the possibly-empty tail of the list.
    ///
    /// ```
    /// use nonempty_collections::nev;
    ///
    /// let v = nev![42];
    /// assert_eq!(v.tail(), &[]);
    ///
    /// let v = nev![1, 4, 2, 3];
    /// assert_eq!(v.tail(), &[4, 2, 3]);
    /// ```
    pub fn tail(&self) -> &[T] {
        &self.tail
    }

    /// Push an element to the end of the list.
    pub fn push(&mut self, e: T) {
        self.tail.push(e)
    }

    /// Pop an element from the end of the list. Will never pop the head value.
    ///
    /// ```
    /// use nonempty_collections::nev;
    ///
    /// let mut v = nev![1, 2];
    /// assert_eq!(Some(2), v.pop());
    /// assert_eq!(None, v.pop());
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        self.tail.pop()
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
        let len = self.len();
        assert!(index <= len);

        if index == 0 {
            let head = std::mem::replace(&mut self.head, element);
            self.tail.insert(0, head);
        } else {
            self.tail.insert(index - 1, element);
        }
    }

    /// Get the length of the list.
    pub fn len(&self) -> usize {
        self.tail.len() + 1
    }

    /// A `NEVec` is never empty.
    #[deprecated(since = "0.1.0", note = "A NEVec is never empty.")]
    pub const fn is_empty(&self) -> bool {
        false
    }

    /// Get the capacity of the list.
    pub fn capacity(&self) -> usize {
        self.tail.capacity() + 1
    }

    /// Get the last element. Never fails.
    pub fn last(&self) -> &T {
        match self.tail.last() {
            None => &self.head,
            Some(e) => e,
        }
    }

    /// Get the last element mutably.
    pub fn last_mut(&mut self) -> &mut T {
        match self.tail.last_mut() {
            None => &mut self.head,
            Some(e) => e,
        }
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
        self.iter().any(|e| e == x)
    }

    /// Get an element by index.
    pub fn get(&self, index: usize) -> Option<&T> {
        if index == 0 {
            Some(&self.head)
        } else {
            self.tail.get(index - 1)
        }
    }

    /// Get an element by index, mutably.
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if index == 0 {
            Some(&mut self.head)
        } else {
            self.tail.get_mut(index - 1)
        }
    }

    /// Truncate the list to a certain size. Must be greater than `0`.
    pub fn truncate(&mut self, len: usize) {
        assert!(len >= 1);
        self.tail.truncate(len - 1);
    }

    /// ```
    /// use nonempty_collections::*;
    ///
    /// let mut l = nev![42, 36, 58];
    ///
    /// let mut l_iter = l.iter();
    ///
    /// assert_eq!(l_iter.next(), Some(&42));
    /// assert_eq!(l_iter.next(), Some(&36));
    /// assert_eq!(l_iter.next(), Some(&58));
    /// assert_eq!(l_iter.next(), None);
    /// ```
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            head: &self.head,
            iter: std::iter::once(&self.head).chain(self.tail.iter()),
        }
    }

    /// ```
    /// use nonempty_collections::*;
    ///
    /// let mut l = nev![42, 36, 58];
    ///
    /// for i in l.iter_mut() {
    ///     *i *= 10;
    /// }
    ///
    /// let mut l_iter = l.iter();
    ///
    /// assert_eq!(l_iter.next(), Some(&420));
    /// assert_eq!(l_iter.next(), Some(&360));
    /// assert_eq!(l_iter.next(), Some(&580));
    /// assert_eq!(l_iter.next(), None);
    /// ```
    ///
    /// # Panics
    ///
    /// If you manually advance this iterator and then call
    /// [`NonEmptyIterator::first`], then you're in for a surprise.
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut {
            head: Some(&mut self.head),
            tail: self.tail.iter_mut(),
        }
    }

    /// Often we have a `Vec` (or slice `&[T]`) but want to ensure that it is
    /// `NEVec` before proceeding with a computation. Using `from_slice` will
    /// give us a proof that we have a `NEVec` in the `Some` branch, otherwise
    /// it allows the caller to handle the `None` case.
    ///
    /// # Example Use
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
        slice.split_first().map(|(h, t)| NEVec {
            head: h.clone(),
            tail: t.into(),
        })
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
    pub fn from_vec(mut vec: Vec<T>) -> Option<NEVec<T>> {
        if vec.is_empty() {
            None
        } else {
            let head = vec.remove(0);
            Some(NEVec { head, tail: vec })
        }
    }

    /// Deconstruct a `NEVec` into its head and tail. This operation never fails
    /// since we are guranteed to have a head element.
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
        (&self.head, &self.tail)
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
        match self.tail.split_last() {
            None => (&self.head, &[], &self.head),
            Some((last, middle)) => (&self.head, middle, last),
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
        self.tail.append(other)
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
    pub fn binary_search_by<'a, F>(&'a self, mut f: F) -> Result<usize, usize>
    where
        F: FnMut(&'a T) -> Ordering,
    {
        match f(&self.head) {
            Ordering::Equal => Ok(0),
            Ordering::Greater => Err(0),
            Ordering::Less => self
                .tail
                .binary_search_by(f)
                .map(|index| index + 1)
                .map_err(|index| index + 1),
        }
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
        if self.tail.is_empty().not() {
            self.tail.sort();

            if self.head > self.tail[0] {
                std::mem::swap(&mut self.head, self.tail.index_mut(0));
                self.tail.sort(); // FIXME Unfortunate second sort, as there is no ordered insert.
            }
        }
    }
}

impl<T> From<NEVec<T>> for Vec<T> {
    /// Turns a non-empty list into a Vec.
    fn from(nonempty: NEVec<T>) -> Vec<T> {
        std::iter::once(nonempty.head)
            .chain(nonempty.tail)
            .collect()
    }
}

impl<T> From<NEVec<T>> for (T, Vec<T>) {
    /// Turns a non-empty list into a Vec.
    fn from(nonempty: NEVec<T>) -> (T, Vec<T>) {
        (nonempty.head, nonempty.tail)
    }
}

impl<T> From<(T, Vec<T>)> for NEVec<T> {
    /// Turns a pair of an element and a Vec into
    /// a NEVec.
    fn from((head, tail): (T, Vec<T>)) -> Self {
        NEVec { head, tail }
    }
}

/// ```
/// use nonempty_collections::nev;
///
/// let v = nev![1, 2, 3];
/// ```
impl<T> FromNonEmptyIterator<T> for NEVec<T> {
    fn from_nonempty_iter<I>(iter: I) -> Self
    where
        I: IntoNonEmptyIterator<Item = T>,
    {
        let (head, rest) = iter.into_nonempty_iter().first();

        NEVec {
            head,
            tail: rest.into_iter().collect(),
        }
    }
}

/// A non-empty iterator over the values of an [`NEVec`].
#[derive(Debug)]
pub struct Iter<'a, T: 'a> {
    head: &'a T,
    iter: Chain<Once<&'a T>, std::slice::Iter<'a, T>>,
}

impl<'a, T> NonEmptyIterator for Iter<'a, T> {
    type Item = &'a T;
    type Iter = Skip<Chain<Once<&'a T>, std::slice::Iter<'a, T>>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    fn first(self) -> (Self::Item, Self::Iter) {
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

/// A non-empty iterator over mutable values from an [`NEVec`].
#[derive(Debug)]
pub struct IterMut<'a, T: 'a> {
    head: Option<&'a mut T>,
    tail: std::slice::IterMut<'a, T>,
}

impl<'a, T> NonEmptyIterator for IterMut<'a, T> {
    type Item = &'a mut T;

    type Iter = std::slice::IterMut<'a, T>;

    fn first(self) -> (Self::Item, Self::Iter) {
        (self.head.unwrap(), self.tail)
    }

    fn next(&mut self) -> Option<Self::Item> {
        match self.head {
            None => self.tail.next(),
            Some(_) => self.head.take(),
        }
    }
}

impl<'a, T> IntoIterator for IterMut<'a, T> {
    type Item = &'a mut T;

    type IntoIter = Chain<Once<&'a mut T>, std::slice::IterMut<'a, T>>;

    fn into_iter(self) -> Self::IntoIter {
        std::iter::once(self.head.unwrap()).chain(self.tail)
    }
}

impl<T> IntoNonEmptyIterator for NEVec<T> {
    type Item = T;

    type IntoIter = crate::iter::Chain<crate::iter::Once<T>, std::vec::IntoIter<Self::Item>>;

    fn into_nonempty_iter(self) -> Self::IntoIter {
        crate::iter::once(self.head).chain(self.tail)
    }
}

impl<T> IntoIterator for NEVec<T> {
    type Item = T;
    type IntoIter = std::iter::Chain<std::iter::Once<T>, std::vec::IntoIter<Self::Item>>;

    fn into_iter(self) -> Self::IntoIter {
        std::iter::once(self.head).chain(self.tail)
    }
}

impl<'a, T> IntoIterator for &'a NEVec<T> {
    type Item = &'a T;
    type IntoIter = std::iter::Chain<std::iter::Once<&'a T>, std::slice::Iter<'a, T>>;

    fn into_iter(self) -> Self::IntoIter {
        std::iter::once(&self.head).chain(self.tail.iter())
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
        if index > 0 {
            &self.tail[index - 1]
        } else {
            &self.head
        }
    }
}

impl<T> std::ops::IndexMut<usize> for NEVec<T> {
    fn index_mut(&mut self, index: usize) -> &mut T {
        if index > 0 {
            &mut self.tail[index - 1]
        } else {
            &mut self.head
        }
    }
}

#[cfg(feature = "serde")]
pub mod serialize {
    //! Serde support for [`NEVec`].

    use std::{convert::TryFrom, fmt};

    use super::NEVec;

    /// Encoding/decoding errors.
    #[derive(Debug)]
    pub enum Error {
        /// There was nothing to decode.
        Empty,
    }

    impl fmt::Display for Error {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Self::Empty => {
                    f.write_str("the vector provided was empty, NEVec needs at least one element")
                }
            }
        }
    }

    impl<T> TryFrom<Vec<T>> for NEVec<T> {
        type Error = Error;

        fn try_from(vec: Vec<T>) -> Result<Self, Self::Error> {
            NEVec::from_vec(vec).ok_or(Error::Empty)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::NEVec;

    #[test]
    fn test_from_conversion() {
        let result = NEVec::from((1, vec![2, 3, 4, 5]));
        let expected = NEVec {
            head: 1,
            tail: vec![2, 3, 4, 5],
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

    #[test]
    fn test_mutate_head() {
        let mut v = NEVec::new(42);
        v.head += 1;
        assert_eq!(v.head, 43);

        let mut v = NEVec::from((1, vec![4, 2, 3]));
        v.head *= 42;
        assert_eq!(v.head, 42);
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
}
