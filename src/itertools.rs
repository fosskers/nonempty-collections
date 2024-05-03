//! Extra non-empty iterator adaptors, functions and macros.
//!
//! To extend [`NonEmptyIterator`] with methods in this crate, import
//! the [`NonEmptyItertools`] trait:
//!
//! ```
//! use nonempty_collections::NonEmptyItertools;
//! ```

use core::fmt;
use std::fmt::Debug;

use itertools::Itertools;

use crate::FromNonEmptyIterator;
use crate::IntoNonEmptyIterator;
use crate::NEVec;
use crate::NonEmptyIterator;

/// A [`NonEmptyIterator`] blanket implementation that provides extra adaptors
/// and methods, similar to [`Itertools`](https://docs.rs/itertools/) for `Iterator`.
pub trait NonEmptyItertools: NonEmptyIterator {
    /// Return an iterator adaptor that iterates over the cartesian product of
    /// the element sets of two iterators `self` and `J`.
    ///
    /// Iterator element type is `(Self::Item, J::Item)`.
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let product = nev![0, 1]
    ///     .iter()
    ///     .copied()
    ///     .cartesian_product("αβ".chars().to_nonempty_iter().unwrap())
    ///     .collect::<NEVec<_>>();
    /// assert_eq!(nev![(0, 'α'), (0, 'β'), (1, 'α'), (1, 'β')], product);
    /// ```
    fn cartesian_product<J>(self, other: J) -> Product<Self, J::IntoNEIter>
    where
        Self: Sized,
        Self::Item: Clone,
        J: IntoNonEmptyIterator,
        <J::IntoNEIter as IntoIterator>::IntoIter: Clone,
    {
        Product {
            inner: Itertools::cartesian_product(
                self.into_iter(),
                other.into_nonempty_iter().into_iter(),
            ),
        }
    }

    /// Sort all iterator elements into a new non-empty iterator in ascending
    /// order.
    ///
    /// **Note:** This consumes the entire iterator, uses the
    /// [`NEVec::sort_by_key`] method and returns the result as a new iterator
    /// that owns its elements.
    ///
    /// This sort is stable (i.e., does not reorder equal elements).
    ///
    /// The sorted iterator, if directly collected to a `NEVec`, is converted
    /// without any extra copying or allocation cost.
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// // sort people in descending order by age
    /// let people = nev![("Jane", 20), ("John", 18), ("Jill", 30), ("Jack", 30)];
    ///
    /// let oldest_people_first = people
    ///     .into_nonempty_iter()
    ///     .sorted_by_key(|x| -x.1)
    ///     .map(|(person, _age)| person)
    ///     .collect::<NEVec<_>>();
    ///
    /// assert_eq!(nev!["Jill", "Jack", "Jane", "John"], oldest_people_first);
    /// ```
    fn sorted_by_key<K, F>(self, f: F) -> crate::vector::IntoIter<Self::Item>
    where
        Self: Sized,
        K: Ord,
        F: FnMut(&Self::Item) -> K,
    {
        let mut v = NEVec::from_nonempty_iter(self);
        v.sort_by_key(f);
        v.into_nonempty_iter()
    }

    /// Check whether all elements are unique (non equal).
    ///
    /// # Examples
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let data = nev![1, 2, 3, 4, 1, 5];
    /// assert!(!nev![1, 2, 3, 4, 1, 5].iter().all_unique());
    /// assert!(nev![2, 3, 4, 1, 5].iter().all_unique());
    /// ```
    fn all_unique(self) -> bool
    where
        Self: Sized,
        Self::Item: Eq + std::hash::Hash,
    {
        self.into_iter().all_unique()
    }
}

impl<T> NonEmptyItertools for T where T: NonEmptyIterator + ?Sized {}

/// A non-empty iterator adaptor that iterates over the cartesian product of
/// the element sets of two iterators `I` and `J`.
///
/// Iterator element type is `(I::Item, J::Item)`.
///
/// See [`.cartesian_product()`](crate::itertools::Itertools::cartesian_product)
/// for more information.
#[must_use = "iterator adaptors are lazy and do nothing unless consumed"]
pub struct Product<I, J>
where
    I: NonEmptyIterator,
    J: NonEmptyIterator,
{
    inner: itertools::Product<I::IntoIter, J::IntoIter>,
}

impl<I, J> NonEmptyIterator for Product<I, J>
where
    I: NonEmptyIterator,
    J: NonEmptyIterator,
    J::Item: Clone,
    I::Item: Clone,
    J::IntoIter: Clone,
    I::IntoIter: Clone,
{
}

impl<I, J> IntoIterator for Product<I, J>
where
    I: NonEmptyIterator,
    J: NonEmptyIterator,
    J::Item: Clone,
    I::Item: Clone,
    J::IntoIter: Clone,
    I::IntoIter: Clone,
{
    type Item = (I::Item, J::Item);

    type IntoIter = itertools::Product<I::IntoIter, J::IntoIter>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner
    }
}

impl<I, J> Debug for Product<I, J>
where
    I: NonEmptyIterator,
    J: NonEmptyIterator,
    I::Item: Debug,
    J::Item: Debug,
    I::IntoIter: Debug,
    J::IntoIter: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.inner, f)
    }
}
