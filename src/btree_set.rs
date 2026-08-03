//! Non-empty [`BTreeSet`]s.

use core::fmt;
use std::borrow::Borrow;
use std::collections::BTreeSet;
use std::num::NonZeroUsize;

#[cfg(feature = "serde")]
use serde::Deserialize;
#[cfg(feature = "serde")]
use serde::Serialize;

use crate::FromNonEmptyIterator;
use crate::IntoIteratorExt;
use crate::IntoNonEmptyIterator;
use crate::Singleton;
use crate::iter::NonEmptyIterator;

/// Like the [`crate::nes!`] macro, but for Binary Tree Sets.
///
/// ```
/// use nonempty_collections::nebts;
///
/// let s = nebts![1, 2, 2, 3,];
/// assert_eq!(3, s.len().get());
/// ```
#[macro_export]
macro_rules! nebts {
    ($h:expr, $( $x:expr ),* $(,)?) => {{
        let mut set = $crate::NEBTreeSet::new($h);
        $( set.insert($x); )*
        set
    }};
    ($h:expr) => {
        $crate::NEBTreeSet::new($h)
    }
}

/// A non-empty, growable `BTreeSet`.
///
/// # Construction and Access
///
/// The [`nebts`] macro is the simplest way to construct an `NEBTreeSet`:
///
/// ```
/// use nonempty_collections::*;
///
/// let s = nebts![1, 1, 2, 2, 3, 3, 4, 4];
/// let mut v: NEVec<_> = s.nonempty_iter().collect();
/// v.sort();
/// assert_eq!(nev![&1, &2, &3, &4], v);
/// ```
///
/// ```
/// use nonempty_collections::nebts;
///
/// let s = nebts!["Fëanor", "Fingolfin", "Finarfin"];
/// assert!(s.contains(&"Fëanor"));
/// ```
///
/// # Conversion
///
/// If you have a [`BTreeSet`] but want an `NEBTreeSet`, try [`NEBTreeSet::try_from_set`].
/// Naturally, this might not succeed.
///
/// If you have an `NEBTreeSet` but want a `BTreeSet`, try their corresponding
/// [`From`] instance. This will always succeed.
///
/// ```
/// use std::collections::BTreeSet;
///
/// use nonempty_collections::nebts;
///
/// let n0 = nebts![1, 2, 3];
/// let s0 = BTreeSet::from(n0);
///
/// // Or just use `Into`.
/// let n1 = nebts![1, 2, 3];
/// let s1: BTreeSet<_> = n1.into();
/// ```
///
/// # API Differences with [`BTreeSet`]
///
/// Note that the following methods aren't implemented for `NEBTreeSet`:
///
/// - `clear`
/// - `remove`
/// - `retain`
/// - `take`
///
/// As these methods are all "mutate-in-place" style and are difficult to
/// reconcile with the non-emptiness guarantee.
#[allow(clippy::unsafe_derive_deserialize)]
#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(bound(
        serialize = "T: Ord + Clone + Serialize",
        deserialize = "T: Ord + Deserialize<'de>"
    )),
    serde(into = "BTreeSet<T>", try_from = "BTreeSet<T>")
)]
#[derive(Clone)]
pub struct NEBTreeSet<T> {
    inner: BTreeSet<T>,
}

impl<T> NEBTreeSet<T>
where
    T: Ord,
{
    /// Creates a new `NEBTreeSet` with a single element.
    #[must_use]
    pub fn new(value: T) -> Self {
        let mut inner = BTreeSet::new();
        inner.insert(value);
        Self { inner }
    }

    /// Returns a regular iterator over the values in this non-empty set.
    ///
    /// For a `NonEmptyIterator` see `Self::nonempty_iter()`.
    pub fn iter(&self) -> std::collections::btree_set::Iter<'_, T> {
        self.inner.iter()
    }

    /// An iterator visiting all elements in arbitrary order.
    pub fn nonempty_iter(&self) -> Iter<'_, T> {
        Iter {
            iter: self.inner.iter(),
        }
    }

    /// Returns the number of elements in the set. Always 1 or more.
    ///
    /// ```
    /// use nonempty_collections::nebts;
    ///
    /// let s = nebts![1, 2, 3];
    /// assert_eq!(3, s.len().get());
    /// ```
    #[must_use]
    pub fn len(&self) -> NonZeroUsize {
        unsafe { NonZeroUsize::new_unchecked(self.inner.len()) }
    }

    /// Attempt a conversion from a [`BTreeSet`], consuming the given `BTreeSet`.
    /// Will return `None` if the `BTreeSet` is empty.
    ///
    /// ```
    /// use std::collections::BTreeSet;
    ///
    /// use nonempty_collections::nebts;
    /// use nonempty_collections::NEBTreeSet;
    ///
    /// let mut s = BTreeSet::new();
    /// s.extend([1, 2, 3]);
    ///
    /// let n = NEBTreeSet::try_from_set(s);
    /// assert_eq!(Some(nebts![1, 2, 3]), n);
    /// let s: BTreeSet<()> = BTreeSet::new();
    /// assert_eq!(None, NEBTreeSet::try_from_set(s));
    /// ```
    #[must_use]
    pub fn try_from_set(set: BTreeSet<T>) -> Option<NEBTreeSet<T>> {
        if set.is_empty() {
            None
        } else {
            Some(NEBTreeSet { inner: set })
        }
    }

    /// Returns true if the set contains a value.
    ///
    /// ```
    /// use nonempty_collections::nebts;
    ///
    /// let s = nebts![1, 2, 3];
    /// assert!(s.contains(&3));
    /// assert!(!s.contains(&10));
    /// ```
    #[must_use]
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Ord + Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.inner.contains(value)
    }

    /// Visits the values representing the difference, i.e., the values that are
    /// in `self` but not in `other`.
    ///
    /// ```
    /// use nonempty_collections::nebts;
    ///
    /// let s0 = nebts![1, 2, 3];
    /// let s1 = nebts![3, 4, 5];
    /// let mut v: Vec<_> = s0.difference(&s1).collect();
    /// v.sort();
    /// assert_eq!(vec![&1, &2], v);
    /// ```
    pub fn difference<'a>(
        &'a self,
        other: &'a NEBTreeSet<T>,
    ) -> std::collections::btree_set::Difference<'a, T> {
        self.inner.difference(&other.inner)
    }

    /// Returns a reference to the value in the set, if any, that is equal to
    /// the given value.
    ///
    /// The value may be any borrowed form of the set’s value type, but `Hash`
    /// and `Eq` on the borrowed form must match those for the value type.
    ///
    /// ```
    /// use nonempty_collections::nebts;
    ///
    /// let s = nebts![1, 2, 3];
    /// assert_eq!(Some(&3), s.get(&3));
    /// assert_eq!(None, s.get(&10));
    /// ```
    #[must_use]
    pub fn get<Q>(&self, value: &Q) -> Option<&T>
    where
        T: Ord + Borrow<Q>,
        Q: Ord,
    {
        self.inner.get(value)
    }

    /// Adds a value to the set.
    ///
    /// If the set did not have this value present, `true` is returned.
    ///
    /// If the set did have this value present, `false` is returned.
    ///
    /// ```
    /// use nonempty_collections::nebts;
    ///
    /// let mut s = nebts![1, 2, 3];
    /// assert_eq!(false, s.insert(2));
    /// assert_eq!(true, s.insert(4));
    /// ```
    pub fn insert(&mut self, value: T) -> bool {
        self.inner.insert(value)
    }

    /// Visits the values representing the interesection, i.e., the values that
    /// are both in `self` and `other`.
    ///
    /// ```
    /// use nonempty_collections::nebts;
    ///
    /// let s0 = nebts![1, 2, 3];
    /// let s1 = nebts![3, 4, 5];
    /// let mut v: Vec<_> = s0.intersection(&s1).collect();
    /// v.sort();
    /// assert_eq!(vec![&3], v);
    /// ```
    pub fn intersection<'a>(
        &'a self,
        other: &'a NEBTreeSet<T>,
    ) -> std::collections::btree_set::Intersection<'a, T> {
        self.inner.intersection(&other.inner)
    }

    /// Returns `true` if `self` has no elements in common with `other`.
    /// This is equivalent to checking for an empty intersection.
    ///
    /// ```
    /// use nonempty_collections::nebts;
    ///
    /// let s0 = nebts![1, 2, 3];
    /// let s1 = nebts![4, 5, 6];
    /// assert!(s0.is_disjoint(&s1));
    /// ```
    #[must_use]
    pub fn is_disjoint(&self, other: &NEBTreeSet<T>) -> bool {
        self.inner.is_disjoint(&other.inner)
    }

    /// Returns `true` if the set is a subset of another, i.e., `other` contains
    /// at least all the values in `self`.
    ///
    /// ```
    /// use nonempty_collections::nebts;
    ///
    /// let sub = nebts![1, 2, 3];
    /// let sup = nebts![1, 2, 3, 4];
    ///
    /// assert!(sub.is_subset(&sup));
    /// assert!(!sup.is_subset(&sub));
    /// ```
    #[must_use]
    pub fn is_subset(&self, other: &NEBTreeSet<T>) -> bool {
        self.inner.is_subset(&other.inner)
    }

    /// Returns `true` if the set is a superset of another, i.e., `self`
    /// contains at least all the values in `other`.
    ///
    /// ```
    /// use nonempty_collections::nebts;
    ///
    /// let sub = nebts![1, 2, 3];
    /// let sup = nebts![1, 2, 3, 4];
    ///
    /// assert!(sup.is_superset(&sub));
    /// assert!(!sub.is_superset(&sup));
    /// ```
    #[must_use]
    pub fn is_superset(&self, other: &NEBTreeSet<T>) -> bool {
        self.inner.is_superset(&other.inner)
    }

    /// Adds a value to the set, replacing the existing value, if any, that is
    /// equal to the given one. Returns the replaced value.
    pub fn replace(&mut self, value: T) -> Option<T> {
        self.inner.replace(value)
    }

    /// Visits the values representing the union, i.e., all the values in `self`
    /// or `other`, without duplicates.
    ///
    /// Note that a Union is always non-empty.
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let s0 = nebts![1, 2, 3];
    /// let s1 = nebts![3, 4, 5];
    /// let mut v: NEVec<_> = s0.union(&s1).collect();
    /// v.sort();
    /// assert_eq!(nev![&1, &2, &3, &4, &5], v);
    /// ```
    pub fn union<'a>(&'a self, other: &'a NEBTreeSet<T>) -> Union<'a, T> {
        Union {
            inner: self.inner.union(&other.inner),
        }
    }
}

impl<T> AsRef<BTreeSet<T>> for NEBTreeSet<T> {
    fn as_ref(&self) -> &BTreeSet<T> {
        &self.inner
    }
}

impl<T> AsMut<BTreeSet<T>> for NEBTreeSet<T> {
    fn as_mut(&mut self) -> &mut BTreeSet<T> {
        &mut self.inner
    }
}

impl<T> PartialEq for NEBTreeSet<T>
where
    T: Ord,
{
    /// ```
    /// use nonempty_collections::nebts;
    ///
    /// let s0 = nebts![1, 2, 3];
    /// let s1 = nebts![1, 2, 3];
    /// let s2 = nebts![1, 2];
    /// let s3 = nebts![1, 2, 3, 4];
    ///
    /// assert!(s0 == s1);
    /// assert!(s0 != s2);
    /// assert!(s0 != s3);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.intersection(other).count() == self.len().get()
    }
}

impl<T> Eq for NEBTreeSet<T> where T: Ord {}

impl<T> IntoNonEmptyIterator for NEBTreeSet<T> {
    type IntoNEIter = IntoIter<T>;

    fn into_nonempty_iter(self) -> Self::IntoNEIter {
        IntoIter {
            iter: self.inner.into_iter(),
        }
    }
}

impl<'a, T> IntoNonEmptyIterator for &'a NEBTreeSet<T>
where
    T: Ord,
{
    type IntoNEIter = Iter<'a, T>;

    fn into_nonempty_iter(self) -> Self::IntoNEIter {
        self.nonempty_iter()
    }
}

impl<T> IntoIterator for NEBTreeSet<T> {
    type Item = T;

    type IntoIter = std::collections::btree_set::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.into_iter()
    }
}

impl<'a, T> IntoIterator for &'a NEBTreeSet<T>
where
    T: Ord,
{
    type Item = &'a T;

    type IntoIter = std::collections::btree_set::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// ```
/// use nonempty_collections::*;
///
/// let s0 = nebts![1, 2, 3];
/// let s1: NEBTreeSet<_> = s0.nonempty_iter().cloned().collect();
/// assert_eq!(s0, s1);
/// ```
impl<T> FromNonEmptyIterator<T> for NEBTreeSet<T>
where
    T: Ord,
{
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let v = nev![1, 1, 2, 3, 2];
    /// let s = NEBTreeSet::from_nonempty_iter(v);
    ///
    /// assert_eq!(nebts![1, 2, 3], s);
    /// ```
    fn from_nonempty_iter<I>(iter: I) -> Self
    where
        I: IntoNonEmptyIterator<Item = T>,
    {
        NEBTreeSet {
            inner: iter.into_nonempty_iter().into_iter().collect(),
        }
    }
}

/// A non-empty iterator over the values of an [`NEBTreeSet`].
#[must_use = "non-empty iterators are lazy and do nothing unless consumed"]
pub struct Iter<'a, T: 'a> {
    iter: std::collections::btree_set::Iter<'a, T>,
}

impl<'a, T: 'a> IntoIterator for Iter<'a, T> {
    type Item = &'a T;

    type IntoIter = std::collections::btree_set::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter
    }
}

impl<T> NonEmptyIterator for Iter<'_, T> {}

impl<T: fmt::Debug> fmt::Debug for Iter<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.iter.fmt(f)
    }
}

/// An owned non-empty iterator over the values of an [`NEBTreeSet`].
#[must_use = "non-empty iterators are lazy and do nothing unless consumed"]
pub struct IntoIter<T> {
    iter: std::collections::btree_set::IntoIter<T>,
}

impl<T> IntoIterator for IntoIter<T> {
    type Item = T;

    type IntoIter = std::collections::btree_set::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter
    }
}

impl<T> NonEmptyIterator for IntoIter<T> {}

impl<T: fmt::Debug> fmt::Debug for IntoIter<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.iter.fmt(f)
    }
}

/// A non-empty iterator producing elements in the union of two [`NEBTreeSet`]s.
#[must_use = "non-empty iterators are lazy and do nothing unless consumed"]
pub struct Union<'a, T: 'a> {
    inner: std::collections::btree_set::Union<'a, T>,
}

impl<'a, T> IntoIterator for Union<'a, T>
where
    T: Ord,
{
    type Item = &'a T;

    type IntoIter = std::collections::btree_set::Union<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner
    }
}

impl<T> NonEmptyIterator for Union<'_, T> where T: Ord {}

impl<T> fmt::Debug for Union<'_, T>
where
    T: fmt::Debug + Ord,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl<T> From<NEBTreeSet<T>> for BTreeSet<T>
where
    T: Ord,
{
    /// ```
    /// use std::collections::BTreeSet;
    ///
    /// use nonempty_collections::nebts;
    ///
    /// let s: BTreeSet<_> = nebts![1, 2, 3].into();
    /// let mut v: Vec<_> = s.into_iter().collect();
    /// v.sort();
    /// assert_eq!(vec![1, 2, 3], v);
    /// ```
    fn from(s: NEBTreeSet<T>) -> Self {
        s.inner
    }
}

impl<T: fmt::Debug> fmt::Debug for NEBTreeSet<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl<T> TryFrom<BTreeSet<T>> for NEBTreeSet<T>
where
    T: Ord,
{
    type Error = crate::Error;

    fn try_from(set: BTreeSet<T>) -> Result<Self, Self::Error> {
        let ne = set
            .try_into_nonempty_iter()
            .ok_or(crate::Error::Empty)?
            .collect();

        Ok(ne)
    }
}

impl<T> Singleton for NEBTreeSet<T>
where
    T: Ord,
{
    type Item = T;

    /// ```
    /// use nonempty_collections::{NEBTreeSet, Singleton, nebts};
    ///
    /// let s = NEBTreeSet::singleton(1);
    /// assert_eq!(nebts![1], s);
    /// ```
    fn singleton(item: Self::Item) -> Self {
        NEBTreeSet::new(item)
    }
}

impl<T> Extend<T> for NEBTreeSet<T>
where
    T: Ord,
{
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.inner.extend(iter);
    }
}

#[cfg(feature = "arbitrary")]
impl<'a, T> arbitrary::Arbitrary<'a> for NEBTreeSet<T>
where
    T: Ord + arbitrary::Arbitrary<'a>,
{
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let head = T::arbitrary(u)?;
        let tail = BTreeSet::<T>::arbitrary(u)?;

        let mut map = Self::new(head);
        map.extend(tail);

        Ok(map)
    }
}

#[cfg(test)]
mod test {
    use maplit::btreeset;

    #[test]
    fn debug_impl() {
        let expected = format!("{:?}", btreeset! {0});
        let actual = format!("{:?}", nebts! {0});
        assert_eq!(expected, actual);
    }

    #[test]
    fn iter_debug_impl() {
        let expected = format!("{:?}", btreeset! {0}.iter());
        let actual = format!("{:?}", nebts! {0}.nonempty_iter());
        assert_eq!(expected, actual);
    }
}

#[cfg(feature = "serde")]
#[cfg(test)]
mod serde_tests {
    use crate::NEBTreeSet;
    use std::collections::BTreeSet;

    #[test]
    fn json() {
        let set0 = nebts![1, 1, 2, 3, 2, 1, 4];
        let j = serde_json::to_string(&set0).unwrap();
        let set1 = serde_json::from_str(&j).unwrap();
        assert_eq!(set0, set1);

        let empty: BTreeSet<usize> = BTreeSet::new();
        let j = serde_json::to_string(&empty).unwrap();
        let bad = serde_json::from_str::<NEBTreeSet<usize>>(&j);
        assert!(bad.is_err());
    }
}
