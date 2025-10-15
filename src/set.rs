//! Non-empty Sets.

use core::fmt;
use std::borrow::Borrow;
use std::collections::HashSet;
use std::hash::BuildHasher;
use std::hash::Hash;
use std::num::NonZeroUsize;

#[cfg(feature = "serde")]
use serde::Deserialize;
#[cfg(feature = "serde")]
use serde::Serialize;

use crate::iter::NonEmptyIterator;
use crate::FromNonEmptyIterator;
use crate::IntoIteratorExt;
use crate::IntoNonEmptyIterator;
use crate::Singleton;

/// Like the [`crate::nev!`] macro, but for Sets. A nice short-hand for
/// constructing [`NESet`] values.
///
/// ```
/// use nonempty_collections::nes;
///
/// let s = nes![1, 2, 2, 3,];
/// assert_eq!(3, s.len().get());
/// ```
#[macro_export]
macro_rules! nes {
    ($h:expr, $( $x:expr ),* $(,)?) => {{
        let mut set = $crate::NESet::new($h);
        $( set.insert($x); )*
        set
    }};
    ($h:expr) => {
        $crate::NESet::new($h)
    }
}

/// A non-empty, growable `HashSet`.
///
/// # Construction and Access
///
/// The [`nes`] macro is the simplest way to construct an `NESet`:
///
/// ```
/// use nonempty_collections::*;
///
/// let s = nes![1, 1, 2, 2, 3, 3, 4, 4];
/// let mut v: NEVec<_> = s.nonempty_iter().collect();
/// v.sort();
/// assert_eq!(nev![&1, &2, &3, &4], v);
/// ```
///
///
/// ```
/// use nonempty_collections::nes;
///
/// let s = nes!["Fëanor", "Fingolfin", "Finarfin"];
/// assert!(s.contains(&"Fëanor"));
/// ```
///
/// # Conversion
///
/// If you have a [`HashSet`] but want an `NESet`, try [`NESet::try_from_set`].
/// Naturally, this might not succeed.
///
/// If you have an `NESet` but want a `HashSet`, try their corresponding
/// [`From`] instance. This will always succeed.
///
/// ```
/// use std::collections::HashSet;
///
/// use nonempty_collections::nes;
///
/// let n0 = nes![1, 2, 3];
/// let s0 = HashSet::from(n0);
///
/// // Or just use `Into`.
/// let n1 = nes![1, 2, 3];
/// let s1: HashSet<_> = n1.into();
/// ```
///
/// # API Differences with [`HashSet`]
///
/// Note that the following methods aren't implemented for `NESet`:
///
/// - `clear`
/// - `drain`
/// - `drain_filter`
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
        serialize = "T: Eq + Hash + Clone + Serialize, S: Clone + BuildHasher",
        deserialize = "T: Eq + Hash + Deserialize<'de>, S: Default + BuildHasher"
    )),
    serde(into = "HashSet<T, S>", try_from = "HashSet<T, S>")
)]
#[derive(Clone)]
pub struct NESet<T, S = std::collections::hash_map::RandomState> {
    inner: HashSet<T, S>,
}

impl<T, S> NESet<T, S> {
    /// Returns the number of elements the set can hold without reallocating.
    #[must_use]
    pub fn capacity(&self) -> NonZeroUsize {
        unsafe { NonZeroUsize::new_unchecked(self.inner.capacity()) }
    }

    /// Returns a reference to the set's `BuildHasher`.
    #[must_use]
    pub fn hasher(&self) -> &S {
        self.inner.hasher()
    }

    /// Returns a regular iterator over the values in this non-empty set.
    ///
    /// For a `NonEmptyIterator` see `Self::nonempty_iter()`.
    pub fn iter(&self) -> std::collections::hash_set::Iter<'_, T> {
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
    /// use nonempty_collections::nes;
    ///
    /// let s = nes![1, 2, 3];
    /// assert_eq!(3, s.len().get());
    /// ```
    #[must_use]
    pub fn len(&self) -> NonZeroUsize {
        unsafe { NonZeroUsize::new_unchecked(self.inner.len()) }
    }

    /// A `NESet` is never empty.
    #[deprecated(since = "0.1.0", note = "A NESet is never empty.")]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        false
    }
}

impl<T> NESet<T>
where
    T: Eq + Hash,
{
    /// Creates a new `NESet` with a single element.
    #[must_use]
    pub fn new(value: T) -> Self {
        let mut inner = HashSet::new();
        inner.insert(value);
        Self { inner }
    }

    /// Creates a new `NESet` with a single element and specified capacity.
    ///
    /// ```
    /// use std::hash::RandomState;
    /// use std::num::NonZeroUsize;
    ///
    /// use nonempty_collections::*;
    /// let set = NESet::with_capacity(NonZeroUsize::MIN, "hello");
    /// assert_eq!(nes! {"hello"}, set);
    /// assert!(set.capacity().get() >= 1);
    /// ```
    #[must_use]
    pub fn with_capacity(capacity: NonZeroUsize, value: T) -> NESet<T> {
        let mut inner = HashSet::with_capacity(capacity.get());
        inner.insert(value);
        NESet { inner }
    }
}

impl<T, S> NESet<T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
    /// Attempt a conversion from a [`HashSet`], consuming the given `HashSet`.
    /// Will return `None` if the `HashSet` is empty.
    ///
    /// ```
    /// use std::collections::HashSet;
    ///
    /// use nonempty_collections::nes;
    /// use nonempty_collections::NESet;
    ///
    /// let mut s = HashSet::new();
    /// s.extend([1, 2, 3]);
    ///
    /// let n = NESet::try_from_set(s);
    /// assert_eq!(Some(nes![1, 2, 3]), n);
    /// let s: HashSet<()> = HashSet::new();
    /// assert_eq!(None, NESet::try_from_set(s));
    /// ```
    #[must_use]
    pub fn try_from_set(set: HashSet<T, S>) -> Option<NESet<T, S>> {
        if set.is_empty() {
            None
        } else {
            Some(NESet { inner: set })
        }
    }

    /// Returns true if the set contains a value.
    ///
    /// ```
    /// use nonempty_collections::nes;
    ///
    /// let s = nes![1, 2, 3];
    /// assert!(s.contains(&3));
    /// assert!(!s.contains(&10));
    /// ```
    #[must_use]
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.inner.contains(value)
    }

    /// Visits the values representing the difference, i.e., the values that are
    /// in `self` but not in `other`.
    ///
    /// ```
    /// use nonempty_collections::nes;
    ///
    /// let s0 = nes![1, 2, 3];
    /// let s1 = nes![3, 4, 5];
    /// let mut v: Vec<_> = s0.difference(&s1).collect();
    /// v.sort();
    /// assert_eq!(vec![&1, &2], v);
    /// ```
    pub fn difference<'a>(
        &'a self,
        other: &'a NESet<T, S>,
    ) -> std::collections::hash_set::Difference<'a, T, S> {
        self.inner.difference(&other.inner)
    }

    /// Returns a reference to the value in the set, if any, that is equal to
    /// the given value.
    ///
    /// The value may be any borrowed form of the set’s value type, but `Hash`
    /// and `Eq` on the borrowed form must match those for the value type.
    ///
    /// ```
    /// use nonempty_collections::nes;
    ///
    /// let s = nes![1, 2, 3];
    /// assert_eq!(Some(&3), s.get(&3));
    /// assert_eq!(None, s.get(&10));
    /// ```
    #[must_use]
    pub fn get<Q>(&self, value: &Q) -> Option<&T>
    where
        T: Borrow<Q>,
        Q: Eq + Hash,
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
    /// use nonempty_collections::nes;
    ///
    /// let mut s = nes![1, 2, 3];
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
    /// use nonempty_collections::nes;
    ///
    /// let s0 = nes![1, 2, 3];
    /// let s1 = nes![3, 4, 5];
    /// let mut v: Vec<_> = s0.intersection(&s1).collect();
    /// v.sort();
    /// assert_eq!(vec![&3], v);
    /// ```
    pub fn intersection<'a>(
        &'a self,
        other: &'a NESet<T, S>,
    ) -> std::collections::hash_set::Intersection<'a, T, S> {
        self.inner.intersection(&other.inner)
    }

    /// Returns `true` if `self` has no elements in common with `other`.
    /// This is equivalent to checking for an empty intersection.
    ///
    /// ```
    /// use nonempty_collections::nes;
    ///
    /// let s0 = nes![1, 2, 3];
    /// let s1 = nes![4, 5, 6];
    /// assert!(s0.is_disjoint(&s1));
    /// ```
    #[must_use]
    pub fn is_disjoint(&self, other: &NESet<T, S>) -> bool {
        self.inner.is_disjoint(&other.inner)
    }

    /// Returns `true` if the set is a subset of another, i.e., `other` contains
    /// at least all the values in `self`.
    ///
    /// ```
    /// use nonempty_collections::nes;
    ///
    /// let sub = nes![1, 2, 3];
    /// let sup = nes![1, 2, 3, 4];
    ///
    /// assert!(sub.is_subset(&sup));
    /// assert!(!sup.is_subset(&sub));
    /// ```
    #[must_use]
    pub fn is_subset(&self, other: &NESet<T, S>) -> bool {
        self.inner.is_subset(&other.inner)
    }

    /// Returns `true` if the set is a superset of another, i.e., `self`
    /// contains at least all the values in `other`.
    ///
    /// ```
    /// use nonempty_collections::nes;
    ///
    /// let sub = nes![1, 2, 3];
    /// let sup = nes![1, 2, 3, 4];
    ///
    /// assert!(sup.is_superset(&sub));
    /// assert!(!sub.is_superset(&sup));
    /// ```
    #[must_use]
    pub fn is_superset(&self, other: &NESet<T, S>) -> bool {
        self.inner.is_superset(&other.inner)
    }

    /// Adds a value to the set, replacing the existing value, if any, that is
    /// equal to the given one. Returns the replaced value.
    pub fn replace(&mut self, value: T) -> Option<T> {
        self.inner.replace(value)
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the `NESet`. The collection may reserve more space to avoid frequent
    /// reallocations.
    ///
    /// # Panics
    ///
    /// Panics if the new allocation size overflows `usize`.
    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(additional);
    }

    /// Shrinks the capacity of the set as much as possible. It will drop down
    /// as much as possible while maintaining the internal rules and possibly
    /// leaving some space in accordance with the resize policy.
    pub fn shrink_to_fit(&mut self) {
        self.inner.shrink_to_fit();
    }

    /// Visits the values representing the union, i.e., all the values in `self`
    /// or `other`, without duplicates.
    ///
    /// Note that a Union is always non-empty.
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let s0 = nes![1, 2, 3];
    /// let s1 = nes![3, 4, 5];
    /// let mut v: NEVec<_> = s0.union(&s1).collect();
    /// v.sort();
    /// assert_eq!(nev![&1, &2, &3, &4, &5], v);
    /// ```
    pub fn union<'a>(&'a self, other: &'a NESet<T, S>) -> Union<'a, T, S> {
        Union {
            inner: self.inner.union(&other.inner),
        }
    }

    /// See [`HashSet::with_capacity_and_hasher`].
    #[must_use]
    pub fn with_capacity_and_hasher(capacity: NonZeroUsize, hasher: S, value: T) -> NESet<T, S> {
        let mut inner = HashSet::with_capacity_and_hasher(capacity.get(), hasher);
        inner.insert(value);
        NESet { inner }
    }

    /// See [`HashSet::with_hasher`].
    #[must_use]
    pub fn with_hasher(hasher: S, value: T) -> NESet<T, S> {
        let mut inner = HashSet::with_hasher(hasher);
        inner.insert(value);
        NESet { inner }
    }
}

impl<T, S> AsRef<HashSet<T, S>> for NESet<T, S> {
    fn as_ref(&self) -> &HashSet<T, S> {
        &self.inner
    }
}

impl<T, S> AsMut<HashSet<T, S>> for NESet<T, S> {
    fn as_mut(&mut self) -> &mut HashSet<T, S> {
        &mut self.inner
    }
}

impl<T, S> PartialEq for NESet<T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
    /// ```
    /// use nonempty_collections::nes;
    ///
    /// let s0 = nes![1, 2, 3];
    /// let s1 = nes![1, 2, 3];
    /// let s2 = nes![1, 2];
    /// let s3 = nes![1, 2, 3, 4];
    ///
    /// assert!(s0 == s1);
    /// assert!(s0 != s2);
    /// assert!(s0 != s3);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.intersection(other).count() == self.len().get()
    }
}

impl<T, S> Eq for NESet<T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
}

impl<T, S> IntoNonEmptyIterator for NESet<T, S> {
    type IntoNEIter = IntoIter<T>;

    fn into_nonempty_iter(self) -> Self::IntoNEIter {
        IntoIter {
            iter: self.inner.into_iter(),
        }
    }
}

impl<'a, T, S> IntoNonEmptyIterator for &'a NESet<T, S> {
    type IntoNEIter = Iter<'a, T>;

    fn into_nonempty_iter(self) -> Self::IntoNEIter {
        self.nonempty_iter()
    }
}

impl<T, S> IntoIterator for NESet<T, S> {
    type Item = T;

    type IntoIter = std::collections::hash_set::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.into_iter()
    }
}

impl<'a, T, S> IntoIterator for &'a NESet<T, S> {
    type Item = &'a T;

    type IntoIter = std::collections::hash_set::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// ```
/// use nonempty_collections::*;
///
/// let s0 = nes![1, 2, 3];
/// let s1: NESet<_> = s0.nonempty_iter().cloned().collect();
/// assert_eq!(s0, s1);
/// ```
impl<T, S> FromNonEmptyIterator<T> for NESet<T, S>
where
    T: Eq + Hash,
    S: BuildHasher + Default,
{
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let v = nev![1, 1, 2, 3, 2];
    /// let s = NESet::from_nonempty_iter(v);
    ///
    /// assert_eq!(nes![1, 2, 3], s);
    /// ```
    fn from_nonempty_iter<I>(iter: I) -> Self
    where
        I: IntoNonEmptyIterator<Item = T>,
    {
        NESet {
            inner: iter.into_nonempty_iter().into_iter().collect(),
        }
    }
}

/// A non-empty iterator over the values of an [`NESet`].
#[must_use = "non-empty iterators are lazy and do nothing unless consumed"]
pub struct Iter<'a, T: 'a> {
    iter: std::collections::hash_set::Iter<'a, T>,
}

impl<'a, T: 'a> IntoIterator for Iter<'a, T> {
    type Item = &'a T;

    type IntoIter = std::collections::hash_set::Iter<'a, T>;

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

/// An owned non-empty iterator over the values of an [`NESet`].
#[must_use = "non-empty iterators are lazy and do nothing unless consumed"]
pub struct IntoIter<T> {
    iter: std::collections::hash_set::IntoIter<T>,
}

impl<T> IntoIterator for IntoIter<T> {
    type Item = T;

    type IntoIter = std::collections::hash_set::IntoIter<T>;

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

/// A non-empty iterator producing elements in the union of two [`NESet`]s.
#[must_use = "non-empty iterators are lazy and do nothing unless consumed"]
pub struct Union<'a, T: 'a, S: 'a> {
    inner: std::collections::hash_set::Union<'a, T, S>,
}

impl<'a, T, S> IntoIterator for Union<'a, T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
    type Item = &'a T;

    type IntoIter = std::collections::hash_set::Union<'a, T, S>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner
    }
}

impl<T, S> NonEmptyIterator for Union<'_, T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
}

impl<T, S> fmt::Debug for Union<'_, T, S>
where
    T: fmt::Debug + Eq + Hash,
    S: BuildHasher,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl<T, S> From<NESet<T, S>> for HashSet<T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
    /// ```
    /// use std::collections::HashSet;
    ///
    /// use nonempty_collections::nes;
    ///
    /// let s: HashSet<_> = nes![1, 2, 3].into();
    /// let mut v: Vec<_> = s.into_iter().collect();
    /// v.sort();
    /// assert_eq!(vec![1, 2, 3], v);
    /// ```
    fn from(s: NESet<T, S>) -> Self {
        s.inner
    }
}

impl<T: fmt::Debug, S> fmt::Debug for NESet<T, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl<T, S> TryFrom<HashSet<T, S>> for NESet<T, S>
where
    T: Eq + Hash,
    S: BuildHasher + Default,
{
    type Error = crate::Error;

    fn try_from(set: HashSet<T, S>) -> Result<Self, Self::Error> {
        let ne = set
            .try_into_nonempty_iter()
            .ok_or(crate::Error::Empty)?
            .collect();

        Ok(ne)
    }
}

impl<T> Singleton for NESet<T>
where
    T: Eq + Hash,
{
    type Item = T;

    /// ```
    /// use nonempty_collections::{NESet, Singleton, nes};
    ///
    /// let s = NESet::singleton(1);
    /// assert_eq!(nes![1], s);
    /// ```
    fn singleton(item: Self::Item) -> Self {
        NESet::new(item)
    }
}

#[cfg(test)]
mod test {
    use maplit::hashset;

    #[test]
    fn debug_impl() {
        let expected = format!("{:?}", hashset! {0});
        let actual = format!("{:?}", nes! {0});
        assert_eq!(expected, actual);
    }

    #[test]
    fn iter_debug_impl() {
        let expected = format!("{:?}", hashset! {0}.iter());
        let actual = format!("{:?}", nes! {0}.nonempty_iter());
        assert_eq!(expected, actual);
    }
}

#[cfg(feature = "serde")]
#[cfg(test)]
mod serde_tests {
    use std::collections::HashSet;

    use crate::nes;
    use crate::NESet;

    #[test]
    fn json() {
        let set0 = nes![1, 1, 2, 3, 2, 1, 4];
        let j = serde_json::to_string(&set0).unwrap();
        let set1 = serde_json::from_str(&j).unwrap();
        assert_eq!(set0, set1);

        let empty: HashSet<usize> = HashSet::new();
        let j = serde_json::to_string(&empty).unwrap();
        let bad = serde_json::from_str::<NESet<usize>>(&j);
        assert!(bad.is_err());
    }
}
