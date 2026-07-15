//! Non-empty IndexSets.

use core::fmt;
use indexmap::IndexSet;
use std::borrow::Borrow;
use std::hash::BuildHasher;
use std::hash::Hash;
use std::num::NonZeroUsize;

#[cfg(feature = "schemars")]
use ::{
    schemars::{JsonSchema, Schema, SchemaGenerator},
    std::borrow::Cow,
};

#[cfg(feature = "serde")]
use serde::Deserialize;
#[cfg(feature = "serde")]
use serde::Serialize;

use crate::FromNonEmptyIterator;
use crate::IntoIteratorExt;
use crate::IntoNonEmptyIterator;
use crate::Singleton;
use crate::iter::NonEmptyIterator;

/// Like the [`crate::nev!`] macro, but for IndexSets. A nice short-hand for
/// constructing [`NEIndexSet`] values.
///
/// ```
/// use nonempty_collections::ne_indexset;
///
/// let s = ne_indexset![1, 2, 2, 3,];
/// assert_eq!(3, s.len().get());
/// ```
#[macro_export]
macro_rules! ne_indexset {
    ($h:expr, $( $x:expr ),* $(,)?) => {{
        let mut set = $crate::NEIndexSet::new($h);
        $( set.insert($x); )*
        set
    }};
    ($h:expr) => {
        $crate::NEIndexSet::new($h)
    }
}

/// A non-empty, growable `IndexSet`.
///
/// # Construction and Access
///
/// The [`ne_indexset`] macro is the simplest way to construct an `NEIndexSet`:
///
/// ```
/// use nonempty_collections::*;
///
/// let s = ne_indexset![1, 1, 2, 2, 3, 3, 4, 4];
/// let mut v: NEVec<_> = s.nonempty_iter().collect();
/// v.sort();
/// assert_eq!(nev![&1, &2, &3, &4], v);
/// ```
///
///
/// ```
/// use nonempty_collections::ne_indexset;
///
/// let s = ne_indexset!["Fëanor", "Fingolfin", "Finarfin"];
/// assert!(s.contains(&"Fëanor"));
/// ```
///
/// # Conversion
///
/// If you have a [`IndexSet`] but want an `NEIndexSet`, try [`NEIndexSet::try_from_set`].
/// Naturally, this might not succeed.
///
/// If you have an `NEIndexSet` but want a `IndexSet`, try their corresponding
/// [`From`] instance. This will always succeed.
///
/// ```
/// use indexmap::set::IndexSet;
///
/// use nonempty_collections::ne_indexset;
///
/// let n0 = ne_indexset![1, 2, 3];
/// let s0 = IndexSet::from(n0);
///
/// // Or just use `Into`.
/// let n1 = ne_indexset![1, 2, 3];
/// let s1: IndexSet<_> = n1.into();
/// ```
///
/// # API Differences with [`IndexSet`]
///
/// Note that the following methods aren't implemented for `NEIndexSet`:
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
    serde(into = "IndexSet<T, S>", try_from = "IndexSet<T, S>")
)]
#[derive(Clone)]
pub struct NEIndexSet<T, S = std::collections::hash_map::RandomState> {
    inner: IndexSet<T, S>,
}

impl<T, S> NEIndexSet<T, S> {
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
    pub fn iter(&self) -> indexmap::set::Iter<'_, T> {
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
    /// use nonempty_collections::ne_indexset;
    ///
    /// let s = ne_indexset![1, 2, 3];
    /// assert_eq!(3, s.len().get());
    /// ```
    #[must_use]
    pub fn len(&self) -> NonZeroUsize {
        unsafe { NonZeroUsize::new_unchecked(self.inner.len()) }
    }

    /// A `NEIndexSet` is never empty.
    #[deprecated(since = "0.1.0", note = "A NEIndexSet is never empty.")]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        false
    }
}

impl<T> NEIndexSet<T>
where
    T: Eq + Hash,
{
    /// Creates a new `NEIndexSet` with a single element.
    #[must_use]
    pub fn new(value: T) -> Self {
        let mut inner = IndexSet::new();
        inner.insert(value);
        Self { inner }
    }

    /// Creates a new `NEIndexSet` with a single element and specified capacity.
    ///
    /// ```
    /// use std::hash::RandomState;
    /// use std::num::NonZeroUsize;
    ///
    /// use nonempty_collections::*;
    /// let set = NEIndexSet::with_capacity(NonZeroUsize::MIN, "hello");
    /// assert_eq!(ne_indexset! {"hello"}, set);
    /// assert!(set.capacity().get() >= 1);
    /// ```
    #[must_use]
    pub fn with_capacity(capacity: NonZeroUsize, value: T) -> NEIndexSet<T> {
        let mut inner = IndexSet::with_capacity(capacity.get());
        inner.insert(value);
        NEIndexSet { inner }
    }
}

impl<T, S> NEIndexSet<T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
    /// Attempt a conversion from a [`IndexSet`], consuming the given `IndexSet`.
    /// Will return `None` if the `IndexSet` is empty.
    ///
    /// ```
    /// use indexmap::set::IndexSet;
    ///
    /// use nonempty_collections::ne_indexset;
    /// use nonempty_collections::NEIndexSet;
    ///
    /// let mut s = IndexSet::new();
    /// s.extend([1, 2, 3]);
    ///
    /// let n = NEIndexSet::try_from_set(s);
    /// assert_eq!(Some(ne_indexset![1, 2, 3]), n);
    /// let s: IndexSet<()> = IndexSet::new();
    /// assert_eq!(None, NEIndexSet::try_from_set(s));
    /// ```
    #[must_use]
    pub fn try_from_set(set: IndexSet<T, S>) -> Option<NEIndexSet<T, S>> {
        if set.is_empty() {
            None
        } else {
            Some(NEIndexSet { inner: set })
        }
    }

    /// Returns true if the set contains a value.
    ///
    /// ```
    /// use nonempty_collections::ne_indexset;
    ///
    /// let s = ne_indexset![1, 2, 3];
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
    /// use nonempty_collections::ne_indexset;
    ///
    /// let s0 = ne_indexset![1, 2, 3];
    /// let s1 = ne_indexset![3, 4, 5];
    /// let mut v: Vec<_> = s0.difference(&s1).collect();
    /// v.sort();
    /// assert_eq!(vec![&1, &2], v);
    /// ```
    pub fn difference<'a>(
        &'a self,
        other: &'a NEIndexSet<T, S>,
    ) -> indexmap::set::Difference<'a, T, S> {
        self.inner.difference(&other.inner)
    }

    /// Returns a reference to the value in the set, if any, that is equal to
    /// the given value.
    ///
    /// The value may be any borrowed form of the set’s value type, but `Hash`
    /// and `Eq` on the borrowed form must match those for the value type.
    ///
    /// ```
    /// use nonempty_collections::ne_indexset;
    ///
    /// let s = ne_indexset![1, 2, 3];
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
    /// use nonempty_collections::ne_indexset;
    ///
    /// let mut s = ne_indexset![1, 2, 3];
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
    /// use nonempty_collections::ne_indexset;
    ///
    /// let s0 = ne_indexset![1, 2, 3];
    /// let s1 = ne_indexset![3, 4, 5];
    /// let mut v: Vec<_> = s0.intersection(&s1).collect();
    /// v.sort();
    /// assert_eq!(vec![&3], v);
    /// ```
    pub fn intersection<'a>(
        &'a self,
        other: &'a NEIndexSet<T, S>,
    ) -> indexmap::set::Intersection<'a, T, S> {
        self.inner.intersection(&other.inner)
    }

    /// Returns `true` if `self` has no elements in common with `other`.
    /// This is equivalent to checking for an empty intersection.
    ///
    /// ```
    /// use nonempty_collections::ne_indexset;
    ///
    /// let s0 = ne_indexset![1, 2, 3];
    /// let s1 = ne_indexset![4, 5, 6];
    /// assert!(s0.is_disjoint(&s1));
    /// ```
    #[must_use]
    pub fn is_disjoint(&self, other: &NEIndexSet<T, S>) -> bool {
        self.inner.is_disjoint(&other.inner)
    }

    /// Returns `true` if the set is a subset of another, i.e., `other` contains
    /// at least all the values in `self`.
    ///
    /// ```
    /// use nonempty_collections::ne_indexset;
    ///
    /// let sub = ne_indexset![1, 2, 3];
    /// let sup = ne_indexset![1, 2, 3, 4];
    ///
    /// assert!(sub.is_subset(&sup));
    /// assert!(!sup.is_subset(&sub));
    /// ```
    #[must_use]
    pub fn is_subset(&self, other: &NEIndexSet<T, S>) -> bool {
        self.inner.is_subset(&other.inner)
    }

    /// Returns `true` if the set is a superset of another, i.e., `self`
    /// contains at least all the values in `other`.
    ///
    /// ```
    /// use nonempty_collections::ne_indexset;
    ///
    /// let sub = ne_indexset![1, 2, 3];
    /// let sup = ne_indexset![1, 2, 3, 4];
    ///
    /// assert!(sup.is_superset(&sub));
    /// assert!(!sub.is_superset(&sup));
    /// ```
    #[must_use]
    pub fn is_superset(&self, other: &NEIndexSet<T, S>) -> bool {
        self.inner.is_superset(&other.inner)
    }

    /// Adds a value to the set, replacing the existing value, if any, that is
    /// equal to the given one. Returns the replaced value.
    pub fn replace(&mut self, value: T) -> Option<T> {
        self.inner.replace(value)
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the `NEIndexSet`. The collection may reserve more space to avoid frequent
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
    /// let s0 = ne_indexset![1, 2, 3];
    /// let s1 = ne_indexset![3, 4, 5];
    /// let mut v: NEVec<_> = s0.union(&s1).collect();
    /// v.sort();
    /// assert_eq!(nev![&1, &2, &3, &4, &5], v);
    /// ```
    pub fn union<'a>(&'a self, other: &'a NEIndexSet<T, S>) -> Union<'a, T, S> {
        Union {
            inner: self.inner.union(&other.inner),
        }
    }

    /// See [`IndexSet::with_capacity_and_hasher`].
    #[must_use]
    pub fn with_capacity_and_hasher(
        capacity: NonZeroUsize,
        hasher: S,
        value: T,
    ) -> NEIndexSet<T, S> {
        let mut inner = IndexSet::with_capacity_and_hasher(capacity.get(), hasher);
        inner.insert(value);
        NEIndexSet { inner }
    }

    /// See [`IndexSet::with_hasher`].
    #[must_use]
    pub fn with_hasher(hasher: S, value: T) -> NEIndexSet<T, S> {
        let mut inner = IndexSet::with_hasher(hasher);
        inner.insert(value);
        NEIndexSet { inner }
    }
}

impl<T, S> AsRef<IndexSet<T, S>> for NEIndexSet<T, S> {
    fn as_ref(&self) -> &IndexSet<T, S> {
        &self.inner
    }
}

impl<T, S> AsMut<IndexSet<T, S>> for NEIndexSet<T, S> {
    fn as_mut(&mut self) -> &mut IndexSet<T, S> {
        &mut self.inner
    }
}

impl<T, S> PartialEq for NEIndexSet<T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
    /// ```
    /// use nonempty_collections::ne_indexset;
    ///
    /// let s0 = ne_indexset![1, 2, 3];
    /// let s1 = ne_indexset![1, 2, 3];
    /// let s2 = ne_indexset![1, 2];
    /// let s3 = ne_indexset![1, 2, 3, 4];
    ///
    /// assert!(s0 == s1);
    /// assert!(s0 != s2);
    /// assert!(s0 != s3);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.intersection(other).count() == self.len().get()
    }
}

impl<T, S> Eq for NEIndexSet<T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
}

impl<T, S> IntoNonEmptyIterator for NEIndexSet<T, S> {
    type IntoNEIter = IntoIter<T>;

    fn into_nonempty_iter(self) -> Self::IntoNEIter {
        IntoIter {
            iter: self.inner.into_iter(),
        }
    }
}

impl<'a, T, S> IntoNonEmptyIterator for &'a NEIndexSet<T, S> {
    type IntoNEIter = Iter<'a, T>;

    fn into_nonempty_iter(self) -> Self::IntoNEIter {
        self.nonempty_iter()
    }
}

impl<T, S> IntoIterator for NEIndexSet<T, S> {
    type Item = T;

    type IntoIter = indexmap::set::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.into_iter()
    }
}

impl<'a, T, S> IntoIterator for &'a NEIndexSet<T, S> {
    type Item = &'a T;

    type IntoIter = indexmap::set::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// ```
/// use nonempty_collections::*;
///
/// let s0 = ne_indexset![1, 2, 3];
/// let s1: NEIndexSet<_> = s0.nonempty_iter().cloned().collect();
/// assert_eq!(s0, s1);
/// ```
impl<T, S> FromNonEmptyIterator<T> for NEIndexSet<T, S>
where
    T: Eq + Hash,
    S: BuildHasher + Default,
{
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let v = nev![1, 1, 2, 3, 2];
    /// let s = NEIndexSet::from_nonempty_iter(v);
    ///
    /// assert_eq!(ne_indexset![1, 2, 3], s);
    /// ```
    fn from_nonempty_iter<I>(iter: I) -> Self
    where
        I: IntoNonEmptyIterator<Item = T>,
    {
        NEIndexSet {
            inner: iter.into_nonempty_iter().into_iter().collect(),
        }
    }
}

/// A non-empty iterator over the values of an [`NEIndexSet`].
#[must_use = "non-empty iterators are lazy and do nothing unless consumed"]
pub struct Iter<'a, T: 'a> {
    iter: indexmap::set::Iter<'a, T>,
}

impl<'a, T: 'a> IntoIterator for Iter<'a, T> {
    type Item = &'a T;

    type IntoIter = indexmap::set::Iter<'a, T>;

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

/// An owned non-empty iterator over the values of an [`NEIndexSet`].
#[must_use = "non-empty iterators are lazy and do nothing unless consumed"]
pub struct IntoIter<T> {
    iter: indexmap::set::IntoIter<T>,
}

impl<T> IntoIterator for IntoIter<T> {
    type Item = T;

    type IntoIter = indexmap::set::IntoIter<T>;

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

/// A non-empty iterator producing elements in the union of two [`NEIndexSet`]s.
#[must_use = "non-empty iterators are lazy and do nothing unless consumed"]
pub struct Union<'a, T: 'a, S: 'a> {
    inner: indexmap::set::Union<'a, T, S>,
}

impl<'a, T, S> IntoIterator for Union<'a, T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
    type Item = &'a T;

    type IntoIter = indexmap::set::Union<'a, T, S>;

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

impl<T, S> From<NEIndexSet<T, S>> for IndexSet<T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
    /// ```
    /// use indexmap::set::IndexSet;
    ///
    /// use nonempty_collections::ne_indexset;
    ///
    /// let s: IndexSet<_> = ne_indexset![1, 2, 3].into();
    /// let mut v: Vec<_> = s.into_iter().collect();
    /// v.sort();
    /// assert_eq!(vec![1, 2, 3], v);
    /// ```
    fn from(s: NEIndexSet<T, S>) -> Self {
        s.inner
    }
}

impl<T: fmt::Debug, S> fmt::Debug for NEIndexSet<T, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl<T, S> TryFrom<IndexSet<T, S>> for NEIndexSet<T, S>
where
    T: Eq + Hash,
    S: BuildHasher + Default,
{
    type Error = crate::Error;

    fn try_from(set: IndexSet<T, S>) -> Result<Self, Self::Error> {
        let ne = set
            .try_into_nonempty_iter()
            .ok_or(crate::Error::Empty)?
            .collect();

        Ok(ne)
    }
}

impl<T> Singleton for NEIndexSet<T>
where
    T: Eq + Hash,
{
    type Item = T;

    /// ```
    /// use nonempty_collections::{NEIndexSet, Singleton, ne_indexset};
    ///
    /// let s = NEIndexSet::singleton(1);
    /// assert_eq!(ne_indexset![1], s);
    /// ```
    fn singleton(item: Self::Item) -> Self {
        NEIndexSet::new(item)
    }
}

impl<T> Extend<T> for NEIndexSet<T>
where
    T: Eq + Hash,
{
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.inner.extend(iter);
    }
}

#[cfg(feature = "schemars")]
impl<T: JsonSchema> JsonSchema for super::NEIndexSet<T> {
    fn schema_name() -> Cow<'static, str> {
        IndexSet::<T>::schema_name()
    }

    fn json_schema(generator: &mut SchemaGenerator) -> Schema {
        let mut schema = IndexSet::<T>::json_schema(generator);

        if let Some(schema_object) = schema.as_object_mut()
            && schema_object["type"] == "array"
        {
            schema_object.insert("minItems".to_string(), 1.into());
        }

        schema
    }

    fn inline_schema() -> bool {
        IndexSet::<T>::inline_schema()
    }
}

#[cfg(test)]
mod test {
    use maplit::hashset;

    #[test]
    fn debug_impl() {
        let expected = format!("{:?}", hashset! {0});
        let actual = format!("{:?}", ne_indexset! {0});
        assert_eq!(expected, actual);
    }

    #[test]
    fn iter_debug_impl() {
        let expected = format!("{:?}", hashset! {0}.iter());
        let actual = format!("{:?}", ne_indexset! {0}.nonempty_iter());
        assert_eq!(expected, actual);
    }
}

#[cfg(feature = "serde")]
#[cfg(test)]
mod serde_tests {
    use crate::NEIndexSet;
    #[allow(unused)]
    use crate::ne_indexset;
    use indexmap::set::IndexSet;

    #[test]
    fn json() {
        let set0 = ne_indexset![1, 1, 2, 3, 2, 1, 4];
        let j = serde_json::to_string(&set0).unwrap();
        let set1 = serde_json::from_str(&j).unwrap();
        assert_eq!(set0, set1);

        let empty: IndexSet<usize> = IndexSet::new();
        let j = serde_json::to_string(&empty).unwrap();
        let bad = serde_json::from_str::<NEIndexSet<usize>>(&j);
        assert!(bad.is_err());
    }
}

#[cfg(feature = "schemars")]
#[cfg(test)]
mod schemars_tests {
    use super::{IndexSet, NEIndexSet};
    use schemars::schema_for;

    #[test]
    fn test_simple_schema() {
        let actual = schema_for!(NEIndexSet<i32>).to_value();

        let mut expected = schema_for!(IndexSet<i32>).to_value();
        expected["minItems"] = 1.into();

        assert_eq!(expected, actual);
    }
}
