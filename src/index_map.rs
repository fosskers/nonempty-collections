//! [`NEIndexMap`] is a non-empty variant of [`IndexMap`].
//!
//! Unlike `HashMap` and [`crate::NEMap`], these feature a predictable iteration
//! order.

use std::fmt;
use std::fmt::Debug;
use std::fmt::Formatter;
use std::hash::BuildHasher;
use std::hash::Hash;
use std::num::NonZeroUsize;

use indexmap::indexmap;
use indexmap::Equivalent;
use indexmap::IndexMap;

use crate::FromNonEmptyIterator;
use crate::IntoNonEmptyIterator;
use crate::NonEmptyIterator;

/// Short-hand for constructing [`NEIndexMap`] values.
///
/// ```
/// use nonempty_collections::ne_indexmap;
///
/// let m = ne_indexmap! {"elves" => 3000, "orcs" => 10000};
/// assert_eq!(2, m.len().get());
/// ```
#[macro_export]
macro_rules! ne_indexmap {
    ($hk:expr => $hv:expr, $( $xk:expr => $xv:expr,)+) => { $crate::ne_indexmap!{$hk => $hv, $($xk => $xv),+} };
    ($hk:expr => $hv:expr, $( $xk:expr => $xv:expr ),*) => {{
        const CAP: core::num::NonZeroUsize = core::num::NonZeroUsize::MIN.saturating_add(<[()]>::len(&[$({ stringify!($xk); }),*]));
        let mut map = $crate::index_map::NEIndexMap::with_capacity(CAP, $hk, $hv);
        $( map.insert($xk, $xv); )*
        map
    }};
    ($hk:expr => $hv:expr) => {
        $crate::index_map::NEIndexMap::new($hk, $hv)
    }
}

/// A non-empty, growable [`IndexMap`].
///
/// Unlike `HashMap` and [`crate::NEMap`], these feature a predictable iteration
/// order.
///
/// ```
/// use nonempty_collections::*;
///
/// let m = ne_indexmap! {"Netherlands" => 18, "Canada" => 40};
/// assert_eq!(2, m.len().get());
/// ```
#[derive(Clone)]
pub struct NEIndexMap<K, V, S = std::collections::hash_map::RandomState> {
    inner: IndexMap<K, V, S>,
}

impl<K, V, S> NEIndexMap<K, V, S> {
    /// Returns the number of elements the map can hold without reallocating.
    #[must_use]
    pub fn capacity(&self) -> NonZeroUsize {
        unsafe { NonZeroUsize::new_unchecked(self.inner.capacity()) }
    }

    /// Returns a reference to the map's `BuildHasher`.
    #[must_use]
    pub fn hasher(&self) -> &S {
        self.inner.hasher()
    }

    /// Returns a regular iterator over the values in this non-empty index map.
    ///
    /// For a `NonEmptyIterator` see `Self::nonempty_iter()`.
    pub fn iter(&self) -> indexmap::map::Iter<'_, K, V> {
        self.inner.iter()
    }

    /// An iterator visiting all elements in their order.
    pub fn nonempty_iter(&self) -> Iter<'_, K, V> {
        Iter {
            iter: self.inner.iter(),
        }
    }

    /// An iterator visiting all elements in their order.
    pub fn nonempty_iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut {
            iter: self.inner.iter_mut(),
        }
    }

    /// An iterator visiting all keys in arbitrary order. The iterator element
    /// type is `&'a K`.
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let m = ne_indexmap! {"Duke" => "Leto", "Doctor" => "Yueh", "Planetologist" => "Kynes"};
    /// let v = m.nonempty_keys().collect::<NEVec<_>>();
    /// assert_eq!(nev![&"Duke", &"Doctor", &"Planetologist"], v);
    /// ```
    pub fn nonempty_keys(&self) -> Keys<'_, K, V> {
        Keys {
            inner: self.inner.keys(),
        }
    }

    /// Returns the number of elements in the map. Always 1 or more.
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let m = ne_indexmap! {"a" => 1, "b" => 2};
    /// assert_eq!(2, m.len().get());
    /// ```
    #[must_use]
    pub fn len(&self) -> NonZeroUsize {
        unsafe { NonZeroUsize::new_unchecked(self.inner.len()) }
    }

    /// A `NEIndexMap` is never empty.
    #[deprecated(note = "A NEIndexMap is never empty.")]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        false
    }

    /// An iterator visiting all values in order.
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let m = ne_indexmap!["Caladan" => "Atreides", "Giedi Prime" => "Harkonnen", "Kaitain" => "Corrino"];
    /// assert_eq!(vec![&"Atreides", &"Harkonnen", &"Corrino"], m.nonempty_values().collect::<Vec<_>>());
    /// ```
    pub fn nonempty_values(&self) -> Values<'_, K, V> {
        Values {
            inner: self.inner.values(),
        }
    }

    /// Return an iterator visiting all mutable values in order.
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let mut m = ne_indexmap![0 => "Fremen".to_string(), 1 => "Crysknife".to_string(), 2 => "Water of Life".to_string()];
    /// m.nonempty_values_mut().into_iter().for_each(|v| v.truncate(3));
    ///
    /// assert_eq!(vec![&mut "Fre".to_string(), &mut "Cry".to_string(),&mut "Wat".to_string()], m.nonempty_values_mut().collect::<Vec<_>>());
    /// ```
    pub fn nonempty_values_mut(&mut self) -> ValuesMut<'_, K, V> {
        ValuesMut {
            inner: self.inner.values_mut(),
        }
    }

    /// Get the first element. Never fails.
    #[allow(clippy::missing_panics_doc)] // the invariant of NEIndexMap is that its non-empty
    #[must_use]
    pub fn first(&self) -> (&K, &V) {
        self.inner.first().unwrap()
    }

    /// Get the last element. Never fails.
    #[allow(clippy::missing_panics_doc)] // the invariant of NEIndexMap is that its non-empty
    #[must_use]
    pub fn last(&self) -> (&K, &V) {
        self.inner.last().unwrap()
    }
}

impl<K: Debug, V: Debug, S> Debug for NEIndexMap<K, V, S> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.nonempty_iter()).finish()
    }
}

impl<K, V> NEIndexMap<K, V>
where
    K: Eq + Hash,
{
    /// Creates a new `NEIndexMap` with a single element.
    #[must_use]
    pub fn new(k: K, v: V) -> Self {
        Self {
            inner: indexmap! {k => v},
        }
    }

    /// Creates a new `NEIndexMap` with a single element and specified
    /// heap capacity.
    #[must_use]
    pub fn with_capacity(capacity: NonZeroUsize, k: K, v: V) -> NEIndexMap<K, V> {
        let mut inner = IndexMap::with_capacity(capacity.get());
        inner.insert(k, v);
        Self { inner }
    }
}

impl<K, V, S> NEIndexMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher,
{
    /// Attempt a conversion from [`IndexMap`], consuming the given `IndexMap`.
    /// Will return `None` if the `IndexMap` is empty.
    ///
    /// ```
    /// use indexmap::*;
    /// use nonempty_collections::*;
    ///
    /// assert_eq!(
    ///     Some(ne_indexmap! {"a" => 1, "b" => 2}),
    ///     NEIndexMap::try_from_map(indexmap! {"a" => 1, "b" => 2})
    /// );
    /// let m: IndexMap<(), ()> = indexmap! {};
    /// assert_eq!(None, NEIndexMap::try_from_map(m));
    /// ```
    #[must_use]
    pub fn try_from_map(map: IndexMap<K, V, S>) -> Option<Self> {
        if map.is_empty() {
            None
        } else {
            Some(Self { inner: map })
        }
    }

    /// Returns true if the map contains a value.
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let m = ne_indexmap! {"Paul" => ()};
    /// assert!(m.contains_key("Paul"));
    /// assert!(!m.contains_key("Atreides"));
    /// ```
    #[must_use]
    pub fn contains_key<Q>(&self, k: &Q) -> bool
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        self.inner.contains_key(k)
    }

    /// Return a reference to the value stored for `key`, if it is present,
    /// else `None`.
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let m = ne_indexmap! {"Arrakis" => 3};
    /// assert_eq!(Some(&3), m.get("Arrakis"));
    /// assert_eq!(None, m.get("Caladan"));
    /// ```
    #[must_use]
    pub fn get<Q>(&self, k: &Q) -> Option<&V>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        self.inner.get(k)
    }

    /// Return references to the key-value pair stored for `key`,
    /// if it is present, else `None`.
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let m = ne_indexmap! {"Year" => 1963, "Pages" => 896};
    /// assert_eq!(Some((&"Year", &1963)), m.get_key_value(&"Year"));
    /// assert_eq!(Some((&"Pages", &896)), m.get_key_value(&"Pages"));
    /// assert_eq!(None, m.get_key_value(&"Title"));
    /// ```
    #[must_use]
    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        self.inner.get_key_value(key)
    }

    /// Return a mutable reference to the value stored for `key`, if it is
    /// present, else `None`.
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let mut m = ne_indexmap! {"Mentat" => 3, "Bene Gesserit" => 14};
    /// let v = m.get_mut(&"Mentat");
    /// assert_eq!(Some(&mut 3), v);
    /// *v.unwrap() += 1;
    /// assert_eq!(Some(&mut 4), m.get_mut(&"Mentat"));
    ///
    /// let v = m.get_mut(&"Bene Gesserit");
    /// assert_eq!(Some(&mut 14), v);
    /// *v.unwrap() -= 1;
    /// assert_eq!(Some(&mut 13), m.get_mut(&"Bene Gesserit"));
    ///
    /// assert_eq!(None, m.get_mut(&"Sandworm"));
    /// ```
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        self.inner.get_mut(key)
    }

    /// Return item index, if it exists in the map.
    ///
    /// ```
    /// use nonempty_collections::*;
    /// let m = ne_indexmap! {"Title" => "Dune", "Author" => "Frank Herbert", "Language" => "English"};
    ///
    /// assert_eq!(Some(0), m.get_index_of(&"Title"));
    /// assert_eq!(Some(1), m.get_index_of(&"Author"));
    /// assert_eq!(None, m.get_index_of(&"Genre"));
    /// ````
    #[must_use]
    pub fn get_index_of<Q>(&self, key: &Q) -> Option<usize>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        self.inner.get_index_of(key)
    }

    /// Insert a key-value pair into the map.
    ///
    /// If an equivalent key already exists in the map: the key remains and
    /// retains in its place in the order, its corresponding value is updated
    /// with `value`, and the older value is returned inside `Some(_)`.
    ///
    /// If no equivalent key existed in the map: the new key-value pair is
    /// inserted, last in order, and `None` is returned.
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let mut m = ne_indexmap! {"Duke" => "Leto", "Doctor" => "Yueh"};
    /// assert_eq!(None, m.insert("Lady", "Jessica"));
    /// assert_eq!(
    ///     vec!["Duke", "Doctor", "Lady"],
    ///     m.nonempty_keys().copied().collect::<Vec<_>>()
    /// );
    ///
    /// // Spoiler alert: there is a different duke at some point
    /// assert_eq!(Some("Leto"), m.insert("Duke", "Paul"));
    /// assert_eq!(
    ///     vec!["Paul", "Yueh", "Jessica"],
    ///     m.nonempty_values().copied().collect::<Vec<_>>()
    /// );
    /// ```
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        self.inner.insert(k, v)
    }

    /// Shrink the capacity of the map as much as possible.
    pub fn shrink_to_fit(&mut self) {
        self.inner.shrink_to_fit();
    }

    /// Creates a new `NEIndexMap` with a single element and specified
    /// heap capacity and hasher.
    #[must_use]
    pub fn with_capacity_and_hasher(
        capacity: NonZeroUsize,
        hasher: S,
        k: K,
        v: V,
    ) -> NEIndexMap<K, V, S> {
        let mut inner = IndexMap::with_capacity_and_hasher(capacity.get(), hasher);
        inner.insert(k, v);
        Self { inner }
    }

    /// See [`IndexMap::with_hasher`].
    #[must_use]
    pub fn with_hasher(hasher: S, k: K, v: V) -> NEIndexMap<K, V, S> {
        let mut inner = IndexMap::with_hasher(hasher);
        inner.insert(k, v);
        Self { inner }
    }

    /// Swaps the position of two key-value pairs in the map.
    ///
    /// # Panics
    /// If `a` or `b` are out of bounds.
    pub fn swap_indices(&mut self, a: usize, b: usize) {
        self.inner.swap_indices(a, b);
    }
}

impl<K, V, S> PartialEq for NEIndexMap<K, V, S>
where
    K: Eq + Hash,
    V: Eq,
    S: BuildHasher,
{
    fn eq(&self, other: &Self) -> bool {
        self.inner.eq(&other.inner)
    }
}

impl<K, V, S> Eq for NEIndexMap<K, V, S>
where
    K: Eq + Hash,
    V: Eq,
    S: BuildHasher,
{
}

impl<K, V, S> From<NEIndexMap<K, V, S>> for IndexMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher,
{
    /// ```
    /// use indexmap::IndexMap;
    /// use nonempty_collections::*;
    ///
    /// let m: IndexMap<&str, usize> = ne_indexmap! {"population" => 1000}.into();
    /// assert!(m.contains_key("population"));
    /// ```
    fn from(m: NEIndexMap<K, V, S>) -> Self {
        m.inner
    }
}

impl<K, V, S> IntoNonEmptyIterator for NEIndexMap<K, V, S> {
    type IntoNEIter = IntoIter<K, V>;

    fn into_nonempty_iter(self) -> Self::IntoNEIter {
        IntoIter {
            iter: self.inner.into_iter(),
        }
    }
}

impl<'a, K, V, S> IntoNonEmptyIterator for &'a NEIndexMap<K, V, S> {
    type IntoNEIter = Iter<'a, K, V>;

    fn into_nonempty_iter(self) -> Self::IntoNEIter {
        self.nonempty_iter()
    }
}

impl<K, V, S> IntoIterator for NEIndexMap<K, V, S> {
    type Item = (K, V);

    type IntoIter = indexmap::map::IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.into_iter()
    }
}

impl<'a, K, V, S> IntoIterator for &'a NEIndexMap<K, V, S> {
    type Item = (&'a K, &'a V);

    type IntoIter = indexmap::map::Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.iter()
    }
}

/// ```
/// use nonempty_collections::*;
///
/// let v = nev![('a', 1), ('b', 2), ('c', 3), ('a', 4)];
/// let m0 = v.into_nonempty_iter().collect::<NEIndexMap<_, _>>();
/// let m1 = ne_indexmap! {'a' => 4, 'b' => 2, 'c' => 3};
/// assert_eq!(m0, m1);
/// ```
impl<K, V, S> FromNonEmptyIterator<(K, V)> for NEIndexMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher + Default,
{
    fn from_nonempty_iter<I>(iter: I) -> Self
    where
        I: IntoNonEmptyIterator<Item = (K, V)>,
    {
        Self {
            inner: iter.into_nonempty_iter().into_iter().collect(),
        }
    }
}

impl<K, V> std::ops::Index<usize> for NEIndexMap<K, V> {
    type Output = V;

    fn index(&self, index: usize) -> &V {
        self.inner.index(index)
    }
}

/// A non-empty iterator over the entries of an [`NEIndexMap`].
#[must_use = "non-empty iterators are lazy and do nothing unless consumed"]
pub struct Iter<'a, K: 'a, V: 'a> {
    iter: indexmap::map::Iter<'a, K, V>,
}

impl<K, V> NonEmptyIterator for Iter<'_, K, V> {}

impl<'a, K, V> IntoIterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    type IntoIter = indexmap::map::Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter
    }
}

// FIXME(#26925) Remove in favor of `#[derive(Clone)]` (see https://github.com/rust-lang/rust/issues/26925 for more info)
impl<K, V> Clone for Iter<'_, K, V> {
    fn clone(&self) -> Self {
        Iter {
            iter: self.iter.clone(),
        }
    }
}

impl<K: Debug, V: Debug> Debug for Iter<'_, K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// A mutable non-empty iterator over the entries of an [`NEIndexMap`].
#[must_use = "non-empty iterators are lazy and do nothing unless consumed"]
pub struct IterMut<'a, K: 'a, V: 'a> {
    iter: indexmap::map::IterMut<'a, K, V>,
}

impl<K, V> NonEmptyIterator for IterMut<'_, K, V> {}

impl<'a, K, V> IntoIterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    type IntoIter = indexmap::map::IterMut<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter
    }
}

impl<K: Debug, V: Debug> Debug for IterMut<'_, K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.iter.fmt(f)
    }
}

/// A non-empty iterator over the entries of an [`NEIndexMap`].
pub struct IntoIter<K, V> {
    iter: indexmap::map::IntoIter<K, V>,
}

impl<K, V> NonEmptyIterator for IntoIter<K, V> {}

impl<K, V> IntoIterator for IntoIter<K, V> {
    type Item = (K, V);

    type IntoIter = indexmap::map::IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter
    }
}

impl<K: Debug, V: Debug> Debug for IntoIter<K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.iter.fmt(f)
    }
}

/// A non-empty iterator over the keys of an [`NEIndexMap`].
///
/// ```
/// use nonempty_collections::*;
///
/// let m = ne_indexmap! {"elves" => 3000, "orcs" => 10000};
/// let v = m.nonempty_keys().copied().collect::<NEVec<_>>();
/// assert_eq!(nev!["elves", "orcs"], v);
/// ```
#[must_use = "non-empty iterators are lazy and do nothing unless consumed"]
pub struct Keys<'a, K: 'a, V: 'a> {
    inner: indexmap::map::Keys<'a, K, V>,
}

impl<K, V> NonEmptyIterator for Keys<'_, K, V> {}

impl<'a, K, V> IntoIterator for Keys<'a, K, V> {
    type Item = &'a K;

    type IntoIter = indexmap::map::Keys<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner
    }
}

// FIXME(#26925) Remove in favor of `#[derive(Clone)]` (see https://github.com/rust-lang/rust/issues/26925 for more info)
impl<K, V> Clone for Keys<'_, K, V> {
    fn clone(&self) -> Self {
        Keys {
            inner: self.inner.clone(),
        }
    }
}

impl<K: Debug, V: Debug> Debug for Keys<'_, K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// A non-empty iterator over the values of an [`NEIndexMap`].
///
/// ```
/// use nonempty_collections::*;
///
/// let m = ne_indexmap! {"elves" => 3000, "orcs" => 10000};
/// let mut v = m.nonempty_values().copied().collect::<NEVec<_>>();
/// v.sort();
/// assert_eq!(nev![3000, 10000], v);
/// ```
#[must_use = "non-empty iterators are lazy and do nothing unless consumed"]
pub struct Values<'a, K: 'a, V: 'a> {
    inner: indexmap::map::Values<'a, K, V>,
}

impl<K, V> NonEmptyIterator for Values<'_, K, V> {}

impl<'a, K, V> IntoIterator for Values<'a, K, V> {
    type Item = &'a V;

    type IntoIter = indexmap::map::Values<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner
    }
}

// FIXME(#26925) Remove in favor of `#[derive(Clone)]` (see https://github.com/rust-lang/rust/issues/26925 for more info)
impl<K, V> Clone for Values<'_, K, V> {
    fn clone(&self) -> Self {
        Values {
            inner: self.inner.clone(),
        }
    }
}

impl<K: Debug, V: Debug> Debug for Values<'_, K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// A non-empty iterator over the mutable values of an [`NEIndexMap`].
#[must_use = "non-empty iterators are lazy and do nothing unless consumed"]
pub struct ValuesMut<'a, K: 'a, V: 'a> {
    inner: indexmap::map::ValuesMut<'a, K, V>,
}

impl<K, V> NonEmptyIterator for ValuesMut<'_, K, V> {}

impl<'a, K, V> IntoIterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;

    type IntoIter = indexmap::map::ValuesMut<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner
    }
}

impl<K: Debug, V: Debug> Debug for ValuesMut<'_, K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_swap_indices() {
        let mut map = ne_indexmap! { 0 => (), 1 => () };
        assert_eq!(vec![0, 1], map.nonempty_keys().copied().collect::<Vec<_>>());
        map.swap_indices(0, 1);
        assert_eq!(vec![1, 0], map.nonempty_keys().copied().collect::<Vec<_>>());
        map.swap_indices(1, 0);
        assert_eq!(vec![0, 1], map.nonempty_keys().copied().collect::<Vec<_>>());

        let mut map = ne_indexmap! { 0 => (), 1 => (), 2 => () };
        assert_eq!(
            vec![0, 1, 2],
            map.nonempty_keys().copied().collect::<Vec<_>>()
        );
        map.swap_indices(0, 1);
        assert_eq!(
            vec![1, 0, 2],
            map.nonempty_keys().copied().collect::<Vec<_>>()
        );
        map.swap_indices(1, 0);
        assert_eq!(
            vec![0, 1, 2],
            map.nonempty_keys().copied().collect::<Vec<_>>()
        );
        map.swap_indices(0, 2);
        assert_eq!(
            vec![2, 1, 0],
            map.nonempty_keys().copied().collect::<Vec<_>>()
        );
        map.swap_indices(1, 2);
        assert_eq!(
            vec![2, 0, 1],
            map.nonempty_keys().copied().collect::<Vec<_>>()
        );

        let mut map = ne_indexmap! { 0 => (), 1 => (), 2 => (), 3 => (), 4 => (), 5 => () };
        assert_eq!(
            vec![0, 1, 2, 3, 4, 5],
            map.nonempty_keys().copied().collect::<Vec<_>>()
        );
        map.swap_indices(1, 2);
        assert_eq!(
            vec![0, 2, 1, 3, 4, 5],
            map.nonempty_keys().copied().collect::<Vec<_>>()
        );
        map.swap_indices(0, 3);
        assert_eq!(
            vec![3, 2, 1, 0, 4, 5],
            map.nonempty_keys().copied().collect::<Vec<_>>()
        );
    }

    #[test]
    fn debug_impl() {
        let expected = format!("{:?}", indexmap! {0 => 10, 1 => 11, 2 => 12});
        let actual = format!("{:?}", ne_indexmap! {0 => 10, 1 => 11, 2 => 12});
        assert_eq!(expected, actual);
    }
}
