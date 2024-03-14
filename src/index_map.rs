//! [`NEIndexMap`] is a non-empty variant of [`IndexMap`].
//!
//! Unlike `HashMap` and [`crate::NEMap`], these feature a predictable iteration
//! order.

#![deny(clippy::correctness, clippy::suspicious)]
#![warn(clippy::complexity, clippy::perf, clippy::style, clippy::pedantic)]
#![allow(clippy::module_name_repetitions)]
use std::fmt;
use std::fmt::Debug;
use std::fmt::Formatter;
use std::hash::BuildHasher;
use std::hash::Hash;
use std::mem;

use crate::FromNonEmptyIterator;
use crate::IntoNonEmptyIterator;
use crate::NonEmptyIterator;
use indexmap::Equivalent;
use indexmap::IndexMap;
use std::num::NonZeroUsize;

/// Short-hand for constructing [`NEIndexMap`] values.
///
/// ```
/// use nonempty_collections::ne_indexmap;
///
/// let m = ne_indexmap!{"elves" => 3000, "orcs" => 10000};
/// assert_eq!(2, m.len());
/// ```
#[macro_export]
macro_rules! ne_indexmap {
    ($hk:expr => $hv:expr, $( $xk:expr => $xv:expr,)+) => { $crate::ne_indexmap!{$hk => $hv, $($xk => $xv),+} };
    ($hk:expr => $hv:expr, $( $xk:expr => $xv:expr ),*) => {{
        const CAP: usize = <[()]>::len(&[$({ stringify!($xk); }),*]);
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
/// let m = ne_indexmap!{"Netherlands" => 18, "Canada" => 40};
/// assert_eq!(2, m.len());
/// ```
#[derive(Clone)]
pub struct NEIndexMap<K, V, S = std::collections::hash_map::RandomState> {
    /// The key of the ever-present element of the non-empty `IndexMap`.
    head_key: K,

    /// The value of the ever-present element of the non-empty `IndexMap`.
    head_val: V,

    /// The remaining key-value pairs, perhaps empty.
    tail: IndexMap<K, V, S>,
}

impl<K, V, S> NEIndexMap<K, V, S> {
    /// Returns the number of elements the map can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.tail.capacity() + 1
    }

    /// Returns a reference to the map's `BuildHasher`.
    pub fn hasher(&self) -> &S {
        self.tail.hasher()
    }

    /// An iterator visiting all elements in their order.
    #[allow(clippy::iter_not_returning_iterator)]
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            head_key: &self.head_key,
            head_val: &self.head_val,
            iter: std::iter::once((&self.head_key, &self.head_val)).chain(self.tail.iter()),
        }
    }

    /// An iterator visiting all elements in their order.
    #[allow(clippy::iter_not_returning_iterator)]
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut {
            iter: std::iter::once((&self.head_key, &mut self.head_val)).chain(self.tail.iter_mut()),
        }
    }

    /// An iterator visiting all keys in arbitrary order. The iterator element
    /// type is `&'a K`.
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let m = ne_indexmap!{"Duke" => "Leto", "Doctor" => "Yueh", "Planetologist" => "Kynes"};
    /// let v = m.keys().collect::<NEVec<_>>();
    /// assert_eq!(nev![&"Duke", &"Doctor", &"Planetologist"], v);
    /// ```
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys {
            head_key: &self.head_key,
            inner: std::iter::once(&self.head_key).chain(self.tail.keys()),
        }
    }

    /// Returns the number of elements in the map. Always 1 or more.
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let m = ne_indexmap!{"a" => 1, "b" => 2};
    /// assert_eq!(2, m.len());
    /// ```
    pub fn len(&self) -> NonZeroUsize {
        NonZeroUsize::MIN.saturating_add(self.tail.len())
    }

    /// A `NEIndexMap` is never empty.
    #[deprecated(note = "A NEIndexMap is never empty.")]
    #[allow(clippy::unused_self)]
    pub const fn is_empty(&self) -> bool {
        false
    }

    /// An iterator visiting all values in order.
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let m = ne_indexmap!["Caladan" => "Atreides", "Giedi Prime" => "Harkonnen", "Kaitain" => "Corrino"];
    /// assert_eq!(vec![&"Atreides", &"Harkonnen", &"Corrino"], m.values().collect::<Vec<_>>());
    /// ```
    pub fn values(&self) -> Values<'_, K, V> {
        Values {
            head_val: &self.head_val,
            inner: std::iter::once(&self.head_val).chain(self.tail.values()),
        }
    }

    /// Return an iterator visiting all mutable values in order.
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let mut m = ne_indexmap![0 => "Fremen".to_string(), 1 => "Crysknife".to_string(), 2 => "Water of Life".to_string()];
    /// m.values_mut().into_iter().for_each(|v| v.truncate(3));
    ///
    /// assert_eq!(vec![&mut "Fre".to_string(), &mut "Cry".to_string(),&mut "Wat".to_string()], m.values_mut().collect::<Vec<_>>());
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        ValuesMut {
            inner: std::iter::once(&mut self.head_val).chain(self.tail.values_mut()),
        }
    }

    /// Get the first element. Never fails.
    pub const fn first(&self) -> (&K, &V) {
        (&self.head_key, &self.head_val)
    }

    /// Get the last element. Never fails.
    pub fn last(&self) -> (&K, &V) {
        match self.tail.last() {
            None => (&self.head_key, &self.head_val),
            Some(e) => e,
        }
    }
}

impl<K: Debug, V: Debug, S> Debug for NEIndexMap<K, V, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K, V> NEIndexMap<K, V> {
    /// Creates a new `NEMap` with a single element.
    pub fn new(k: K, v: V) -> Self {
        Self {
            head_key: k,
            head_val: v,
            tail: IndexMap::default(),
        }
    }

    /// Creates a new `NEIndexMap` with a single element and specified capacity.
    pub fn with_capacity(capacity: usize, k: K, v: V) -> NEIndexMap<K, V> {
        Self {
            head_key: k,
            head_val: v,
            tail: IndexMap::with_capacity(capacity),
        }
    }
}

impl<K, V, S> NEIndexMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher,
{
    /// Returns true if the map contains a value.
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let m = ne_indexmap!{"Paul" => ()};
    /// assert!(m.contains_key("Paul"));
    /// assert!(!m.contains_key("Atreides"));
    /// ```
    pub fn contains_key<Q>(&self, k: &Q) -> bool
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        self.tail.contains_key(k) || k.equivalent(&self.head_key)
    }

    /// Return a reference to the value stored for `key`, if it is present,
    /// else `None`.
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let m = ne_indexmap!{"Arrakis" => 3};
    /// assert_eq!(Some(&3), m.get("Arrakis"));
    /// assert_eq!(None, m.get("Caladan"));
    /// ```
    pub fn get<Q>(&self, k: &Q) -> Option<&V>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        self.tail
            .get(k)
            .or_else(|| (k.equivalent(&self.head_key)).then_some(&self.head_val))
    }

    /// Return references to the key-value pair stored for `key`,
    /// if it is present, else `None`.
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let m = ne_indexmap!{"Year" => 1963, "Pages" => 896};
    /// assert_eq!(Some((&"Year", &1963)), m.get_key_value(&"Year"));
    /// assert_eq!(Some((&"Pages", &896)), m.get_key_value(&"Pages"));
    /// assert_eq!(None, m.get_key_value(&"Title"));
    /// ```
    pub fn get_key_value<Q: ?Sized>(&self, key: &Q) -> Option<(&K, &V)>
    where
        Q: Hash + Equivalent<K>,
    {
        if key.equivalent(&self.head_key) {
            Some((&self.head_key, &self.head_val))
        } else {
            self.tail.get_key_value(key)
        }
    }

    /// Return a mutable reference to the value stored for `key`, if it is
    /// present, else `None`.
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let mut m = ne_indexmap!{"Mentat" => 3, "Bene Gesserit" => 14};
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
    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
    where
        Q: Hash + Equivalent<K>,
    {
        if key.equivalent(&self.head_key) {
            Some(&mut self.head_val)
        } else {
            self.tail.get_mut(key)
        }
    }

    /// Return item index, if it exists in the map.
    ///
    /// ```
    /// use nonempty_collections::*;
    /// let m = ne_indexmap!{"Title" => "Dune", "Author" => "Frank Herbert", "Language" => "English"};
    ///
    /// assert_eq!(Some(0), m.get_index_of(&"Title"));
    /// assert_eq!(Some(1), m.get_index_of(&"Author"));
    /// assert_eq!(None, m.get_index_of(&"Genre"));
    /// ````
    pub fn get_index_of<Q: ?Sized>(&self, key: &Q) -> Option<usize>
    where
        Q: Hash + Equivalent<K>,
    {
        if key.equivalent(&self.head_key) {
            Some(0)
        } else {
            self.tail.get_index_of(key).map(|i| i + 1)
        }
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
    /// let mut m = ne_indexmap!{"Duke" => "Leto", "Doctor" => "Yueh"};
    /// assert_eq!(None, m.insert("Lady", "Jessica"));
    /// assert_eq!(vec!["Duke", "Doctor", "Lady"], m.keys().copied().collect::<Vec<_>>());
    ///
    /// // Spoiler alert: there is a different duke at some point
    /// assert_eq!(Some("Leto"), m.insert("Duke", "Paul"));
    /// assert_eq!(vec!["Paul", "Yueh", "Jessica"], m.values().copied().collect::<Vec<_>>());
    /// ```
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        if k.equivalent(&self.head_key) {
            Some(std::mem::replace(&mut self.head_val, v))
        } else {
            self.tail.insert(k, v)
        }
    }

    /// Shrink the capacity of the map as much as possible.
    pub fn shrink_to_fit(&mut self) {
        self.tail.shrink_to_fit();
    }

    /// See [`IndexMap::with_capacity_and_hasher`].
    pub fn with_capacity_and_hasher(capacity: usize, hasher: S, k: K, v: V) -> NEIndexMap<K, V, S> {
        Self {
            head_key: k,
            head_val: v,
            tail: IndexMap::with_capacity_and_hasher(capacity, hasher),
        }
    }

    /// See [`IndexMap::with_hasher`].
    pub fn with_hasher(hasher: S, k: K, v: V) -> NEIndexMap<K, V, S> {
        Self {
            head_key: k,
            head_val: v,
            tail: IndexMap::with_hasher(hasher),
        }
    }

    /// Swaps the position of two key-value pairs in the map.
    ///
    /// # Panics
    /// If `a` or `b` are out of bounds.
    #[allow(clippy::panic)]
    pub fn swap_indices(&mut self, mut a: usize, mut b: usize) {
        if a == b && a < self.len().get() {
            return;
        }
        if b == 0 {
            b = a;
            a = 0;
        }

        if a == 0 {
            b -= 1;
            let (existing_k, existing_v) = self
                .tail
                .swap_remove_index(b)
                .unwrap_or_else(|| panic!("Index out of bounds {b}"));

            let old_head_key = mem::replace(&mut self.head_key, existing_k);
            let old_head_value = mem::replace(&mut self.head_val, existing_v);

            let (index, _) = self.tail.insert_full(old_head_key, old_head_value);
            // swap the newly inserted item to the original position
            self.tail.swap_indices(index, b);
        } else {
            self.tail.swap_indices(a - 1, b - 1);
        }
    }
}

impl<K, V, S> PartialEq for NEIndexMap<K, V, S>
where
    K: Eq + Hash,
    V: Eq,
    S: BuildHasher,
{
    fn eq(&self, other: &Self) -> bool {
        self.iter()
            .all(|(k, v)| other.get(k).is_some_and(|ov| v == ov))
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
    /// use nonempty_collections::*;
    /// use indexmap::IndexMap;
    ///
    /// let m: IndexMap<&str, usize> = ne_indexmap!{"population" => 1000}.into();
    /// assert!(m.contains_key("population"));
    /// ```
    fn from(m: NEIndexMap<K, V, S>) -> Self {
        let mut map = m.tail;
        map.shift_insert(0, m.head_key, m.head_val);
        map
    }
}

impl<K, V, S> IntoNonEmptyIterator for NEIndexMap<K, V, S> {
    type Item = (K, V);

    type IntoIter = crate::iter::Chain<crate::iter::Once<(K, V)>, indexmap::map::IntoIter<K, V>>;

    fn into_nonempty_iter(self) -> Self::IntoIter {
        crate::iter::once((self.head_key, self.head_val)).chain(self.tail)
    }
}

/// ```
/// use nonempty_collections::*;
///
/// let v = nev![('a', 1), ('b', 2), ('c', 3)];
/// let m0 = v.into_nonempty_iter().collect::<NEIndexMap<_, _>>();
/// let m1 = ne_indexmap!{'a' => 1, 'b' => 2, 'c' => 3};
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
        let ((head_key, head_val), rest) = iter.into_nonempty_iter().first();

        Self {
            head_key,
            head_val,
            tail: rest.into_iter().collect(),
        }
    }
}

impl<K, V> std::ops::Index<usize> for NEIndexMap<K, V> {
    type Output = V;

    fn index(&self, index: usize) -> &V {
        if index > 0 {
            &self.tail[index - 1]
        } else {
            &self.head_val
        }
    }
}

/// A non-empty iterator over the entries of an [`NEIndexMap`].
pub struct Iter<'a, K: 'a, V: 'a> {
    head_key: &'a K,
    head_val: &'a V,
    iter: std::iter::Chain<std::iter::Once<(&'a K, &'a V)>, indexmap::map::Iter<'a, K, V>>,
}

impl<'a, K, V> NonEmptyIterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    type IntoIter = std::iter::Skip<
        std::iter::Chain<std::iter::Once<(&'a K, &'a V)>, indexmap::map::Iter<'a, K, V>>,
    >;

    fn first(self) -> (Self::Item, Self::IntoIter) {
        ((self.head_key, self.head_val), self.iter.skip(1))
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

impl<'a, K, V> IntoIterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    type IntoIter =
        std::iter::Chain<std::iter::Once<(&'a K, &'a V)>, indexmap::map::Iter<'a, K, V>>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter
    }
}

// FIXME(#26925) Remove in favor of `#[derive(Clone)]` (see https://github.com/rust-lang/rust/issues/26925 for more info)
impl<K, V> Clone for Iter<'_, K, V> {
    fn clone(&self) -> Self {
        Iter {
            head_key: self.head_key,
            head_val: self.head_val,
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
pub struct IterMut<'a, K: 'a, V: 'a> {
    iter: std::iter::Chain<std::iter::Once<(&'a K, &'a mut V)>, indexmap::map::IterMut<'a, K, V>>,
}

impl<'a, K, V> NonEmptyIterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    type IntoIter =
        std::iter::Chain<std::iter::Once<(&'a K, &'a mut V)>, indexmap::map::IterMut<'a, K, V>>;

    fn first(mut self) -> (Self::Item, Self::IntoIter) {
        let (key, val) = self.iter.next().unwrap();
        ((key, val), self.iter)
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

impl<'a, K, V> IntoIterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    type IntoIter =
        std::iter::Chain<std::iter::Once<(&'a K, &'a mut V)>, indexmap::map::IterMut<'a, K, V>>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter
    }
}

/// A non-empty iterator over the keys of an [`NEIndexMap`].
///
/// ```
/// use nonempty_collections::*;
///
/// let m = ne_indexmap!{"elves" => 3000, "orcs" => 10000};
/// let v = m.keys().copied().collect::<NEVec<_>>();
/// assert_eq!(nev!["elves", "orcs"], v);
/// ```
pub struct Keys<'a, K: 'a, V: 'a> {
    head_key: &'a K,
    inner: std::iter::Chain<std::iter::Once<&'a K>, indexmap::map::Keys<'a, K, V>>,
}

impl<'a, K, V> NonEmptyIterator for Keys<'a, K, V> {
    type Item = &'a K;

    type IntoIter =
        std::iter::Skip<std::iter::Chain<std::iter::Once<&'a K>, indexmap::map::Keys<'a, K, V>>>;

    fn first(self) -> (Self::Item, Self::IntoIter) {
        (self.head_key, self.inner.skip(1))
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

impl<'a, K, V> IntoIterator for Keys<'a, K, V> {
    type Item = &'a K;

    type IntoIter = std::iter::Chain<std::iter::Once<&'a K>, indexmap::map::Keys<'a, K, V>>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner
    }
}

// FIXME(#26925) Remove in favor of `#[derive(Clone)]` (see https://github.com/rust-lang/rust/issues/26925 for more info)
impl<K, V> Clone for Keys<'_, K, V> {
    fn clone(&self) -> Self {
        Keys {
            head_key: self.head_key,
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
/// let m = ne_indexmap!{"elves" => 3000, "orcs" => 10000};
/// let mut v = m.values().copied().collect::<NEVec<_>>();
/// v.sort();
/// assert_eq!(nev![3000, 10000], v);
/// ```
pub struct Values<'a, K: 'a, V: 'a> {
    head_val: &'a V,
    inner: std::iter::Chain<std::iter::Once<&'a V>, indexmap::map::Values<'a, K, V>>,
}

impl<'a, K, V> NonEmptyIterator for Values<'a, K, V> {
    type Item = &'a V;

    type IntoIter =
        std::iter::Skip<std::iter::Chain<std::iter::Once<&'a V>, indexmap::map::Values<'a, K, V>>>;

    fn first(self) -> (Self::Item, Self::IntoIter) {
        (self.head_val, self.inner.skip(1))
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

impl<'a, K, V> IntoIterator for Values<'a, K, V> {
    type Item = &'a V;

    type IntoIter = std::iter::Chain<std::iter::Once<&'a V>, indexmap::map::Values<'a, K, V>>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner
    }
}

// FIXME(#26925) Remove in favor of `#[derive(Clone)]` (see https://github.com/rust-lang/rust/issues/26925 for more info)
impl<K, V> Clone for Values<'_, K, V> {
    fn clone(&self) -> Self {
        Values {
            head_val: self.head_val,
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
pub struct ValuesMut<'a, K: 'a, V: 'a> {
    inner: std::iter::Chain<std::iter::Once<&'a mut V>, indexmap::map::ValuesMut<'a, K, V>>,
}

impl<'a, K, V> NonEmptyIterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;

    type IntoIter =
        std::iter::Chain<std::iter::Once<&'a mut V>, indexmap::map::ValuesMut<'a, K, V>>;

    fn first(mut self) -> (Self::Item, Self::IntoIter) {
        let value = self.inner.next().unwrap();
        (value, self.inner)
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

impl<'a, K, V> IntoIterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;

    type IntoIter =
        std::iter::Chain<std::iter::Once<&'a mut V>, indexmap::map::ValuesMut<'a, K, V>>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_swap_indices() {
        let mut map = ne_indexmap! { 0 => (), 1 => () };
        assert_eq!(vec![0, 1], map.keys().copied().collect::<Vec<_>>());
        map.swap_indices(0, 1);
        assert_eq!(vec![1, 0], map.keys().copied().collect::<Vec<_>>());
        map.swap_indices(1, 0);
        assert_eq!(vec![0, 1], map.keys().copied().collect::<Vec<_>>());

        let mut map = ne_indexmap! { 0 => (), 1 => (), 2 => () };
        assert_eq!(vec![0, 1, 2], map.keys().copied().collect::<Vec<_>>());
        map.swap_indices(0, 1);
        assert_eq!(vec![1, 0, 2], map.keys().copied().collect::<Vec<_>>());
        map.swap_indices(1, 0);
        assert_eq!(vec![0, 1, 2], map.keys().copied().collect::<Vec<_>>());
        map.swap_indices(0, 2);
        assert_eq!(vec![2, 1, 0], map.keys().copied().collect::<Vec<_>>());
        map.swap_indices(1, 2);
        assert_eq!(vec![2, 0, 1], map.keys().copied().collect::<Vec<_>>());

        let mut map = ne_indexmap! { 0 => (), 1 => (), 2 => (), 3 => (), 4 => (), 5 => () };
        assert_eq!(
            vec![0, 1, 2, 3, 4, 5],
            map.keys().copied().collect::<Vec<_>>()
        );
        map.swap_indices(1, 2);
        assert_eq!(
            vec![0, 2, 1, 3, 4, 5],
            map.keys().copied().collect::<Vec<_>>()
        );
        map.swap_indices(0, 3);
        assert_eq!(
            vec![3, 2, 1, 0, 4, 5],
            map.keys().copied().collect::<Vec<_>>()
        );
    }
}
