//! [`NEIndexMap`] is a non-empty variant of [`IndexMap`].
#![deny(clippy::correctness, clippy::suspicious)]
#![warn(clippy::complexity, clippy::perf, clippy::style, clippy::pedantic)]
#![allow(clippy::module_name_repetitions)]
use std::fmt::Debug;
use std::hash::BuildHasher;
use std::hash::Hash;
use std::iter;
use std::mem;

use crate::FromNonEmptyIterator;
use crate::IntoNonEmptyIterator;
use crate::NonEmptyIterator;
use indexmap::Equivalent;
use indexmap::IndexMap;

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

    /// An iterator visiting all elements in arbitrary order. The iterator
    /// element type is `(&'a K, &'a V)`.
    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> + IntoIterator<Item = (&K, &V)> {
        // TODO implement as struct
        iter::once((&self.head_key, &self.head_val)).chain(self.tail.iter())
    }

    // TODO iter_mut

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
    pub fn keys(&self) -> impl NonEmptyIterator<Item = &K> + IntoIterator<Item = &K> {
        crate::iter::once(&self.head_key).chain(self.tail.keys())
    }

    /// Returns the number of elements in the map. Always 1 or more.
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let m = ne_indexmap!{"a" => 1, "b" => 2};
    /// assert_eq!(2, m.len());
    /// ```
    pub fn len(&self) -> usize {
        self.tail.len() + 1
    }

    /// A `NEIndexMap` is never empty.
    #[deprecated(note = "A NEIndexMap is never empty.")]
    #[allow(clippy::unused_self)]
    pub const fn is_empty(&self) -> bool {
        false
    }

    /// `&'a V`.
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let m = ne_indexmap!["Caladan" => "Atreides", "Giedi Prime" => "Harkonnen", "Kaitain" => "Corrino"];
    /// assert_eq!(vec![&"Atreides", &"Harkonnen", &"Corrino"], m.values().collect::<Vec<_>>());
    /// ```
    pub fn values(&self) -> impl NonEmptyIterator<Item = &V> + IntoIterator<Item = &V> {
        crate::iter::once(&self.head_val).chain(self.tail.values())
    }

    // TODO values_mut

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
    /// let m = ne_indexmap! {"Paul" => 8};
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
    /// let m = ne_indexmap!["Arrakis" => 3];
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

    // TODO get_key_value

    // TODO get_mut

    /// Return item index, if it exists in the map
    pub fn get_index_of<Q: ?Sized>(&self, key: &Q) -> Option<usize>
    where
        Q: Hash + Equivalent<K>,
    {
        if key.equivalent(&self.head_key) {
            Some(0)
        } else {
            self.tail.get_index_of(key).map(|i| i - 1)
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
        if a == b && a < self.len() {
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
