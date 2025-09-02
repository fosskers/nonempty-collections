//! Non-empty [`HashMap`]s.

use core::fmt;
use std::borrow::Borrow;
use std::collections::HashMap;
use std::hash::BuildHasher;
use std::hash::Hash;
use std::num::NonZeroUsize;

#[cfg(feature = "serde")]
use serde::Deserialize;
#[cfg(feature = "serde")]
use serde::Serialize;

use crate::FromNonEmptyIterator;
use crate::IntoIteratorExt;
use crate::IntoNonEmptyIterator;
use crate::NonEmptyIterator;

/// Like the [`crate::nev!`] macro, but for Maps. A nice short-hand for
/// constructing [`NEMap`] values.
///
/// ```
/// use nonempty_collections::nem;
///
/// let m = nem! {"elves" => 3000, "orcs" => 10000};
/// assert_eq!(2, m.len().get());
/// ```
#[macro_export]
macro_rules! nem {
    ($hk:expr => $hv:expr, $( $xk:expr => $xv:expr ),* $(,)?) => {{
        let mut map = $crate::NEMap::new($hk, $hv);
        $( map.insert($xk, $xv); )*
        map
    }};
    ($hk:expr => $hv:expr) => {
        $crate::NEMap::new($hk, $hv)
    }
}

/// A non-empty, growable `HashMap`.
///
/// ```
/// use nonempty_collections::nem;
///
/// let m = nem!["elves" => 3000, "orcs" => 10000];
/// assert_eq!(2, m.len().get());
/// ```
#[allow(clippy::unsafe_derive_deserialize)]
#[cfg_attr(
    feature = "serde",
    derive(Deserialize, Serialize),
    serde(bound(
        serialize = "K: Eq + Hash + Clone + Serialize, V: Clone + Serialize, S: Clone + BuildHasher",
        deserialize = "K: Eq + Hash + Clone + Deserialize<'de>, V: Deserialize<'de>, S: Default + BuildHasher"
    )),
    serde(into = "HashMap<K, V, S>", try_from = "HashMap<K, V, S>")
)]
#[derive(Clone)]
pub struct NEMap<K, V, S = std::collections::hash_map::RandomState> {
    inner: HashMap<K, V, S>,
}

impl<K, V> NEMap<K, V>
where
    K: Eq + Hash,
{
    /// Creates a new `NEMap` with a single element.
    #[must_use]
    pub fn new(k: K, v: V) -> NEMap<K, V> {
        let mut inner = HashMap::new();
        inner.insert(k, v);
        NEMap { inner }
    }

    /// Creates a new `NEMap` with a single element and specified capacity.
    /// ```
    /// use std::num::*;
    ///
    /// use nonempty_collections::*;
    /// let map = NEMap::with_capacity(NonZeroUsize::MIN, 1, 1);
    /// assert_eq!(nem! { 1 => 1 }, map);
    /// assert!(map.capacity().get() >= 1);
    /// ```
    #[must_use]
    pub fn with_capacity(capacity: NonZeroUsize, k: K, v: V) -> NEMap<K, V> {
        let mut inner = HashMap::with_capacity(capacity.get());
        inner.insert(k, v);
        NEMap { inner }
    }
}

impl<K, V, S> NEMap<K, V, S> {
    /// Attempt a conversion from [`HashMap`], consuming the given `HashMap`.
    /// Will return `None` if the `HashMap` is empty.
    ///
    /// ```
    /// use std::collections::*;
    ///
    /// use nonempty_collections::*;
    ///
    /// let mut map = HashMap::new();
    /// map.extend([("a", 1), ("b", 2)]);
    /// assert_eq!(Some(nem! {"a" => 1, "b" => 2}), NEMap::try_from_map(map));
    /// let map: HashMap<(), ()> = HashMap::new();
    /// assert_eq!(None, NEMap::try_from_map(map));
    /// ```
    #[must_use]
    pub fn try_from_map(map: HashMap<K, V, S>) -> Option<Self> {
        if map.is_empty() {
            None
        } else {
            Some(Self { inner: map })
        }
    }

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

    /// Returns a regular iterator over the entries in this non-empty map.
    ///
    /// For a `NonEmptyIterator` see `Self::nonempty_iter()`.
    pub fn iter(&self) -> std::collections::hash_map::Iter<'_, K, V> {
        self.inner.iter()
    }

    /// Returns a regular mutable iterator over the entries in this non-empty
    /// map.
    ///
    /// For a `NonEmptyIterator` see `Self::nonempty_iter_mut()`.
    pub fn iter_mut(&mut self) -> std::collections::hash_map::IterMut<'_, K, V> {
        self.inner.iter_mut()
    }

    /// An iterator visiting all elements in arbitrary order. The iterator
    /// element type is `(&'a K, &'a V)`.
    pub fn nonempty_iter(&self) -> Iter<'_, K, V> {
        Iter {
            iter: self.inner.iter(),
        }
    }

    /// An iterator visiting all elements in arbitrary order. The iterator
    /// element type is `(&'a K, &'a mut V)`.
    ///
    /// # Panics
    ///
    /// If you manually advance this iterator until empty and then call `first`,
    /// you're in for a surprise.
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
    /// let m = nem!["Valmar" => "Vanyar", "Tirion" => "Noldor", "Alqualondë" => "Teleri"];
    /// let mut v: NEVec<_> = m.keys().collect();
    /// v.sort();
    /// assert_eq!(nev![&"Alqualondë", &"Tirion", &"Valmar"], v);
    /// ```
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys {
            inner: self.inner.keys(),
        }
    }

    /// Returns the number of elements in the map. Always 1 or more.
    ///
    /// ```
    /// use nonempty_collections::nem;
    ///
    /// let m = nem!["a" => 1, "b" => 2];
    /// assert_eq!(2, m.len().get());
    /// ```
    #[must_use]
    pub fn len(&self) -> NonZeroUsize {
        unsafe { NonZeroUsize::new_unchecked(self.inner.len()) }
    }

    /// A `NEMap` is never empty.
    #[deprecated(since = "0.1.0", note = "A NEMap is never empty.")]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        false
    }

    /// An iterator visiting all values in arbitrary order. The iterator element
    /// type is `&'a V`.
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let m = nem!["Valmar" => "Vanyar", "Tirion" => "Noldor", "Alqualondë" => "Teleri"];
    /// let mut v: NEVec<_> = m.values().collect();
    /// v.sort();
    /// assert_eq!(nev![&"Noldor", &"Teleri", &"Vanyar"], v);
    /// ```
    pub fn values(&self) -> Values<'_, K, V> {
        Values {
            inner: self.inner.values(),
        }
    }

    // /// An iterator visiting all values mutably in arbitrary order. The iterator
    // /// element type is `&'a mut V`.
    // ///
    // /// ```
    // /// use nonempty_collections::nem;
    // ///
    // /// let mut m = nem!["Valmar" => 10000, "Tirion" => 10000, "Alqualondë" =>
    // 10000]; ///
    // /// for v in m.values_mut() {
    // ///     *v += 1000;
    // /// }
    // /// ```
    // pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
    //     ValuesMut {
    //         inner: self.iter_mut(),
    //         head_val: todo!(),
    //     }
    // }
}

impl<K, V, S> NEMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher,
{
    /// Returns true if the map contains a value.
    ///
    /// ```
    /// use nonempty_collections::nem;
    ///
    /// let m = nem!["Jack" => 8];
    /// assert!(m.contains_key("Jack"));
    /// assert!(!m.contains_key("Colin"));
    /// ```
    #[must_use]
    pub fn contains_key<Q>(&self, k: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.inner.contains_key(k)
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's value type, but `Hash` and
    /// `Eq` on the borrowed form must match those for the key type.
    ///
    /// ```
    /// use nonempty_collections::nem;
    ///
    /// let m = nem!["silmarils" => 3];
    /// assert_eq!(Some(&3), m.get("silmarils"));
    /// assert_eq!(None, m.get("arkenstone"));
    /// ```
    #[must_use]
    pub fn get<Q>(&self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.inner.get(k)
    }

    /// Returns the key-value pair corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's value type, but `Hash` and
    /// `Eq` on the borrowed form must match those for the key type.
    ///
    /// ```
    /// use nonempty_collections::nem;
    ///
    /// let m = nem!["silmarils" => 3];
    /// assert_eq!(Some((&"silmarils", &3)), m.get_key_value("silmarils"));
    /// assert_eq!(None, m.get_key_value("arkenstone"));
    /// ```
    #[must_use]
    pub fn get_key_value<Q>(&self, k: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.inner.get_key_value(k)
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's value type, but `Hash` and
    /// `Eq` on the borrowed form must match those for the key type.
    ///
    /// ```
    /// use nonempty_collections::nem;
    ///
    /// let mut m = nem!["silmarils" => 3];
    /// let mut v = m.get_mut("silmarils").unwrap();
    ///
    /// // And thus it came to pass that the Silmarils found their long homes:
    /// // one in the airs of heaven, and one in the fires of the heart of the
    /// // world, and one in the deep waters.
    /// *v -= 3;
    ///
    /// assert_eq!(Some(&0), m.get("silmarils"));
    /// ```
    #[must_use]
    pub fn get_mut<Q>(&mut self, k: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.inner.get_mut(k)
    }

    /// Insert a key-value pair into the map.
    ///
    /// If the map did not have this present, [`None`] is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old
    /// value is returned. The key is not updated, though; this matters for
    /// types that can be `==` without being identical. See [`HashMap::insert`]
    /// for more.
    ///
    /// ```
    /// use nonempty_collections::nem;
    ///
    /// let mut m = nem!["Vilya" => "Elrond", "Nenya" => "Galadriel"];
    /// assert_eq!(None, m.insert("Narya", "Cirdan"));
    ///
    /// // The Ring of Fire was given to Gandalf upon his arrival in Middle Earth.
    /// assert_eq!(Some("Cirdan"), m.insert("Narya", "Gandalf"));
    /// ```
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        self.inner.insert(k, v)
    }

    /// Shrinks the capacity of the map as much as possible. It will drop down
    /// as much as possible while maintaining the internal rules and possibly
    /// leaving some space in accordance with the resize policy.
    pub fn shrink_to_fit(&mut self) {
        self.inner.shrink_to_fit();
    }

    /// See [`HashMap::with_capacity_and_hasher`].
    #[must_use]
    pub fn with_capacity_and_hasher(
        capacity: NonZeroUsize,
        hasher: S,
        k: K,
        v: V,
    ) -> NEMap<K, V, S> {
        let mut inner = HashMap::with_capacity_and_hasher(capacity.get(), hasher);
        inner.insert(k, v);
        NEMap { inner }
    }

    /// See [`HashMap::with_hasher`].
    #[must_use]
    pub fn with_hasher(hasher: S, k: K, v: V) -> NEMap<K, V, S> {
        let mut inner = HashMap::with_hasher(hasher);
        inner.insert(k, v);
        NEMap { inner }
    }
}

impl<K, V, S> AsRef<HashMap<K, V, S>> for NEMap<K, V, S> {
    fn as_ref(&self) -> &HashMap<K, V, S> {
        &self.inner
    }
}

impl<K, V, S> AsMut<HashMap<K, V, S>> for NEMap<K, V, S> {
    fn as_mut(&mut self) -> &mut HashMap<K, V, S> {
        &mut self.inner
    }
}

impl<K, V, S> PartialEq for NEMap<K, V, S>
where
    K: Eq + Hash,
    V: PartialEq,
    S: BuildHasher,
{
    /// This is an `O(n)` comparison of each key/value pair, one by one.
    /// Short-circuits if any comparison fails.
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let m0 = nem!['a' => 1, 'b' => 2];
    /// let m1 = nem!['b' => 2, 'a' => 1];
    /// assert_eq!(m0, m1);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        self.inner.eq(&other.inner)
    }
}

impl<K, V, S> Eq for NEMap<K, V, S>
where
    K: Eq + Hash,
    V: Eq,
    S: BuildHasher,
{
}

impl<K, V, S> From<NEMap<K, V, S>> for HashMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher,
{
    /// ```
    /// use nonempty_collections::nem;
    /// use std::collections::HashMap;
    ///
    /// let m: HashMap<&str, usize> = nem!["population" => 1000].into();
    /// assert!(m.contains_key("population"));
    /// ```
    fn from(m: NEMap<K, V, S>) -> Self {
        m.inner
    }
}

impl<K, V, S> TryFrom<HashMap<K, V, S>> for NEMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher + Default,
{
    type Error = crate::Error;

    fn try_from(map: HashMap<K, V, S>) -> Result<Self, Self::Error> {
        map.try_into_nonempty_iter()
            .map(NonEmptyIterator::collect)
            .ok_or(crate::Error::Empty)
    }
}

impl<K, V, S> IntoNonEmptyIterator for NEMap<K, V, S> {
    type IntoNEIter = IntoIter<K, V>;

    fn into_nonempty_iter(self) -> Self::IntoNEIter {
        IntoIter {
            iter: self.inner.into_iter(),
        }
    }
}

impl<'a, K, V, S> IntoNonEmptyIterator for &'a NEMap<K, V, S> {
    type IntoNEIter = Iter<'a, K, V>;

    fn into_nonempty_iter(self) -> Self::IntoNEIter {
        self.nonempty_iter()
    }
}

impl<K, V, S> IntoIterator for NEMap<K, V, S> {
    type Item = (K, V);

    type IntoIter = std::collections::hash_map::IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.into_iter()
    }
}

impl<'a, K, V, S> IntoIterator for &'a NEMap<K, V, S> {
    type Item = (&'a K, &'a V);

    type IntoIter = std::collections::hash_map::Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K, V, S> IntoIterator for &'a mut NEMap<K, V, S> {
    type Item = (&'a K, &'a mut V);

    type IntoIter = std::collections::hash_map::IterMut<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

/// ```
/// use nonempty_collections::*;
///
/// let v = nev![('a', 1), ('b', 2), ('c', 3), ('a', 4)];
/// let m0: NEMap<_, _> = v.into_nonempty_iter().collect();
/// let m1: NEMap<_, _> = nem!['a' => 4, 'b' => 2, 'c' => 3];
/// assert_eq!(m0, m1);
/// ```
impl<K, V, S> FromNonEmptyIterator<(K, V)> for NEMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher + Default,
{
    fn from_nonempty_iter<I>(iter: I) -> Self
    where
        I: IntoNonEmptyIterator<Item = (K, V)>,
    {
        NEMap {
            inner: iter.into_nonempty_iter().into_iter().collect(),
        }
    }
}

/// A non-empty iterator over the entries of an [`NEMap`].
#[must_use = "non-empty iterators are lazy and do nothing unless consumed"]
pub struct Iter<'a, K: 'a, V: 'a> {
    iter: std::collections::hash_map::Iter<'a, K, V>,
}

impl<K, V> NonEmptyIterator for Iter<'_, K, V> {}

impl<'a, K, V> IntoIterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    type IntoIter = std::collections::hash_map::Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for Iter<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.iter.fmt(f)
    }
}

/// A non-empty iterator over mutable values of an [`NEMap`].
#[must_use = "non-empty iterators are lazy and do nothing unless consumed"]
pub struct IterMut<'a, K: 'a, V: 'a> {
    iter: std::collections::hash_map::IterMut<'a, K, V>,
}

impl<K, V> NonEmptyIterator for IterMut<'_, K, V> {}

impl<'a, K, V> IntoIterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    type IntoIter = std::collections::hash_map::IterMut<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for IterMut<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.iter.fmt(f)
    }
}

/// A non-empty iterator over the entries of an [`NEMap`].
pub struct IntoIter<K, V> {
    iter: std::collections::hash_map::IntoIter<K, V>,
}

impl<K, V> NonEmptyIterator for IntoIter<K, V> {}

impl<K, V> IntoIterator for IntoIter<K, V> {
    type Item = (K, V);

    type IntoIter = std::collections::hash_map::IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for IntoIter<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.iter.fmt(f)
    }
}

/// A non-empty iterator over the keys of an [`NEMap`].
#[must_use = "non-empty iterators are lazy and do nothing unless consumed"]
pub struct Keys<'a, K: 'a, V: 'a> {
    inner: std::collections::hash_map::Keys<'a, K, V>,
}

impl<K, V> NonEmptyIterator for Keys<'_, K, V> {}

impl<'a, K, V> IntoIterator for Keys<'a, K, V> {
    type Item = &'a K;

    type IntoIter = std::collections::hash_map::Keys<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for Keys<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

/// A non-empty iterator over the values of an [`NEMap`].
#[must_use = "non-empty iterators are lazy and do nothing unless consumed"]
pub struct Values<'a, K: 'a, V: 'a> {
    inner: std::collections::hash_map::Values<'a, K, V>,
}

impl<K, V> NonEmptyIterator for Values<'_, K, V> {}

impl<'a, K, V> IntoIterator for Values<'a, K, V> {
    type Item = &'a V;

    type IntoIter = std::collections::hash_map::Values<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for Values<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl<K: fmt::Debug, V: fmt::Debug, S> fmt::Debug for NEMap<K, V, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

// /// A non-empty iterator over mutable values of an [`NEMap`].
// pub struct ValuesMut<'a, K: 'a, V: 'a> {
//     inner: IterMut<'a, K, V>,
// }

// impl<'a, K, V> NonEmptyIterator for ValuesMut<'a, K, V> {
//     type Item = &'a mut V;

//     type Iter = Skip<Chain<Once<&'a mut V>,
// std::collections::hash_map::IterMut<'a, K, V>>>;

//     fn first(self) -> (Self::Item, Self::Iter) {
//         (self.head_val, self.inner.skip(1))
//     }

//     fn next(&mut self) -> Option<Self::Item> {
//         self.inner.next().map(|(_, v)| v)
//     }
// }

#[cfg(test)]
mod test {
    use std::num::NonZeroUsize;

    use maplit::hashmap;

    use crate::nem;

    struct Foo {
        user: String,
    }

    #[test]
    fn debug_impl() {
        let expected = format!("{:?}", hashmap! {0 => 10});
        let actual = format!("{:?}", nem! {0 => 10});
        assert_eq!(expected, actual);
    }

    #[test]
    fn macro_usage() {
        let a = Foo {
            user: "a".to_string(),
        };
        let b = Foo {
            user: "b".to_string(),
        };

        let map = nem![1 => a, 2 => b];
        assert_eq!("a", map.get(&1).unwrap().user);
        assert_eq!("b", map.get(&2).unwrap().user);
    }

    #[test]
    fn macro_length() {
        let map = nem![1 => 'a', 2 => 'b', 1 => 'c'];
        assert_eq!(unsafe { NonZeroUsize::new_unchecked(2) }, map.len());
        assert_eq!('c', *map.get(&1).unwrap());
        assert_eq!('b', *map.get(&2).unwrap());
    }

    #[test]
    fn iter_mut() {
        let mut v = nem! {"a" => 0, "b" => 1, "c" => 2};

        v.iter_mut().for_each(|(_k, v)| {
            *v += 1;
        });
        assert_eq!(nem! {"a" => 1, "b" => 2, "c" => 3}, v);

        for (_k, v) in &mut v {
            *v -= 1;
        }
        assert_eq!(nem! {"a" => 0, "b" => 1, "c" => 2}, v);
    }
}

#[cfg(feature = "serde")]
#[cfg(test)]
mod serde_tests {
    use std::collections::HashMap;

    use crate::nem;
    use crate::NEMap;

    #[test]
    fn json() {
        let map0 = nem![1 => 'a', 2 => 'b', 1 => 'c'];
        let j = serde_json::to_string(&map0).unwrap();
        let map1 = serde_json::from_str(&j).unwrap();
        assert_eq!(map0, map1);

        let empty: HashMap<usize, char> = HashMap::new();
        let j = serde_json::to_string(&empty).unwrap();
        let bad = serde_json::from_str::<NEMap<usize, char>>(&j);
        assert!(bad.is_err());
    }
}
