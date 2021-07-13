//! Non-empty [`HashMap`]s.

use std::borrow::Borrow;
use std::collections::HashMap;
use std::hash::{BuildHasher, Hash};

/// Like the [`nev`] macro, but for Maps. A nice short-hand for constructing
/// [`NEMap`] values.
#[macro_export]
macro_rules! nem {
    ($hk:expr => $hv:expr, $( $xk:expr => $xv:expr ),*) => {{
        let mut tail = std::collections::HashMap::new();
        tail.insert($hk, $hv);
        $( tail.insert($xk, $xv); )*
        tail.remove(&$hk);
        $crate::NEMap { head_key: $hk, head_val: $hv, tail }
    }};
    ($hk:expr => $hv:expr) => {
        $crate::NEMap { head_key: $hk, head_val: $hv, tail: std::collections::HashMap::new() }
    }
}

/// A non-empty, growable `HashMap`.
///
/// ```
/// use nonempty_collections::nem;
///
/// let m = nem!["elves" => 3000, "orcs" => 10000];
/// ```
pub struct NEMap<K, V, S = std::collections::hash_map::RandomState> {
    /// The key of the ever-present element of the non-empty `HashMap`.
    pub head_key: K,

    /// The value of the ever-present element of the non-empty `HashMap`.
    pub head_val: V,

    /// The remaining key-value pairs, perhaps empty.
    pub tail: HashMap<K, V, S>,
}

impl<K, V, S> NEMap<K, V, S> {
    /// Returns the number of elements the map can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.tail.capacity() + 1
    }

    /// Returns a reference to the map's `BuildHasher`.
    pub fn hasher(&self) -> &S {
        self.tail.hasher()
    }

    /// Returns the number of elements in the map. Always 1 or more.
    ///
    /// ```
    /// use nonempty_collections::nem;
    ///
    /// let m = nem!["a" => 1, "b" => 2];
    /// assert_eq!(2, m.len());
    /// ```
    pub fn len(&self) -> usize {
        self.tail.len() + 1
    }
}

impl<K, V, S> NEMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher,
{
    /// Returns true if the set contains a value.
    ///
    /// ```
    /// use nonempty_collections::nem;
    ///
    /// let m = nem!["Jack" => 8];
    /// assert!(m.contains_key("Jack"));
    /// assert!(!m.contains_key("Colin"));
    /// ```
    pub fn contains_key<Q>(&self, k: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.tail.contains_key(k) || k == self.head_key.borrow()
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
    pub fn get<Q>(&self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.tail
            .get(k)
            .or_else(|| (k == self.head_key.borrow()).then(|| &self.head_val))
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
    pub fn get_key_value<Q>(&self, k: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.tail
            .get_key_value(k)
            .or_else(|| (k == self.head_key.borrow()).then(|| (&self.head_key, &self.head_val)))
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
    pub fn get_mut<Q>(&mut self, k: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        match self.tail.get_mut(k) {
            Some(v) => Some(v),
            None if k == self.head_key.borrow() => Some(&mut self.head_val),
            None => None,
        }
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
        if k == self.head_key {
            Some(std::mem::replace(&mut self.head_val, v))
        } else {
            self.tail.insert(k, v)
        }
    }

    /// Creates a new `NESet` with a single element.
    pub fn new(k: K, v: V) -> NEMap<K, V> {
        NEMap {
            head_key: k,
            head_val: v,
            tail: HashMap::new(),
        }
    }
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
        let mut map = m.tail;
        map.insert(m.head_key, m.head_val);
        map
    }
}
