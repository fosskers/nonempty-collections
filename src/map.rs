//! Non-empty [`HashMap`]s.

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

impl<K, V, S> From<NEMap<K, V, S>> for HashMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher,
{
    fn from(m: NEMap<K, V, S>) -> Self {
        let mut map = m.tail;
        map.insert(m.head_key, m.head_val);
        map
    }
}
