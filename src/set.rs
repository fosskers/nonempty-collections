//! Non-empty Sets.

use std::collections::HashSet;

// FIXME Account for duplication with the head.
/// Like the [`nev`] macro, but for Sets. A nice short-hand for constructing
/// [`NESet`] values.
#[macro_export]
macro_rules! nes {
    ($h:expr, $( $x:expr ),*) => {{
        let mut tail = HashSet::new();
        $( tail.push($x); )*
        $crate::NESet { head: $h, tail }
    }};
    ($h:expr) => {
        $crate::NESet { head: $h, tail: HashSet::new() }
    }
}

/// A non-empty, growable Set.
#[derive(Debug, Clone)]
pub struct NESet<T> {
    /// The element of the non-empty Vector. Always exists.
    pub head: T,

    /// The remaining elements of the non-empty Vector, perhaps empty.
    pub tail: HashSet<T>,
}
