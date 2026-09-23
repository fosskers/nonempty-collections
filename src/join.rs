//! `join_all`/`try_join_all` for non-empty iterators of [`Future`]s, using the
//! [`futures-util`](https://docs.rs/futures-util) crate.

use std::future::Future;

use crate::IntoNonEmptyIterator;
use crate::NEVec;

/// Creates a future which represents a non-empty collection of the outputs
/// of the futures given.
///
/// The returned future will drive execution for all of its underlying
/// futures, collecting the results into a destination [`NEVec`] in the same
/// order as they were provided.
///
/// See also [`futures_util::future::join_all`].
///
/// ```
/// use nonempty_collections::*;
///
/// async fn ready(n: i32) -> i32 {
///     n
/// }
///
/// let r = futures_executor::block_on(join::join_all(nev![ready(1), ready(2), ready(3)]));
/// assert_eq!(nev![1, 2, 3], r);
/// ```
pub async fn join_all<I>(iter: I) -> NEVec<<I::Item as Future>::Output>
where
    I: IntoNonEmptyIterator,
    I::Item: Future,
{
    let v = futures_util::future::join_all(iter.into_nonempty_iter()).await;
    NEVec::try_from_vec(v).expect("join_all preserves the length of its non-empty input")
}

/// Creates a future which represents either a non-empty collection of the
/// results of the futures given, or an error.
///
/// The returned future will drive execution for all of its underlying
/// futures, collecting the results into a destination [`NEVec`] in the same
/// order as they were provided.
///
/// If any future returns an error then all other futures will be canceled
/// and an error will be returned immediately. If all futures complete
/// successfully, however, then the returned future will succeed with an
/// [`NEVec`] of all the successful results.
///
/// See also [`futures_util::future::try_join_all`].
///
/// ```
/// use nonempty_collections::*;
///
/// async fn checked(n: i32) -> Result<i32, &'static str> {
///     if n < 0 { Err("negative") } else { Ok(n) }
/// }
///
/// let r = futures_executor::block_on(join::try_join_all(nev![
///     checked(1),
///     checked(2),
///     checked(3)
/// ]));
/// assert_eq!(Ok(nev![1, 2, 3]), r);
///
/// let r = futures_executor::block_on(join::try_join_all(nev![
///     checked(1),
///     checked(-2),
///     checked(3)
/// ]));
/// assert_eq!(Err("negative"), r);
/// ```
pub async fn try_join_all<I, T, E>(iter: I) -> Result<NEVec<T>, E>
where
    I: IntoNonEmptyIterator,
    I::Item: Future<Output = Result<T, E>>,
{
    let v = futures_util::future::try_join_all(iter.into_nonempty_iter()).await?;
    Ok(NEVec::try_from_vec(v)
        .expect("try_join_all preserves the length of its non-empty input on success"))
}
