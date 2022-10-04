use super::*;

/// A mutable iterator over the values of a `DoubleMap` in arbitrary order.
/// The iterator element type is `&'a mut V`.
///
/// This `struct` is created by the [`values_mut`](DoubleMap::values_mut) method
/// on [`DoubleMap`]. See its documentation for more.
///
/// # Example
///
/// ```
/// use double_map::{DoubleMap, doublemap};
///
/// let mut map = doublemap!{
///     1, "a" => "One".to_owned(),
///     2, "b" => "Two".to_owned(),
///     3, "c" => "Three".to_owned(),
/// };
///
/// let mut values = map.values_mut();
/// values.next().map(|v| v.push_str(" coin"));
/// values.next().map(|v| v.push_str(" coin"));
/// values.next().map(|v| v.push_str(" coin"));
///
/// // It is fused iterator
/// assert_eq!(values.next(), None);
/// assert_eq!(values.next(), None);
///
/// assert_eq!(map.get_key1(&1).unwrap(), &"One coin".to_owned()  );
/// assert_eq!(map.get_key1(&2).unwrap(), &"Two coin".to_owned()  );
/// assert_eq!(map.get_key1(&3).unwrap(), &"Three coin".to_owned());
/// ```
pub struct ValuesMut<'a, K1, K2, V> {
    pub(super) inner: IterMut<'a, K1, K2, V>,
}

impl<'a, K1, K2, V> Iterator for ValuesMut<'a, K1, K2, V> {
    type Item = &'a mut V;

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<&'a mut V> {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.inner.next() {
            Some((_, _, v)) => Some(v),
            None => None,
        }
    }
    #[cfg_attr(feature = "inline-more", inline)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<K1, K2, V> ExactSizeIterator for ValuesMut<'_, K1, K2, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn len(&self) -> usize {
        self.inner.len()
    }
}
impl<K1, K2, V> FusedIterator for ValuesMut<'_, K1, K2, V> {}

impl<K1, K2, V: Debug> fmt::Debug for ValuesMut<'_, K1, K2, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list()
            .entries(self.inner.iter().map(|(_, _, v)| v))
            .finish()
    }
}
