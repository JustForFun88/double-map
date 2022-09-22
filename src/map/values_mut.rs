use super::*;

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
