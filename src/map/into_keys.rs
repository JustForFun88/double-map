use super::*;

pub struct IntoKeys<K1, K2, V, A: Allocator + Clone = Global> {
    pub(super) inner: IntoIter<K1, K2, V, A>,
}

impl<K1, K2, V, A: Allocator + Clone> Iterator for IntoKeys<K1, K2, V, A> {
    type Item = (K1, K2);

    #[inline]
    fn next(&mut self) -> Option<(K1, K2)> {
        match self.inner.next() {
            Some((k1, k2, _)) => Some((k1, k2)),
            None => None,
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<K1, K2, V, A: Allocator + Clone> ExactSizeIterator for IntoKeys<K1, K2, V, A> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K1, K2, V, A: Allocator + Clone> FusedIterator for IntoKeys<K1, K2, V, A> {}

impl<K1: Debug, K2: Debug, V, A: Allocator + Clone> fmt::Debug for IntoKeys<K1, K2, V, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list()
            .entries(self.inner.iter().map(|(k1, k2, _)| (k1, k2)))
            .finish()
    }
}
