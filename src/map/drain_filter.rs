use super::*;

pub struct DrainFilter<'a, K1, K2, V, F, A: Allocator + Clone = Global>
where
    F: FnMut(&K1, &K2, &mut V) -> bool,
{
    pub(super) f: F,
    pub(super) inner: DrainFilterInner<'a, K1, K2, V, A>,
}

impl<'a, K1, K2, V, F, A> Drop for DrainFilter<'a, K1, K2, V, F, A>
where
    F: FnMut(&K1, &K2, &mut V) -> bool,
    A: Allocator + Clone,
{
    #[cfg_attr(feature = "inline-more", inline)]
    fn drop(&mut self) {
        while let Some(item) = self.next() {
            let guard = ConsumeAllOnDrop(self);
            drop(item);
            mem::forget(guard);
        }
    }
}

struct ConsumeAllOnDrop<'a, T: Iterator>(pub &'a mut T);

impl<T: Iterator> Drop for ConsumeAllOnDrop<'_, T> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn drop(&mut self) {
        self.0.for_each(drop);
    }
}

impl<K1, K2, V, F, A> Iterator for DrainFilter<'_, K1, K2, V, F, A>
where
    F: FnMut(&K1, &K2, &mut V) -> bool,
    A: Allocator + Clone,
{
    type Item = (K1, K2, V);

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next(&mut self.f)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.inner.iter.size_hint().1)
    }
}

impl<K1, K2, V, F> FusedIterator for DrainFilter<'_, K1, K2, V, F> where
    F: FnMut(&K1, &K2, &mut V) -> bool
{
}

pub(super) struct DrainFilterInner<'a, K1, K2, V, A: Allocator + Clone> {
    pub iter: RawPointerIter<(K1, K2, V)>,
    pub table: &'a mut RawTable<(K1, K2, V), A>,
}

impl<K1, K2, V, A: Allocator + Clone> DrainFilterInner<'_, K1, K2, V, A> {
    #[cfg_attr(feature = "inline-more", inline)]
    pub(super) fn next<F>(&mut self, f: &mut F) -> Option<(K1, K2, V)>
    where
        F: FnMut(&K1, &K2, &mut V) -> bool,
    {
        unsafe {
            for item in &mut self.iter {
                let &mut (ref key1, ref key2, ref mut value) = item.as_data_mut();
                if f(key1, key2, value) {
                    return Some(self.table.remove(item));
                }
            }
        }
        None
    }
}
