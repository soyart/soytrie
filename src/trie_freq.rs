use std::collections::HashMap;

use super::util;

pub struct TrieNodeFreq<K, V>
where
    K: Clone + Eq + std::hash::Hash,
{
    pub freq: usize,
    pub value: Option<V>,
    pub(super) children: HashMap<K, TrieNodeFreq<K, V>>,
}

impl<K, V> TrieNodeFreq<K, V>
where
    K: Clone + Eq + std::hash::Hash,
{
    /// Returns the mutable reference of the existing child at key `key`.
    /// If it does not exist, inserts `child` to `self.children` and returning that new child.
    #[inline]
    pub fn get_or_insert_direct_value<T, Q>(&mut self, key: Q, value: T) -> &mut Self
    where
        Q: std::ops::Deref<Target = K>,
        T: Into<Self>,
    {
        self.get_or_insert_direct_child::<Q>(key, value.into())
    }

    #[inline]
    pub fn get_or_insert_direct_child<Q>(&mut self, key: Q, child: Self) -> &mut Self
    where
        Q: std::ops::Deref<Target = K>,
    {
        self.freq += 1;
        util::insert_direct_value(&mut self.children, key.clone(), child)
    }
}
