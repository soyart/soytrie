use std::collections::HashMap;

#[inline(always)]
pub(super) fn insert_direct_value<'a, K, V>(m: &'a mut HashMap<K, V>, key: K, value: V) -> &'a mut V
where
    K: Eq + std::hash::Hash,
{
    m.entry(key).or_insert(value)
}
