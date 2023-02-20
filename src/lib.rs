#![feature(test)]

use std::collections::HashMap;

/// Defines how the trie node treats each match.
pub enum SearchMode {
    /// Entire path has to match, and the final [`TrieNode<K, V>`](TrieNode) has to
    /// have some value (i.e. a word or a _value node_).
    Exact,

    /// Entire path has to match, although the final [`TrieNode<K, V>`](TrieNode)
    /// maybe non-value (i.e. non-word or a _path node_)
    Prefix,
}

/// A node in a trie.
/// In this trie implementation, a node can be either a _value node_, or a _path node_.
/// A value node has [`Some(V)`](Some) in the value field, while path node has [`None`](None).
/// If using multiple tries, consider using [`Trie<K, V>`](Trie), which has a path node as root.
pub struct TrieNode<K, V>
where
    K: Clone + Eq + std::hash::Hash,
{
    pub value: Option<V>,

    children: HashMap<K, TrieNode<K, V>>,
}

impl<K, V> TrieNode<K, V>
where
    K: Clone + Eq + std::hash::Hash,
{
    /// Creates new node with value set to [None](None).
    #[inline]
    pub fn new() -> Self {
        Self {
            children: HashMap::new(),
            value: None,
        }
    }

    /// Returns the mutable reference of the existing child at key `key`.
    /// If it does not exist, inserts `child` to `self.children` and returning that new child.
    #[inline]
    pub fn insert_direct_child<T>(&mut self, key: K, child: T) -> &mut Self
    where
        T: Into<Self>,
    {
        self.children.entry(key).or_insert(child.into())
    }

    /// Inserts `value` to child at path `path`. If the child does not exist, a new child
    /// is created and appended to the trie with value `Some(value)`.
    #[inline]
    pub fn insert(&mut self, path: &[K], value: V) {
        // The recursive and more functional implementation performs worse than the current imperative version.
        // if path.is_empty() {
        //     self.value = Some(value);
        //     return;
        // }
        //
        // self.insert_direct_child(path[0].clone(), TrieNode::new())
        //     .insert(&path[1..], value)

        let mut curr = self;
        for p in path {
            let next = curr.insert_direct_child(p.clone(), TrieNode::new());
            curr = next;
        }

        curr.value = Some(value);
    }

    /// Returns a reference to the direct child at key `key`.
    #[inline(always)]
    pub fn get_direct_child(&self, key: K) -> Option<&Self> {
        self.children.get(&key)
    }

    /// Returns a mutable reference to the direct child at key `key`.
    #[inline(always)]
    pub fn get_direct_child_mut(&mut self, key: K) -> Option<&mut Self> {
        self.children.get_mut(&key)
    }

    /// Recursively searchs for child at the path, returning reference to the child if it exists.
    pub fn get_child(&self, path: &[K]) -> Option<&Self> {
        if path.is_empty() {
            return Some(self);
        }

        self.children
            .get(&path[0])
            .and_then(|child| child.get_child(&path[1..]))
    }

    /// Recursively searchs for child at the path, returning mutable reference to the child if it exists.
    pub fn get_child_mut(&mut self, path: &[K]) -> Option<&mut Self> {
        if path.is_empty() {
            return Some(self);
        }

        self.children
            .get_mut(&path[0])
            .and_then(|child| child.get_child_mut(&path[1..]))
    }

    /// Searchs for child at the path, returning boolean value indicating success.
    #[inline(always)]
    pub fn search(&self, mode: SearchMode, path: &[K]) -> bool {
        match self.get_child(path) {
            None => false,
            Some(child) => match mode {
                SearchMode::Prefix => true,
                SearchMode::Exact => child.value.is_some(),
            },
        }
    }

    /// Removes and returns the direct owned child at key `key`.
    #[inline(always)]
    pub fn remove_direct_child(&mut self, key: K) -> Option<Self> {
        self.children.remove(&key)
    }

    /// Removes the child at path `path`, returning the owned child.
    pub fn remove(&mut self, path: &[K]) -> Option<Self> {
        let last_idx = path.len() - 1;

        self.get_child_mut(&path[..last_idx])
            .and_then(|child| child.children.remove(&path[last_idx]))
    }

    /// Recursively collects all extant children of `node`.
    fn collect_children<'s, 'l>(node: &'l Self, children: &mut Vec<&'s Self>)
    where
        'l: 's,
    {
        children.push(node);
        for child in node.children.values() {
            Self::collect_children(child, children);
        }
    }

    /// Returns all children that are _value nodes_ as a vector of references to the children.
    #[inline]
    pub fn all_children(&self) -> Vec<&V> {
        let children = &mut Vec::new();
        Self::collect_children(self, children);

        children
            .iter()
            .filter_map(|child| child.value.as_ref())
            .collect()
    }

    /// Collects all values of the children of the child at path `path`, returning [`None`](None)
    /// if the child does not exist or if the child's number of children is 0. Otherwise, the
    /// references to values is collected as [`Some(Vec<&V>)`](Some)
    #[inline]
    pub fn predict(&self, path: &[K]) -> Option<Vec<&V>> {
        self.get_child(path).and_then(|child| {
            let predicted = child.all_children();

            if predicted.is_empty() {
                return None;
            }

            Some(predicted)
        })
    }
}

impl<K, V> From<V> for TrieNode<K, V>
where
    K: Clone + Eq + std::hash::Hash,
{
    fn from(value: V) -> Self {
        Self {
            value: Some(value),
            children: HashMap::new(),
        }
    }
}

/// If `K` and `V` is Clone, then `TrieNode<K, V>` is also `Clone`.
impl<K, V> Clone for TrieNode<K, V>
where
    K: Clone + Eq + std::hash::Hash,
    V: Clone,
{
    fn clone(&self) -> Self {
        Self {
            value: self.value.clone(),
            children: self.children.clone(),
        }
    }
}

impl<K, V> TrieNode<K, V>
where
    K: Clone + Eq + std::hash::Hash,
    V: Clone,
{
    #[inline]
    pub fn get_direct_child_clone(&self, key: K) -> Option<Self> {
        self.children
            .get(&key)
            .and_then(|child| Some(child.clone()))
    }

    #[inline]
    pub fn get_direct_child_mut_clone(&mut self, key: K) -> Option<Self> {
        self.children
            .get_mut(&key)
            .and_then(|child| Some(child.clone()))
    }

    /// Clones a `TrieNode<K, V>` out of `self.children`
    /// ```
    /// use soytrie::TrieNode;
    ///
    /// let mut node = TrieNode::<u8, u8>::new();
    /// node.insert(b"1", b'1'.into());
    /// let mut cloned = node.search_child_clone(b"1").expect("no such child");
    /// cloned.insert(b"2", b'2'.into());
    ///
    /// assert_eq!(
    ///     node.all_children().len(),
    ///     1,
    /// );
    ///
    /// assert_eq!(
    ///     cloned.all_children().len(),
    ///     2,
    /// );
    /// ```
    pub fn search_child_clone(&self, path: &[K]) -> Option<Self> {
        if path.is_empty() {
            return Some(self.clone());
        }

        self.children
            .get(&path[0])
            .and_then(|child| child.search_child_clone(&path[1..]))
    }
}

pub struct Trie<K, V>
where
    K: Clone + Eq + std::hash::Hash,
{
    root: TrieNode<K, V>,
}

/// Wraps a `TrieNode<K, V>` with value `None` as its root node
impl<K, V> Trie<K, V>
where
    K: Clone + Eq + std::hash::Hash,
{
    #[inline]
    pub fn new() -> Self {
        Self {
            root: TrieNode::new(),
        }
    }
}

impl<K, V> From<TrieNode<K, V>> for Trie<K, V>
where
    K: Clone + Eq + std::hash::Hash,
{
    fn from(node: TrieNode<K, V>) -> Self {
        Self { root: node }
    }
}

impl<K, V> AsRef<TrieNode<K, V>> for Trie<K, V>
where
    K: Clone + Eq + std::hash::Hash,
{
    fn as_ref(&self) -> &TrieNode<K, V> {
        &self.root
    }
}

impl<K, V> std::ops::Deref for Trie<K, V>
where
    K: Clone + Eq + std::hash::Hash,
{
    type Target = TrieNode<K, V>;
    fn deref(&self) -> &Self::Target {
        &self.root
    }
}

impl<K, V> std::ops::DerefMut for Trie<K, V>
where
    K: Clone + Eq + std::hash::Hash,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.root
    }
}

#[cfg(test)]
mod tests {
    extern crate test;
    use test::Bencher;

    use super::*;

    const BENCH_SIZE: usize = 10_000;

    #[test]
    fn test_trie() {
        use super::*;
        let mut trie: Trie<u8, &str> = Trie::new();

        trie.insert(b"a", "a");
        trie.insert(b"ab", "ab");
        trie.insert(b"abc", "abc");
        trie.insert(b"foo", "foo");
        trie.insert(b"foobar", "foobar");
        trie.insert(b"foobar2000", "foobar2000");

        assert_eq!(trie.predict(b"f").expect("bad predict").len(), 3); // foo, foobar, foobar2000
        assert_eq!(trie.predict(b"ab").expect("bad predict").len(), 2); // ab, abc
        assert_eq!(trie.predict(b"fa"), None);

        assert_eq!(trie.search(SearchMode::Prefix, b"a"), true);
        assert_eq!(trie.search(SearchMode::Prefix, b"f"), true);
        assert_eq!(trie.search(SearchMode::Prefix, b"fo"), true);
        assert_eq!(trie.search(SearchMode::Prefix, b"fa"), false);
        assert_eq!(trie.search(SearchMode::Prefix, b"bar"), false);
        assert_eq!(trie.search(SearchMode::Prefix, b"ob"), false);
        assert_eq!(trie.search(SearchMode::Prefix, b"foooba"), false);

        assert_eq!(trie.search(SearchMode::Exact, b"f"), false);
        assert_eq!(trie.search(SearchMode::Exact, b"fo"), false);
        assert_eq!(trie.search(SearchMode::Exact, b"foo"), true);
        assert_eq!(trie.search(SearchMode::Exact, b"foob"), false);
        assert_eq!(trie.search(SearchMode::Exact, b"fooba"), false);
        assert_eq!(trie.search(SearchMode::Exact, b"foobar"), true);

        assert_eq!(trie.all_children().len(), 6);
        assert_eq!(trie.predict(b"a").expect("a node is None").len(), 3);
        assert_eq!(trie.predict(b"f").expect("f node is None").len(), 3);

        let foob_node = trie.root.get_child(b"foob");
        assert_eq!(
            foob_node.expect("foob node is None").all_children().len(),
            2
        );

        let foobar2000_node = trie.get_child(b"foobar2000");
        assert_eq!(
            foobar2000_node
                .expect("foobar2000 node is None")
                .all_children()
                .len(),
            1,
        );

        let foobar2000_node = trie.remove(b"foobar2000").expect("foobar2000 node is None");
        assert_eq!(foobar2000_node.all_children().len(), 1);
        assert_eq!(foobar2000_node.value, Some("foobar2000"));
        assert_eq!(trie.all_children().len(), 5);
        trie.remove(b"abc"); // deletes abc
        assert_eq!(trie.all_children().len(), 4);
        trie.remove(b"ab"); // deletes ab
        assert_eq!(trie.all_children().len(), 3);
        trie.remove(b"ab"); // deletes ab
        assert_eq!(trie.all_children().len(), 3);
        trie.remove(b"f"); // deletes f, fo, foo
        assert_eq!(trie.all_children().len(), 1);
        trie.remove(b"a"); // deletes a
        assert_eq!(trie.all_children().len(), 0);
    }

    fn insert_root(i: usize, b: &mut Bencher, trie: &mut Trie<usize, &str>) {
        b.iter(|| {
            let inputs: Vec<usize> = (i..BENCH_SIZE).into_iter().collect();

            trie.insert(&inputs, "foo");

            assert_eq!(trie.all_children().len(), i + 1);
            assert_eq!(
                trie.search_child(&inputs).and_then(|child| child.value),
                Some("foo")
            );
        })
    }

    #[bench]
    fn insert_bench(b: &mut Bencher) {
        let mut trie = Trie::new();
        (0..3).for_each(|i| insert_root(i, b, &mut trie))
    }
}
