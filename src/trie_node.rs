/// Defines how the trie node treats each match.
#[derive(PartialEq)]
pub enum SearchMode {
    /// Exact gets valued node
    Exact,
    /// Prefix gets both path and valued nodes
    Prefix,
}

/// Traits for representing tries.
/// In this trie implementation, a node can be either a _valued node_, or a _path node_.
/// A valued node has [`Some(_)`](Some) in the value field, while path node has [`None`](None).
pub trait TrieNode<K, V>
where
    K: Clone + Eq + std::hash::Hash,
    Self: Sized,
{
    fn new() -> Self;

    /// Returns Some(_) if the node tracks frequency, None otherwise
    fn freq(&self) -> Option<usize>;

    fn set_value(&mut self, value: V);

    fn peek_value(&self) -> &Option<V>;

    fn is_valued(&self) -> bool;

    /// Returns `Some(Self)` if there's already child at key, otherwise inserts `child` and returns `None`
    /// It is a sister to [get_or_insert_direct_child](Self::get_or_insert_direct_child).
    fn insert_or_get_direct_child<Q>(&mut self, key: Q, child: Self) -> Option<Self>
    where
        Q: std::ops::Deref<Target = K>;

    /// Returns the mutable reference of the existing child at key `key`.
    /// If it does not exist, inserts `child` to `self.children` and returning that new child.
    fn get_or_insert_direct_child<Q>(&mut self, key: Q, child: Self) -> &mut Self
    where
        Q: std::ops::Deref<Target = K>;

    fn get_direct_child<Q>(&self, key: Q) -> Option<&Self>
    where
        Q: std::ops::Deref<Target = K>;

    fn get_direct_child_mut<Q>(&mut self, key: Q) -> Option<&mut Self>
    where
        Q: std::ops::Deref<Target = K>;

    fn remove_direct_child<Q>(&mut self, key: Q) -> Option<Self>
    where
        Q: std::ops::Deref<Target = K>;

    fn remove(&mut self, path: &[K]) -> Option<Self>;

    fn collect_children<'l, 's>(node: &'l Self, children: &mut Vec<&'s Self>)
    where
        'l: 's;

    fn all_children_values(&self) -> Vec<&V>;

    fn num_children(&self) -> usize;

    fn swap_node_value(&mut self, value: V) -> Option<V>;

    #[inline(always)]
    fn counts_freq(&self) -> bool {
        self.freq().is_some()
    }

    #[inline(always)]
    fn swap(&mut self, node: &mut Self) {
        std::mem::swap(self, node)
    }

    /// Like `insert_child`, but returns Some(TrieNode<K, V>) if there's a node at `path`.
    /// If `path` is empty, the value is used to construct a new Self, and that Self is swapped with self,
    /// and the call always returns `Some(node)` if `path` is empty.
    /// ```
    /// # use soytrie::{TrieNode, HashMapTrieFreq};
    /// let mut node: HashMapTrieFreq<_, u8> = TrieNode::new();
    /// assert!(node.get_or_update_child(b"foo", 1).is_none());
    /// assert!(node.get_or_update_child(b"fool", 6).is_none());
    /// assert!(node.get_or_update_child(b"foobar", 2).is_none());
    /// assert!(node.get_or_update_child(b"foobar", 3).is_some());
    /// assert_eq!(node.get_or_update_child(b"foobar", 4).expect("None child").value, Some(3));
    /// assert_eq!(node.get_or_update_child(b"foobar", 5).expect("None child").value, Some(4));
    ///
    /// let mut new_node: HashMapTrieFreq<_, u8> = HashMapTrieFreq::new();
    /// // Empty path always returns some child
    /// assert!(new_node.get_or_update_child(b"", 1).expect("None child").value.is_none());
    /// assert!(new_node.get_or_update_child(b"a", 2).is_none());
    /// assert!(new_node.get_or_update_child(b"ab", 3).is_none());
    /// assert!(new_node.get_or_update_child(b"abc", 4).is_none());
    /// # assert_eq!(new_node.all_valued_children().len(), 4);
    /// # let node_a = new_node.get_child(b"a").expect("None node at path 'a'");
    /// # assert_eq!(new_node.all_valued_children().len(), 4);
    /// # assert!(node_a.get_child(b"b").is_some());
    /// let mut node_a = new_node.get_child_mut(b"a").expect("None node 'a'");
    /// let a_prefixed_len = node_a.all_valued_children().len();
    /// // get_or_update_child WILL DROP node_b children
    /// assert_eq!(node_a.get_or_update_child(b"b", 5).expect("None child").value, Some(3));
    /// assert_ne!(node_a.all_valued_children().len(), a_prefixed_len);
    /// ```
    fn get_or_update_child(&mut self, path: &[K], value: V) -> Option<Self>
    where
        V: Into<Self>,
    {
        // TODO: preserve children
        if path.is_empty() {
            let mut tmp: Self = value.into();
            std::mem::swap(self, &mut tmp);

            return Some(tmp);
        }

        if path.len() == 1 {
            return self.insert_or_get_direct_child(&path[0], value.into());
        }

        self.get_or_insert_direct_child(&path[0], Self::new())
            .get_or_update_child(&path[1..], value)
    }

    /// Returns the mutable reference of the existing child at key `key`.
    /// If it does not exist, inserts `child` to `self.children` and returning that new child.
    #[inline(always)]
    fn get_or_insert_direct_value<T, Q>(&mut self, key: Q, value: T) -> &mut Self
    where
        Q: std::ops::Deref<Target = K>,
        T: Into<Self>,
    {
        self.get_or_insert_direct_child(key, value.into())
    }

    fn insert_child(&mut self, path: &[K], child: Self) {
        // if path.is_empty() {
        //     *self = child;
        //     return;
        // }
        //
        // self.children
        //     .entry(path[0].clone())
        //     .or_insert(Self::new())
        //     .insert_child(&path[1..], child);

        let mut curr = self;
        for p in path {
            let next = curr.get_or_insert_direct_value(p, Self::new());
            curr = next;
        }

        *curr = child;
    }

    /// ```
    /// # use soytrie::{HashMapTrie, TrieNode};
    /// let mut node: HashMapTrie<u8, _> = HashMapTrie::new();
    ///
    /// node.insert_value(b"a", "a"); // This adds valued node at "a"
    /// node.insert_value(b"ab", "ab"); // This adds valued node at "b"
    /// node.insert_value(b"abcde", "abcde"); // This adds path nodes at "c", "d", and valued node at "e"
    ///
    /// assert_eq!(node.all_valued_children().len(), 3); // valued nodes: "a", "b", "e"
    ///
    /// node.insert_child(b"ab", "ab".into()); // This call to insert_child drops the old value at
    /// // "b" and adds a fresh, new valued node at "b". The old "b" node's children was dropped.
    ///
    /// assert_eq!(node.all_valued_children().len(), 2); // valued nodes: "a", "b"
    /// ```
    #[inline]
    fn insert_value(&mut self, path: &[K], value: V) {
        let mut curr = self;
        for p in path {
            let next = curr.get_or_insert_direct_value(p, Self::new());
            curr = next;
        }

        curr.set_value(value);
    }

    /// Returns a boolean indicating success.
    /// ```
    /// # use soytrie::{HashMapTrie, TrieNode, SearchMode};
    /// let mut node = HashMapTrie::new();
    /// node.insert_value(b"abc", "abc"); // node at "a" is direct child, but a path node
    /// node.insert_value(b"x", "x"); // node at "x" is both direct child and valued node
    ///
    /// assert_eq!(node.has_direct_child(SearchMode::Prefix, &b'a'), true);
    /// assert_eq!(node.has_direct_child(SearchMode::Exact, &b'a'), false);
    /// assert_eq!(node.has_direct_child(SearchMode::Prefix, &b'b'), false);
    /// assert_eq!(node.has_direct_child(SearchMode::Exact, &b'b'), false);
    /// assert_eq!(node.has_direct_child(SearchMode::Prefix, &b'x'), true);
    /// assert_eq!(node.has_direct_child(SearchMode::Exact, &b'x'), true);
    /// ```
    #[inline(always)]
    fn has_direct_child<Q>(&self, mode: SearchMode, key: Q) -> bool
    where
        Q: std::ops::Deref<Target = K>,
    {
        self.get_direct_child(key).is_some_and(|child| match mode {
            SearchMode::Exact => child.is_valued(),
            SearchMode::Prefix => true,
        })
    }

    /// Recursively searchs for child at the path, returning reference to the child if it exists.
    fn get_child(&self, path: &[K]) -> Option<&Self> {
        path.is_empty().then_some(self).or_else(|| {
            self.get_direct_child(&path[0])
                .and_then(|child| child.get_child(&path[1..]))
        })
    }

    /// Recursively searchs for child at the path, returning mutable reference to the child if it exists.
    fn get_child_mut(&mut self, path: &[K]) -> Option<&mut Self> {
        if path.is_empty() {
            return Some(self);
        }

        self.get_direct_child_mut(&path[0])
            .and_then(|child| child.get_child_mut(&path[1..]))
    }

    /// Calls [swap_node_value](Self::swap_node_value) on child at `path`.
    /// ```
    /// # use soytrie::{HashMapTrie, TrieNode};
    /// let mut node = HashMapTrie::new();
    /// node.insert_value(b"foo", 1);
    /// assert!(node.swap_child_value(b"f", 2).is_none());
    /// assert_eq!(node.swap_child_value(b"f", 3), Some(2));
    /// assert_eq!(node.swap_child_value(b"foo", 4), Some(1));
    /// ```
    #[inline(always)]
    fn swap_child_value(&mut self, path: &[K], value: V) -> Option<V> {
        self.get_child_mut(path)
            .and_then(|child| child.swap_node_value(value))
    }

    /// Searchs for child at the path, returning boolean value indicating success.
    #[inline(always)]
    fn search(&self, mode: SearchMode, path: &[K]) -> bool {
        match self.get_child(path) {
            None => false,
            Some(child) => match mode {
                SearchMode::Prefix => true,
                SearchMode::Exact => child.is_valued(),
            },
        }
    }

    /// Returns all children of the node.
    /// ```
    /// # use soytrie::{HashMapTrieFreq, TrieNode};
    /// let mut node = HashMapTrieFreq::new();
    ///
    /// node.insert_value(b"a", "a"); // Adds valued node at "a"
    /// node.insert_value(b"ab", "ab"); // Adds valued node at "b"
    /// node.insert_value(b"abcde", "abcde"); // Adds path nodes at "c", "d", and valued node at "e"
    /// node.insert_value(b"xyz", "xyz"); // Adds path nodes at "x", "y", and valued node at "z"
    ///
    /// assert_eq!(node.all_children().len(), 9); // nodes: a, b, c, d, e, x, y, z and root node
    /// ```
    fn all_children<'l, 's>(&'l self) -> Vec<&'s Self>
    where
        'l: 's,
    {
        let mut children = Vec::new();
        Self::collect_children(self, &mut children);

        children
    }

    /// Returns all valued child nodes of the node.
    /// ```
    /// # use soytrie::{HashMapTrie, TrieNode};
    /// let mut node = HashMapTrie::new();
    ///
    /// node.insert_value(b"a", "a"); // This adds valued node at "a"
    /// node.insert_value(b"ab", "ab"); // This adds valued node at "b"
    /// node.insert_value(b"abcde", "abcde"); // This adds path nodes at "c", "d", and valued node at "e"
    /// node.insert_value(b"xyz", "xyz"); // Adds path nodes at "x", "y", and valued node at "z"
    ///
    /// assert_eq!(node.all_valued_children().len(), 4); // valued nodes: "a", "b", "e", and "z"
    /// ```
    fn all_valued_children<'l, 's>(&'l self) -> Vec<&'s Self>
    where
        'l: 's,
    {
        self.all_children()
            .into_iter()
            .filter(|child| child.is_valued())
            .collect()
    }

    /// Collects all values of the valued deep children of the child at path `path`,
    /// returning [`None`](None) if the child does not exist or if the child's
    /// number of children is 0. Otherwise, the references to values is collected
    /// as [`Some(Vec<&V>)`](Some). [`with_prefix`](Self::with_prefix) is aliased to `predict`.
    /// ```
    /// # use soytrie::{HashMapTrie, TrieNode};
    /// let mut node = HashMapTrie::new();
    /// node.insert_value(b"a", "a");
    /// node.insert_value(b"ab", "ab");
    /// node.insert_value(b"1234", "1234");
    ///
    /// assert!(node.predict(b"z").is_none());
    /// assert!(node.predict(b"4").is_none());
    /// assert_eq!(node.predict(b"a").unwrap().len(), 2); // "a" and "ab"
    /// assert_eq!(node.predict(b"123").unwrap().len(), 1); // "1234"
    /// assert_eq!(node.predict(b"").unwrap().len(), 3) // "a", "ab", "1234"
    /// ```
    #[inline(always)]
    fn predict(&self, path: &[K]) -> Option<Vec<&V>> {
        self.get_child(path).and_then(|child| {
            let predicted = child.all_children_values();

            if predicted.is_empty() {
                return None;
            }

            Some(predicted)
        })
    }

    /// Alias to [`Self::predict`](Self::predict)
    fn with_prefix(&self, path: &[K]) -> Option<Vec<&V>> {
        self.predict(path)
    }

    /// Reports whether the given fragment of path `frag` suffices to uniquely identify
    /// a _valued_ child, i.e. the shortest path without ambiguity.
    /// ```
    /// # use soytrie::{HashMapTrie, TrieNode};
    /// let mut node = HashMapTrie::new();
    /// node.insert_value(b"12345", "12345"); // "1" is not ambiguous
    /// node.insert_value(b"12222", "12222"); // "12_" is not ambiguous
    /// node.insert_value(b"01234", "01234"); // "0" is not ambiguous
    ///
    /// assert_eq!(node.non_ambiguous(b"1"), false);
    /// assert_eq!(node.non_ambiguous(b"12"), false);
    /// assert_eq!(node.non_ambiguous(b"123"), true);
    /// assert_eq!(node.non_ambiguous(b"122"), true);
    /// assert_eq!(node.non_ambiguous(b"0"), true);
    ///
    /// assert_eq!(node.non_ambiguous(b"abc"), false); // No such node
    /// ```
    fn non_ambiguous(&self, frag: &[K]) -> bool {
        self.get_child(frag)
            .is_some_and(|child| child.num_children() == 1)
    }

    /// Returns the shortest prefix length `ret` at which no ambiguity is found.
    /// `unique_prefix_len` does not checks for valued nodes, and only cares if there's
    /// a path to some child below `path[..ret]`. The valued returned will be <= `path.len()`.
    /// TODO: Improve performance
    /// ```
    /// # use soytrie::{HashMapTrie, TrieNode};
    /// let mut node = HashMapTrie::new();
    ///
    /// node.insert_value(b"1234xxx", "1234xxx");
    /// node.insert_value(b"1235xxx", "1235xxx");
    /// assert_eq!(node.unique_prefix_len(b"1234xxx"), Some(4)); // unique prefix is 123{4,5}
    /// assert_eq!(node.unique_prefix_len(b"1235xxx"), Some(4)); // unique prefix is 123{4,5}
    ///
    /// node.insert_value(b"12xxxxx", "12xxxxx");
    /// assert_eq!(node.unique_prefix_len(b"12xxxxx"), Some(3)); // unique_prefix is 12{3,x}
    /// ```
    fn unique_prefix_len(&self, path: &[K]) -> Option<usize> {
        let mut curr = self;

        for i in 0..path.len() {
            match curr.num_children() {
                0 => {
                    return None;
                }
                1 => {
                    return Some(i);
                }
                _ => match curr.get_direct_child(&path[i]) {
                    None => {
                        return Some(i);
                    }

                    Some(next) => {
                        curr = next;
                    }
                },
            }
        }

        None
    }
}

// Returns t
pub mod tests {
    use super::TrieNode;
    pub fn test_trie<T>(mut trie: T)
    where
        T: TrieNode<u8, String>,
    {
        use super::*;

        trie.insert_value(b"a", "a".to_string());
        trie.insert_value(b"ab", "ab".into());
        trie.insert_value(b"abc", "abc".into());
        trie.insert_value(b"foo", "foo".into());
        trie.insert_value(b"foobar", "foobar".into());
        trie.insert_value(b"foobar2000", "foobar2000".into());

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

        assert_eq!(trie.all_children_values().len(), 6);
        assert_eq!(trie.predict(b"a").expect("a node is None").len(), 3);
        assert_eq!(trie.predict(b"f").expect("f node is None").len(), 3);

        let foob_node = trie.get_child(b"foob");
        assert_eq!(
            foob_node
                .expect("foob node is None")
                .all_children_values()
                .len(),
            2
        );

        let foobar2000_node = trie.get_child(b"foobar2000");
        assert_eq!(
            foobar2000_node
                .expect("foobar2000 node is None")
                .all_children_values()
                .len(),
            1,
        );

        let foobar2000_node = trie.remove(b"foobar2000").expect("foobar2000 node is None");
        assert_eq!(foobar2000_node.all_children_values().len(), 1);
        assert_eq!(foobar2000_node.peek_value(), &Some("foobar2000".into()));
        let assert_check = |trie: &T| {
            assert_eq!(
                trie.all_children_values().len(),
                trie.all_valued_children().len()
            )
        };

        assert_eq!(trie.all_children_values().len(), 5);
        assert_check(&trie);

        trie.remove(b"abc"); // deletes abc
        assert_eq!(trie.all_children_values().len(), 4);
        assert_check(&trie);

        trie.remove(b"ab"); // deletes ab
        assert_eq!(trie.all_children_values().len(), 3);
        assert_check(&trie);

        trie.remove(b"ab"); // deletes ab
        assert_eq!(trie.all_children_values().len(), 3);
        assert_check(&trie);

        trie.remove(b"f"); // deletes f, fo, foo
        assert_eq!(trie.all_children_values().len(), 1);
        assert_check(&trie);

        trie.remove(b"a"); // deletes a
        assert_eq!(trie.all_children_values().len(), 0);
        assert_check(&trie);
    }

    pub fn test_unique<T>(mut node: T)
    where
        T: TrieNode<u8, usize>,
    {
        node.insert_value(b"1234000", 1);
        node.insert_value(b"1234500", 2);

        assert_eq!(node.unique_prefix_len(b"1234000").unwrap(), 5); // 1234{0}
        assert_eq!(node.unique_prefix_len(b"1234500").unwrap(), 5); // 1234{5}

        node.remove(b"1234000");
        assert_eq!(node.unique_prefix_len(b"1234500").unwrap(), 0); // Only node

        node.insert_value(b"1234000", 3);
        assert_eq!(node.unique_prefix_len(b"1234500").unwrap(), 5); // 1234{5}
    }
}
