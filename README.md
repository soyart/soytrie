# soytrie

soytrie is a simple, generic Rust implementation of trie using hash map.

## Features

It supports insertion, deep insertion, searching, prediction,
   deletion, and deep deletion.

## Examples

```rust

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

let foob_node = trie.root.search_child(b"foob");
assert_eq!(
    foob_node.expect("foob node is None").all_children().len(),
    2
);

let foobar2000_node = trie.search_child(b"foobar2000");
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
```
