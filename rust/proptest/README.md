# Testing with Rust proptest

This directory demonstrates how to find the bug [proptest][] in Rust.

## Testing with proptest

To find an invariant violation for the buffer size of 10:

```shell
$ cargo test
```

To bump the buffer size to 100, also bump the number of tests accordingly:

```shell
$ BUF_SIZE=100 PROPTEST_CASES=10000 cargo test
```

[proptest]: https://docs.rs/proptest/latest/proptest/