# Fuzzing with AFLplusplus

This directory demonstrates how to find the bug with [AFLplusplus][].

## Fuzzing Binary Inputs

To find an invariant violation for the buffer size of 10 when using
binary files as inputs:

```shell
$ make fuzz-binary
```

To bump the buffer size to 100, edit the `BUF_SIZE` constant:

```shell
$ BUF_SIZE=100 make fuzz-binary
```

## Fuzzing Text Inputs

To find an invariant violation for the buffer size of 10 when using
text files as inputs:

```shell
$ make fuzz-text
```

To bump the buffer size to 100, edit the `BUF_SIZE` constant:

```shell
$ BUF_SIZE=100 make fuzz-text
```


[AFLplusplus]: https://aflplus.plus/