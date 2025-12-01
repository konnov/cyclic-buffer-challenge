# Checking with Quint

This directory demonstrates how to find the bug with [Quint][].

## Randomized Simulation

To find an invariant violation for the buffer size of 10:

```shell
$ quint run --invariant=safeInv \
  --main=mc10u8_buggy_circular_buffer buggy_circular_buffer.qnt
```

If you bump the buffer size to 100, also bump the number of tests
and the number of steps in each test accordingly:

```shell
$ quint run --invariant=safeInv --max-steps=200 --max-samples=1000000 \
  --main=mc100u8_buggy_circular_buffer buggy_circular_buffer.qnt
```

## Bounded Model Checking with Apalache

To find an invariant violation for the buffer size of 10:

```shell
$ quint verify --invariant=safeInv --max-steps=20 \
  --main=mc10u8_buggy_circular_buffer buggy_circular_buffer.qnt
```

## Randomized Symbolic Execution with Apalache

To find an invariant violation for the buffer size of 10:

```shell
$ quint verify --invariant=safeInv --max-steps=20 \
  --random-transitions=true \
  --main=mc10u8_buggy_circular_buffer buggy_circular_buffer.qnt
```

[Quint]: https://quint-lang.org/