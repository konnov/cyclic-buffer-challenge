# Checking with TLC and Apalache

This directory demonstrates how to find the bug with [TLC][] and [Apalache][].

## Breadth-First Search with TLC

> [!TIP]
> To download the CLI version of TLC, run:
> `wget https://github.com/tlaplus/tlaplus/releases/download/v1.7.4/tla2tools.jar`

To find an invariant violation for the buffer size of 2 and
`{0, 1}` as buffer elements:

```shell
$ java -cp tla2tools.jar "-XX:+UseParallelGC" tlc2.TLC \
  -config MC.cfg MC2u1_BuggyCircularBuffer.tla
```

You can try to do the same for buffer size of 10 and `0..255` as buffer
elements, but **it will eat all of your disk space!**:

```shell
$ java -cp tla2tools.jar "-XX:+UseParallelGC" tlc2.TLC \
  -simulate -config MC.cfg MC10u8_BuggyCircularBuffer.tla
```

## Random Simulation with TLC

To find an invariant violation for the buffer size of 10:

```shell
$ java -cp tla2tools.jar "-XX:+UseParallelGC" tlc2.TLC \
  -simulate -config MC.cfg MC10u8_BuggyCircularBuffer.tla
```

To bump the buffer size to 100:

```shell
$ java -cp tla2tools.jar "-XX:+UseParallelGC" tlc2.TLC \
  -simulate -config MC.cfg MC100u8_BuggyCircularBuffer.tla
```

## Bounded Model Checking with Apalache

> [!TIP]
> To download the Apalache docker image, run:
> `docker pull ghcr.io/apalache-mc/apalache`

To find an invariant violation for the buffer size of 10:

```shell
$ docker run --rm -v `pwd`:/var/apalache ghcr.io/apalache-mc/apalache \
  check --inv=SafeInv --length=20 MC10u8_BuggyCircularBuffer.tla
```

## Randomized Symbolic Execution with Apalache

```shell
$ docker run --rm -v `pwd`:/var/apalache ghcr.io/apalache-mc/apalache \
  simulate --inv=SafeInv --length=20 MC10u8_BuggyCircularBuffer.tla
```


[TLC]: https://github.com/tlaplus/tlaplus/
[Apalache]: https://apalache-mc.org/