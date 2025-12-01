# Buggy Cyclic Buffer Challenge

A bug finding challenge for all of the tools around. Are you tired of everyone
selling you **the best tool in town**? Well, the truth is, there is no one tool
that works best for every problem. Here is a simple challenge that demonstrates
what kind of compromises we have to make.

Want to add your tool? Fork the repository and make a PR!

*For professional consulting, verification reports, or adaptation of these
methods, see [konnov.phd][] and [protocols-made-fun.com][].*

## The Challenge

The challenge is to find a bug in a simple cyclic buffer implementation. The
buffer has a fixed size (e.g., 10, 100) and supports two operations: `write` and
`read` (or `put` and `get`). The bug is that the buffer does not correctly
handle the case when the buffer is full and a `write` operation is performed. In
this case, the buffer should either overwrite the oldest data or reject the
`write` operation, but the buggy implementation allows overwriting without
proper checks, leading to data loss.

## Approaches

We leverage different tools and techniques to find this bug, including model
checking, fuzzing, property-based testing, and random simulation.

| Directory | Tool/Framework | Approach | Details |
|-----------|---------------|----------|---------|
| [`c/`](c/) | [AFLplusplus](https://aflplus.plus/) | Fuzzing (binary & text inputs) | [README](c/README.md) |
| [`tla/`](tla/) | [TLC](https://github.com/tlaplus/tlaplus/) | Breadth-first search, Random simulation | [README](tla/README.md) |
| [`tla/`](tla/) | [Apalache](https://apalache-mc.org/) | Bounded model checking, Randomized symbolic execution | [README](tla/README.md) |
| [`quint/`](quint/) | [Quint](https://quint-lang.org/) | Randomized simulation | [README](quint/README.md) |
| [`quint/`](quint/) | [Quint](https://quint-lang.org/) + [Apalache](https://apalache-mc.org/) | Bounded model checking, Randomized symbolic execution | [README](quint/README.md) |
| [`rust/proptest/`](rust/proptest/) | [proptest](https://docs.rs/proptest/latest/proptest/) | Property-based testing | [README](rust/proptest/README.md) |

[konnov.phd]: https://konnov.phd/
[protocols-made-fun.com]: https://protocols-made-fun.com/