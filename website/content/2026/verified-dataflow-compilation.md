+++
title = "Compiling Programs to Dataflow Circuits, Formally Verified™"
date = 2026-01-29

[taxonomies]
areas = ["Programming Languages"]
tags = ["Compiler Verification", "Theorem Proving", "Lean", "Dataflow", "HLS", "CGRA"]

[extra]
author = {name = "Zhengyao Lin", url = "https://zhengyao.page/" }
committee = []
+++

*Dataflow architectures* [?] are computer architectures designed to directly execute programs represented as *dataflow circuits*,
which consist of a set of operators (instructions) with data dependencies between them, but without any implicit control flow
(i.e., no "next" instruction, jumps, or basic blocks).

The paradigm of dataflow has seen a re-emergence in reconfigurable dataflow architectures (RDAs) [?] and
dynamically-scheduled high-level synthesis (HLS) [?].
In RDAs, since the program is compiled to a dataflow circuit ahead of time, the architecture can be designed
to reduce energy costs in data movement (e.g., moving data between registers/cache/memory and ALUs)
and handling instructions (e.g., fetching and decoding).
These improvements can sometimes lead to over 100x better energy efficiency compared to off-the-shelf low-power CPUs [?].
In dynamically-scheduled HLS [?], by making operators in the dataflow circuit data-driven without following a
static global schedule (i.e., asynchrony), we can achieve 6x speedup on certain irregular workloads compared to
traditional statically-scheduled HLS.

A key problem, however, is that while parallelism and dynamic scheduling benefit performance, they simultaneously
create challenges for *correctness*.
When programming RDAs or using dynamic HLS, the typical workflow is to compile a high-level sequential program
(in C, for example) into an asynchronous dataflow circuit.
Each instruction in the original sequential program is converted into a parallel operator in the dataflow circuit. 
To enable realistic applications, these operators also access *shared memory*.
As a result, even a simple sequential source program becomes a highly distributed system with both
message passing and shared memory, along with potential deadlocks and data races.

In this blog post and our related PLDI paper [?], we tackle the problem of *formally verifying* dataflow compilation,
which provably prevents any incorrect dataflow compilation and guarantees that the compiled dataflow circuit
is correct and equivalent to the source program.

## Examples and Challenges

Let us consider a simple example of dataflow compilation to get a sense of how it works and what the challenges are.
The example source program is a single relaxation step in the [Bellman-Ford algorithm](https://en.wikipedia.org/wiki/Bellman%E2%80%93Ford_algorithm).
The input is a graph represented as an edge list, where each edge `e = 1 .. E - 1` has source vertex `Src[e]`, destination vertex `Dst[e]`, and weight `W[e]`.
The current distance to each vertex is stored in the array `Dist`,
and the loop below iterates through all edges and updates the distance of a node
if a shorter path is found.
```
for 0 <= e < E
  u = Src[e]
  v = Dst[e]
  d = Dist[u] + W[e]
  if d < Dist[v]
    Dist[v] = d
```

We first compile the loop body to the dataflow circuit below.

<img src="/2026/verified-dataflow-compilation/loop-body.svg" style="height: 20em" />

This dataflow circuit is essentially a collection of memory and arithmetic operations
in the loop body: we have the load operators (`LD`) for each array that takes an index
to be loaded from, store operators (`ST`) that stores the input value to the input index,
and arithmetic operators (`+` and `<`).
The two steer operators (`T`) are used for encoding branching.
It takes an input value and a branch condition (in this case computed by the comparison
operator), forwards the value to the output if the condition is true, and otherwise
discards the input.
Besides the operators, the channels (edges) between them reflect the data-
and control-dependencies in the source imperative program.

Semantically, these operators mentioned above are data-driven and parallel: they each
act like a small recursive process that waits for inputs, does the operation, and
pushes outputs to its output channels.
The channels between them are queues with non-blocking send (except on full buffer)
and blocking reads.
As a result, operators without dependencies between them can potentially run in parallel,
modulo hardware timing.
For instance, the three loads for `Src`, `Dst`, `W` can be executed simultaneously,
and then in the next step, the two loads for `Dist` and the addition `+` can also run in parallel.


**Memory Ordering.**
While such parallelism is great for performance, it also leads to
correctness issues in memory ordering.
To see this, we compile the loop header as well in the following extended circuit, where the
additional part of the circuit annotated with `LH` (for loop header) will emit a sequence
of edges `0 .. E - 1` to the loop body circuit.

(IMAGE)

However, now we have an issue with memory ordering.
The loads and store to `Dist` have various dependencies that are *originally* enforced by the
sequential control-flow; e.g., loads in the next iteration may overlap with the store in
the previous iteration with a read-after-write dependency.
They are now lost due to the more parallel semantics of dataflow circuits, since it is possible
that on certain execution schedules, the `LD` of `Dist` in the second iteration runs in parallel
with the `ST` of `Dist` in the first iteration, resulting in a potential *data race*.

There are in general two solutions to the memory ordering issue.
The first is to use a *load-store queue* [?], which is an additional hardware unit that
dynamically commits memory operations in a safe order.
Out-of-order execution in CPUs (which is also dataflow in a sense) sometimes uses load-store queues
for correct memory ordering.

However, we are focusing on a second pure-dataflow approach to avoid the additional hardware complexity,
which is to add an additional data dependency as a back-edge from the `ST` to the `LD` of `Dist` to
send a *memory synchronization* signal.
This way, we can make sure that `LD`s of `Dist` will always wait for the `ST` in the previous iteration
to finish, avoiding any data races.

(IMAGE)

In tension with avoiding data races, the dataflow compiler still needs to extract as much parallelism
as possible and avoid overly synchronizing the dataflow circuit, since otherwise it would lose the
parallelism benefits of the hardware.

**Other Correctness Issues.**
Besides data races, *deadlocks* could also happen in an asynchronous dataflow circuit.
The channels between operators have a finite buffer size, and a sender has to wait if its output channel is full,
blocking its own execution and potentially the execution of any upstream operators.

In general, a correct dataflow compiler must make sure that over *all possible execution schedules*, the parallel
dataflow circuit behaves equivalently to the source program.
Larger applications may scale to hundreds of operators, such as the following dataflow circuit for computing SHA-256
compiled by the RipTide [?] dataflow compiler, and debugging an incorrect dataflow circuit with data races and
deadlocks would be a nightmare.

(IMAGE)

## Wavelet: A Formally Verified Dataflow Compiler

The goal of our research is to use *formal verification* to prove the absence of any dataflow issues mentioned in the
previous section.
We have recently built prototype dataflow compiler called Wavelet [?], with its core passes verified in the Lean theorem
prover [?], guaranteeing that it always generates correct dataflow circuits.
We briefly summarize our approach in this section with examples, and refer the reader to our full paper [?] for details.

Wavelet consists of five compilation passes.
Its input language is a simple imperative language called \\(\mathbb{L}_{let}\\),
which is equipped with a capability type system and a construct called *fence* to
soundly mark synchronization points.

\\(\mathbb{L}_{let}\\) is currently embedded in Rust,
and a lightly abridged example looks like this,
where `f` maps each element of an array A from `i` to `n` through another function `g`,
whose body is omitted.
```Rust
#[cap(A: uniq @ i..n)]
fn f(i: u32, n: u32) {
  if i < n {
    let x = load_A(i);
    let y = g(x);
    fence!();
    let () = store_A(i, y);
    f(i + 1, n)
  } else { () }
}

#[cap()]
fn g(x: u32) -> u32 { ... }
```

We only support tail recursion and branching as the two primitive control-flow
constructs for a clearer correspondence to dataflow circuits, but most loops can be easily
reduced to this form.
Each function needs to be annotated with an initial *capability*, in this case
`A: uniq @ i..n`, which means that the function requires the unique or write capability
for the array `A` from indices `i` to `n`.
In the body, the user needs to occasionally add an annotation of `fence!()`, which tells
the type checker to reclaim any used capabilities for future memory operations.
Here in the example, `load_A(i)` consumes the capability for `A[i]`.
In order to type-check `store_A(i, y)`, which may conflict with `load_A(i)` if run in parallel,
we have to add a `fence!()` for synchronization.

## Comparison with RipTide and LLVM CIRCT

## Related Work
