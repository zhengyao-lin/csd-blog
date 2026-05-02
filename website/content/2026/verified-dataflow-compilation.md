+++
title = "Verified Compilation to Dataflow Circuits"
date = 2026-05-02

[taxonomies]
areas = ["Programming Languages"]
tags = ["Compiler Verification", "Theorem Proving", "Lean", "Dataflow", "HLS", "CGRA"]

[extra]
author = {name = "Zhengyao Lin", url = "https://zhengyao.page/" }
committee = []
+++

*Dataflow architectures* are computer architectures designed to directly execute programs represented as *dataflow circuits*,
which consist of a set of operators (instructions) with data dependencies between them, but without any implicit control flow
(i.e., no "next" instruction, jumps, or basic blocks).

The paradigm of dataflow has seen a re-emergence in reconfigurable dataflow architectures (RDAs) [^riptide] [^pipestitch] [^ripple] [^tyr] [^plasticine] and
dynamically-scheduled high-level synthesis (HLS) [^dynamatic].
In RDAs, since the program is compiled to a dataflow circuit ahead of time, the architecture can be designed
to reduce energy costs in data movement (e.g., moving data between registers/cache/memory and ALUs)
and handling instructions (e.g., fetching and decoding).
These improvements can sometimes lead to over 100\\(\times\\) better energy efficiency compared to off-the-shelf low-power CPUs [^riptide].
In dynamically-scheduled HLS [^dynamatic], by making operators in the dataflow circuit data-driven without following a
static global schedule (i.e., asynchrony), we can achieve 6\\(\times\\) speedup on certain irregular workloads compared to
traditional statically-scheduled HLS.

A key problem, however, is that while dataflow and dynamic scheduling benefit energy efficiency and performance, they simultaneously
create challenges for *correctness*.
When programming RDAs or using dynamic HLS, the typical workflow is to compile a high-level sequential program
(in C, for example) into an asynchronous dataflow circuit.
Each instruction in the original sequential program is converted into a parallel operator in the dataflow circuit.
To enable realistic applications, these operators also access *shared memory*.
As a result, even a simple sequential source program becomes a highly distributed system with both
message passing and shared memory, along with potential deadlocks and data races.

In this blog post adapted from our PLDI paper [^wavelet], we tackle the problem of *formally verifying* dataflow compilation,
which provably rules out compilation issues and guarantees that the compiled dataflow circuit
is equivalent to the source program.

## Examples and Challenges

Let us consider a simple example of dataflow compilation to get a sense of how it works and what the challenges are.
The example source program is a single relaxation step in the [Bellman-Ford algorithm](https://en.wikipedia.org/wiki/Bellman%E2%80%93Ford_algorithm).
The input is a graph represented as an edge list, where each edge `e = 0 .. E - 1` has source vertex `Src[e]`, destination vertex `Dst[e]`, and weight `W[e]`.
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

<center>
<img src="/2026/verified-dataflow-compilation/loop-body.png" style="height: 18em" />
</center>

This dataflow circuit is essentially a collection of memory and arithmetic operations
in the loop body: we have the load operators (`LD`) for each array that take an index
to be loaded from, store operators (`ST`) that store the input value at the input index,
and arithmetic operators (`+` and `<`).
The two steer operators (`T`) are used for encoding branching.
Each takes an input value and a branch condition (in this case computed by the comparison
operator), forwards the value to the output if the condition is true, and otherwise
discards the input.
Besides the operators, the channels (edges) between them reflect the data-
and control-dependencies in the source imperative program.

Semantically, these operators are data-driven and parallel: each
acts like a small recursive process that waits for inputs, does the operation, and
pushes outputs to its output channels.
The channels between them are queues with non-blocking sends (except on full buffer)
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
of edge indices `0 .. E - 1` to the loop body circuit.


<center>
<img src="/2026/verified-dataflow-compilation/loop-header.png" style="height: 18em" />
</center>

However, now we have an issue with memory ordering.
The loads and stores to `Dist` have various dependencies that are *originally* enforced by the
sequential control flow; e.g., loads in the next iteration may overlap with the store in
the previous iteration with a read-after-write dependency.
These dependencies are now lost due to the parallel semantics of dataflow circuits, since it is possible
that on certain execution schedules, the `LD` of `Dist` in the second iteration runs in parallel
with the `ST` of `Dist` in the first iteration, resulting in a potential *data race*.

There are in general two solutions to the memory ordering issue.
The first is to use a *load-store queue* [^dynamatic], which is an additional hardware unit that
dynamically commits memory operations in a safe order.
Out-of-order execution in CPUs (which is also dataflow in a sense) sometimes uses load-store queues
for correct memory ordering.

However, we are focusing on a second pure-dataflow approach to avoid the additional hardware complexity,
which is to add an additional data dependency as a back-edge from the `ST` to the `LD` of `Dist` to
send a *memory synchronization* signal.
This way, we can make sure that `LD`s of `Dist` will always wait for the `ST` in the previous iteration
to finish, avoiding any data races.
These additional data dependencies are denoted by green edges below in our final dataflow circuit.

<center>
<img src="/2026/verified-dataflow-compilation/full.png" style="height: 18em" />
</center>

In tension with avoiding data races, the dataflow compiler still needs to extract as much parallelism
as possible and avoid overly synchronizing the dataflow circuit, since otherwise it would lose the
parallelism benefits of the hardware.

**Other Correctness Issues.**
Besides data races, *deadlocks* can also occur in an asynchronous dataflow circuit.
The channels between operators have a finite buffer size, and a sender has to wait if its output channel is full,
blocking its own execution and potentially the execution of any upstream operators.

In general, a correct dataflow compiler must make sure that over *all possible execution schedules*, the parallel
dataflow circuit behaves equivalently to the source program.
Larger applications may scale to hundreds of operators, such as the following dataflow circuit for computing SHA-256,
compiled by the RipTide [^riptide] dataflow compiler, and debugging an incorrect dataflow circuit with data races and
deadlocks would be a nightmare.

<center>
<img src="/2026/verified-dataflow-compilation/sha256.svg" />
</center>

## Wavelet: A Formally Verified Dataflow Compiler

The goal of our research is to use *formal verification* to prove the absence of any dataflow issues mentioned in the
previous section.
We have recently built a prototype dataflow compiler called Wavelet [^wavelet], with its core passes verified in the [Lean](https://lean-lang.org/) theorem
prover, guaranteeing that it always generates correct dataflow circuits.
We briefly summarize our approach in this section with examples, and refer the reader to our full paper [^wavelet] for details.

**Source Language and Type System.**
The input language of Wavelet is a simple imperative language called \\(\mathbb{L}\_{let}\\),
which is equipped with a *capability type system* that tracks which parts of memory are permitted to be accessed,
and a construct called *fence* to soundly mark synchronization points.

\\(\mathbb{L}\_{let}\\) is currently embedded in Rust,
and a lightly abridged example looks like this,
where `f` maps each element of the array `A` from `i` to `n` through another function `g`,
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
In the body, the user occasionally needs to add a `fence!()` annotation, which tells
the type checker to reclaim any used capabilities for future memory operations.
Here in the example, `load_A(i)` consumes the capability for `A[i]`.
In order to type-check `store_A(i, y)`, which may conflict with `load_A(i)` if run in parallel,
we have to add a `fence!()` for synchronization.

**Elaboration.**
Using these capabilities and fence annotations, Wavelet then elaborates the source
\\(\mathbb{L}\_{let}\\) program into an \\(\mathbb{L}^*\_{let}\\) program,
which replaces the capability types and fences with explicit permission variables,
and represents memory ordering with the data dependencies of permission variables.
```Rust
fn f(i: u32, n: u32, p: uniq A[i..n]) {
  if i < n {
    let (p1, p2) = join_split(p);     // p1: uniq A[i], p2: uniq A[i+1..n]
    let (x, p3) = load_A(i, p1);      // p3: uniq A[i]
    let y = g(x);
    let ((), p4) = store_A(i, y, p3); // p4: uniq A[i]
    f(i + 1, n, p2)
  } else { () }
}
```
Each permission variable denotes a unique or shared permission to a slice of an array and
can only be used at most once (i.e., they are affine).
The permission variables can be manipulated with a special ghost function `join_split(...)`,
which combines the input permissions and splits them in a way that would satisfy the following
usage of the output permissions.

In essence, this elaboration step converts *implicit* memory ordering enforced by sequential
control flow into *explicit* data dependencies, in order to facilitate further compilation to
dataflow circuits.
At this point, any two adjacent operations in the program can reorder without affecting
the final result, as long as no data dependency is violated.
In particular, the call to `store_A` in the example and the tail recursive call to `f`
can run in parallel, since they do not have any data dependencies between them.

**Dataflow Compilation.**
In the core passes of Wavelet, we translate this \\(\mathbb{L}^*\_{let}\\) program
into a dataflow circuit, formalized in a dataflow calculus called \\(\mathbb{L}\_{flow}\\).
The compiled example looks like the following.

<center>
<img src="/2026/verified-dataflow-compilation/wavelet-circuit.png" style="height: 18em" />
</center>

In Wavelet, each function is individually compiled to a dataflow circuit, potentially with
references to other functions (like `g` in this circuit), and we have a separate linking
pass to syntactically "stitch" the circuits into one final circuit.
This dataflow circuit can then be optimized and mapped to RDAs like RipTide [^riptide] or
further lowered to hardware designs for dynamically-scheduled HLS.

**Formal Verification.**
In total, Wavelet consists of two front-end passes for type checking and elaboration,
two core passes for translating sequential functions into a single dataflow circuit,
and a final pass for optimization and lowering to backends.
The two core passes are *formalized and verified* in the Lean theorem prover, proving two
important properties about the compiler:

- *Forward Simulation*: The input program is (weakly) simulated by the output dataflow circuit, essentially meaning that the dataflow circuit has at least one schedule that provably behaves the same as the input program.
- *Determinacy*: The dataflow circuit has a deterministic result, no matter which execution schedule we choose.

Together, these two results guarantee that the produced dataflow circuit behaves exactly the same
as the input source program over all schedules, and also rule out the possibility of any deadlock
or data race in the dataflow circuit.

A key novelty of Wavelet is how the determinacy property is formally verified in a modular way
across the entire pipeline, without any changes to the forward simulation proofs.
Our front-end type checker and elaboration validate an important assumption of our determinacy
theorem, which is that there exists a placement of disjoint *permission tokens*, so that they can
flow through the dataflow circuit in an affine way (i.e., no duplication or creation of new tokens).
This guarantee is formulated as a progress property that is preserved through various forward
simulations, and is then finally used for determinacy theorems at the dataflow level.

## Comparison with RipTide and LLVM CIRCT

We compared Wavelet with two existing, unverified dataflow compilers in RipTide [^riptide] and
[LLVM CIRCT](https://circt.llvm.org/), in terms of the performance and resource usage of dataflow circuits compiled
from a collection of 10 benchmark programs from RipTide.
The results are shown below.

<center>
<img src="/2026/verified-dataflow-compilation/eval.svg" />
</center>

RipTide is an RDA focusing on energy efficiency and general-purpose programmability, and we used
dataflow-level simulators for both RipTide and Wavelet, collecting the number of simulation steps and
operators in the compiled dataflow circuit.
In the comparison, we also include results for the RipTide compiler without the *streamification*
optimization, which replaces a set of operators that compute the loop variable and condition
with a single `Stream` operator.
Since Wavelet does not have this dataflow graph rewrite, excluding it yields a fairer comparison
of the base compilation strategies.
Overall, without the stream operator, Wavelet is 1.69\\(\times\\) slower and produces 2.26\\(\times\\)
larger dataflow circuits than RipTide.
We attribute this gap to the different memory ordering strategy in Wavelet, which induces more
synchronization signals than RipTide.

[CIRCT](https://circt.llvm.org/) is a collection of MLIR-based IRs and compilers for hardware design, and we are
specifically using a compilation pipeline in CIRCT for dynamically-scheduled HLS.
We compile the source programs using both Wavelet and CIRCT to an intermediate MLIR dialect called
[`handshake`](https://circt.llvm.org/docs/Dialects/Handshake/), and then further lower it to RTL designs in SystemVerilog using CIRCT itself.

Wavelet-compiled dataflow circuits are 1.2\\(\times\\) slower than CIRCT-compiled circuits, but use only
about 70% of CIRCT's resources.
The difference in resource usage is mostly due to different control-flow primitives used in CIRCT,
which uses a [`control_merge` operator](https://circt.llvm.org/docs/Dialects/Handshake/#handshakecontrol_merge-circthandshakecontrolmergeop)
for handling jumps between basic blocks.

## Related Work

Dataflow as a general idea has seen wide applications such as in dataflow architectures,
stream processing, and functional reactive programming.
If you are interested in reading more, here are some references to recent papers
on programming languages and formal verification for these topics:

- Languages and formal verification for asynchronous dataflow
  + Graphiti: Formally Verified Out-of-Order Execution in Dataflow Circuits, Herklotz et al., ASPLOS 2026.
  + Ripple: Asynchronous Programming for Spatial Dataflow Architectures, Ghosh et al., PLDI 2025.
  + A Mechanized Semantics for Dataflow Circuits, Law et al., OOPSLA 2025.
- Types and semantics for stream processing
  + Flo: A Semantic Foundation for Progressive Stream Processing, Laddad et al., POPL 2025.
  + Stream Types, Cutler et al., PLDI 2024.

## Acknowledgements

I would like to thank my awesome collaborators [Yi Cai](https://tracycy.com/),
[Milijana Surbatovich](https://msurbatovich.github.io/),
[Joshua Gancher](https://gancher.dev/),
and [Bryan Parno](https://www.andrew.cmu.edu/user/bparno/).

## References

[^riptide]: Graham Gobieski, Souradip Ghosh, Marijn Heule, Todd Mowry, Tony Nowatzki, Nathan Beckmann, and Brandon Lucia. 2022. RipTide: A Programmable, Energy-Minimal Dataflow Compiler and Architecture. In Proceedings of the 55th Annual IEEE/ACM International Symposium on Microarchitecture (MICRO ’22), IEEE Press, Chicago, Illinois, USA, 546–564. <https://doi.org/10.1109/MICRO56248.2022.00046>
<br></br>

[^pipestitch]: Nathan Serafin, Souradip Ghosh, Harsh Desai, Nathan Beckmann, and Brandon Lucia. 2023. Pipestitch: An energy-minimal dataflow architecture with lightweight threads. In Proceedings of the 56th Annual IEEE/ACM International Symposium on Microarchitecture (MICRO ’23), Association for Computing Machinery, Toronto, ON, Canada, 1409–1422. <https://doi.org/10.1145/3613424.3614283>
<br></br>

[^ripple]: Souradip Ghosh, Yufei Shi, Brandon Lucia, and Nathan Beckmann. 2025. Ripple: Asynchronous Programming for Spatial Dataflow Architectures. Proc. ACM Program. Lang. 9, PLDI (June 2025). <https://doi.org/10.1145/3729256>
<br></br>

[^tyr]: Nikhil Agarwal, Mitchell Fream, Souradip Ghosh, Brian C. Schwedock, and Nathan Beckmann. 2024. The TYR Dataflow Architecture: Improving Locality by Taming Parallelism. In Proceedings of the 2024 57th IEEE/ACM International Symposium on Microarchitecture (MICRO ’24), IEEE Press, Austin, TX, USA, 1184–1200. <https://doi.org/10.1109/MICRO61859.2024.00089>
<br></br>

[^plasticine]: Raghu Prabhakar, Yaqi Zhang, David Koeplinger, Matt Feldman, Tian Zhao, Stefan Hadjis, Ardavan Pedram, Christos Kozyrakis, and Kunle Olukotun. 2017. Plasticine: A Reconfigurable Architecture For Parallel Patterns. In Proceedings of the 44th Annual International Symposium on Computer Architecture (ISCA ’17), Association for Computing Machinery, Toronto, ON, Canada, 389–402. <https://doi.org/10.1145/3079856.3080256>
<br></br>

[^dynamatic]: Lana Josipović, Radhika Ghosal, and Paolo Ienne. 2018. Dynamically Scheduled High-level Synthesis. In Proceedings of the 2018 ACM/SIGDA International Symposium on Field-Programmable Gate Arrays (FPGA ’18), Association for Computing Machinery, Monterey, CA, USA, 127–136. <https://doi.org/10.1145/3174243.3174264>
<br></br>

[^wavelet]: Zhengyao Lin, Yi Cai, and Milijana Surbatovich. 2026. Let It Flow: A Formally Verified Compilation Framework for Asynchronous Dataflow. Proc. ACM Program. Lang. 10, PLDI (June 2026). <https://doi.org/10.1145/3808263>. [GitHub Repo](https://github.com/plum-umd/wavelet)
