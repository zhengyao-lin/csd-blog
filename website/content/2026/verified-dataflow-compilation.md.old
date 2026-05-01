+++
title = "Formally Verified Dataflow Compilation"
date = 2026-01-29

[taxonomies]
areas = ["Programming Languages"]
tags = ["Compiler Verification", "Theorem Proving", "Lean", "Dataflow", "HLS", "CGRA"]

[extra]
author = {name = "Zhengyao Lin", url = "https://zhengyao.page/" }
committee = []
+++

<!-- Overview:
1. Background and motivation
   - What is dataflow architecture and compilation
   - Why is dataflow compilation difficult
2. Formally verifying dataflow compilation
3. Determinacy
4. Conlusion -->

<!-- Dataflow architectures, unlike traditional von Neumann architectures predominant in CPUs, execute programs represented as a *dataflow graph* without any explicit control-flow. -->

*Dataflow architectures* [cgra-survey] are computer architectures designed to directly execute programs represented as *dataflow circuits*, which consist of a set of operators (instructions) with data dependencies between them, but without any implicit control flow (i.e., no "next" instruction, jumps, or basic blocks).

The lack of control flow has two main advantages: parallelism and data locality.
In a dataflow circuit, *all* operators run in parallel, and they can execute as soon as their inputs are ready.
This is like out-of-order execution in CPUs, but it is done statically on the whole program, so that the hardware does not need additional complexity to analyze dependencies.
The explicit data dependencies in dataflow circuits also inform well-designed architectures to directly send data from the producer to the consumer without going through memories, which reduces data movement costs and can improve power consumption by 100x in some applications [riptide,tyr].

For these reasons, modern dataflow architectures such as *coarse-grained reconfigurable arrays (CGRAs)* [cgra-survey] are receiving increasing attention from the architecture community in recent years, accelerating applications in machine learning [?], signal processing [?], and edge computing [?].

The benefits of dataflow circuits come with a catch, however, and that is the increased complexity of the compiler.
To ensure programmability, a compiler targeting a dataflow architecture has to translate a sequential, usually imperative, program (e.g., in C) into an equivalent dataflow circuit.
This means that the compiler needs to turn a sequential program into a concurrent one (where each instruction runs in its own parallel process!), and ensure that the output dataflow circuit (1) behaves the same way as the source program, and (2) does not have any concurrency issues like deadlocks and data races.

To see these challenges more concretely, here are two examples.

Example 1: Data race introduced by the compiler.

Use a loop `for i do A[i] = B[i]` and consider cases when `A` and `B` could alias or not.

Example 2: Deadlocks introduced by the compiler (maybe rewriter?).

<!-- A dataflow graph is inherently parallel: any instruction or operator in a dataflow graph can execute whenever they have input data available.
From the perspective of computer architects, dataflow graphs also have great data locality, because each instruction knows exactly which next instruction to send the output data to, without having to repeatedly write to/read from the memory. -->
<!-- 
By utilizing these features of dataflow graphs, decades of research on dataflow architectures[?] have shown that the right design can achieve orders-of-magnitube better energy-efficiency than von Neumann architectures that are predominant in CPUs, without sacrificing, or even improving, performance. -->
<!-- 
However, the Achilles' heel of dataflow architectures is programmability.
Directly writing a *correct* dataflow graph is hard, for the same reasons that concurrent programming is difficult: without an explicit, synchronized control-flow, a dataflow graph can easily have deadlocks and data races.
TODO: expand more -->

<!-- That's why in this blog post, I'm going to go over my work on formally verifying dataflow compilation, yada yada. -->

<!-- TODO:
- Simple example(s)
- The problems
- How to verify -->

# Formally verifying (dataflow) compilation

While extensive testing can alleviate these issues in general, the parallel nature of dataflow circuits makes it difficult to discover concurrency bugs via simple testing.
In our work, we turn to formal verification: we formalize and prove that a dataflow compiler is free of the aforementioned issues, using the Lean theorem prover [?].

At a very high level, compiler verification generally involves:

1. Formalizing the semantics of input, output, and any intermediate representations (IRs) used in the compiler. That is, we need to mathematically describe the meaning of programs in these languages.
2. Prove that the compiler (which also has to be formalized) always produces an output program that is "equivalent" to the input program.

Let us get into more details of what these steps mean in our context.
For (1), we use *(small-step) operational semantics* to describe programming language semantics in this blog post.
Essentially, an operational semantics formalizes the meaning of a program as a labeled transition system (i.e., an automaton), where the potentially infinite state space represents program execution states (program counter, memory state, values bound to local variables, etc.), and transitions from a state represents possible "next steps" of execution.
There are some tricky details about how to actually define this transition relation based on the syntax of the program, but for now, you can simply think of the meaning of a program as an (infinite) automaton.

<!-- Each transition is usually labelled by the action or effect done in that step. -->

<!-- So now you can think of the meaning of any program (input, output, or intermediate) involved in the compiler as a transition system. -->

Now let's say that the compiler takes an input program \\(A\\) and translates it to an output program \\(B\\).
Using the operational semantics, we can now define the meaning of these programs as labelled transition systems, denoted as \\(\llbracket A \rrbracket := (S, s_0, \to_s: S \times \Sigma \times S)\\) and \\(\llbracket B \rrbracket := (T, t_0, \to_t: T \times \Sigma \times T)\\), where \\(S\\) and \\(T\\) are the state spaces, \\(s_0\\) and \\(t_0\\) are the initial states, and \\(\to\\)'s are the labelled transition relations using labels in a common label set \\(\Sigma\\) (i.e., the alphabet in automata terms).
The ultimate goal is to prove that \\(\llbracket A \rrbracket\\) and \\(\llbracket B \rrbracket\\) are "equivalent" automata, but what does that mean?

There are a number of definitions of such "equivalence" we can choose from.
For example, one may be attempted to say that \\(\llbracket A \rrbracket\\) and \\(\llbracket B \rrbracket\\) are isomorphic as graphs (think of \\(S\\) as nodes and \\(\to\\) as edges).
However, this is too strong and usually not true for compilers, for a few reasons.
First, we want to allow optimizations such as dead code elimination.
They change the behavior of the program, but not in a way that is observable by the end user.
Second, we don't necessarily want \\(\llbracket B \rrbracket\\) to preserve *all* the behavior of \\(\llbracket A \rrbracket\\).
Think of a C program with an undefined behavior: while the source program may either crash or print a unicorn, per the specification, the compiler may choose one of those behaviors in the output program.

Therefore, in our case, we use the notion of *simulation*:
> **Definition (Backward Simulation).**
> Given a binary relation \\(R : S \times T\\), we say that \\(R\\) is a *simulation* between \\(\llbracket A \rrbracket\\) and \\(\llbracket B \rrbracket\\) if:
> - \\(R(s_0, t_0)\\), i.e., the initial states are related.
> - For any state \\(s \in S, t \in T\\), if \\(R(s, t)\\) and \\(s \overset{l}{\to} s\'\\), then there exists some \\(t\'\\), such that \\(t \overset{l}{\to} t\'\\) and \\(R(s', t')\\).

Intuitively, the second requirement says that for any pair of related states, if \\(B\\) makes a step, then \\(A\\) can make a corresponding step that result again in a pair of related states.
In particular, if we can show that such simulation relation \\(R\\) exists, then there is a *trace refinement*: any trace of \\(\llbracket B \rrbracket\\) is a trace of \\(\llbracket A \rrbracket\\).
In other words, any behavior of \\(\llbracket B \rrbracket\\) has a corresponding behavior in \\(\llbracket A \rrbracket\\).

In reality, this definition is still slightly too strong, because, for example, \\(B\\) may have internal steps (e.g., setting up stacks) that do not correspond to any step in \\(A\\).
We omit these cases in this blog post for simplicity.

## How to prove simulation and challenges of dataflow compilation

The definition above is a *backward* simulation, because relative to the compiler which translates \\(A\\) to \\(B\\), we are proving that \\(B\\) is simulated by \\(A\\).
However, what is usually done by verified compilers such as CompCert [?] is to show the other direction first: i.e., a *forward* simulation that \\(A\\) is simulated by \\(B\\).
This is because \\(B\\), as a more concrete program (think assembly), usually requires more internal steps than \\(A\\), so it is easier to perform induction on the more abstract steps of \\(A\\), and then show that \\(B\\) has corresponding steps.
Then, assuming a deterministic semantics (i.e., any state has at most one transition), we can show that forward simulation implies backward simulation.

However, the last step of turning a forward simulation to a backward simulation is where the traditional strategy breaks down for dataflow compilation.
Semantics of dataflow circuits (the target program \\(B\\)) is concurrent and non-deterministic, while the semantics of the input program \\(A\\) is sequential, imperative, and deterministic.
As a result, it is easy for the compiler to incorrectly introduce more behaviors in \\(B\\) than \\(A\\) (e.g., data races and deadlocks), and it is much more difficult to show the absence of these buggy behaviors.

In our formalization of a dataflow compiler in Lean, we adopt a novel proof strategy, where we first prove forward simulation in the traditional way (i.e., the behavior of \\(B\\) includes the behavior of the source program \\(A\\)).
In the second part, using a combination of typing and simulation, we show that the dataflow circuit \\(B\\) is *determinant*: it always produces the same result, even if intermediate states may be non-deterministic due to execution schedule or timing.

By combining the forward simulation and the second determinancy results, we are then able to prove that the input sequential program \\(A\\) and output dataflow circuit \\(B\\) always produce the same results, and \\(B\\) is free of data races and deadlocks.

## Proving determinacy

Proving that the dataflow circuit \\(B\\) is determinant (that it produces the same result regardless of schedule) becomes tricky when different operators can access a shared memory and there could be data races.
In our work, we rule out the possibility of data races entirely through the use of *affine permission tokens* [?].

The idea is that, in the dataflow circuit \\(B\\), which consists of a large number of distributed operators communicating with each other through channels, whenver a memory load/store operator needs access to the memory, it needs to possess the suitable permission token for the memory region it tries to read/write.
Then, when the operator is done with reading/writing, the token is passed through channels to other nodes, when in turn gives other operators access to the same region.
Most importantly, these tokens are *affine*, in the sense that operators cannot duplicate or create new tokens.
These tokens are also *ghost* tokens, because they only exist in the reasoning about the dataflow circuit, and the actual execution of \\(B\\) will treat them as control/synchronization signals at the hardware level.

Our proof obligation then becomes proving that there exists a consistent way the produced circuit can distribute these affine permission tokens.
In terms of proof engineering, the challenging part is to find a formulation of this property that allows it to propagate through various compiler passes and existing forward simulation proofs without any additional proof changes.
We refer the reader to our full paper for details on how this is done [?].

## Pipelining and Optimizations

?

# Evaluation against unverified dataflow compilers

Formally verifying a compiler usually comes with a significant amount of human labor and cost in compilation quality (because optimizations are difficult to formally verify).
Therefore, let's see how worse our verified dataflow compiler is compared to unverified ones.

In this evaluation, we compare against two unverified compilers in two slightly pipelines:

# Related work and conclusion

- Internal determinism
