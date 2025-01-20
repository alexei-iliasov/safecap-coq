# SSI Semantics

Discussing SSI semantics we have to consider the following 
three parts:
	
1. signalling data, signalling program written in SSI GDL notation,
2. signalling plan, representing railway layout in a digital format,
3. signalling principles, formally encoding safety requirements.

All these three parts must be an agreement and establishing this would be an aim of a verification procedure. Before we can arrive at such a procedure we must give a concrete of what does it mean for SSI signalling to be correct and in the process we shall explain concrete meanings of all three ingredients and their interrelationship.


## Signalling data semantics

Signalling data in SSI is, despite its appellation, is a program. This program, once initialized into a universally predetermined keeps executing in endless cycle as is characteristic for control system. Each cycle iteration is split into three stages: processing of input telegrams, processing of internal logic dealing with route and point requests as well some other controls, and, finally, processing of output telegrams. Thus, stage one reads in state of equipment under control, stage two computes new internal state and stage three commands equipment to new state. 

At finer level, signalling program is made up of a large number of atomically executed blocks. An example of such a block would be processing of one input telegram, dealing with route setting request of a particular route and so on. 

Atomic code block level of granularity is the basis for reasoning about signalling correctness. While it would have been completely sound to reason at the level of single loop iteration, there is no practical advantage to it as signalling program are developed in stages and often aggregated from many smaller parts.

To formalize, let indexed set $SI, SL$ and $SO$ represent nest-state transitions encoding input telegrams, internal logic and output telegrams. Let $Q$ be signalling program state space such that $Q=A_0 \times A_1 \times ... A_j$ where $A_i$ is the type of i-th signalling program variable - $v_i \in A_i$; then $SI_i \subseteq Q \times Q, SL_i \subseteq Q \times Q, SO_i \subseteq Q \times Q$. Assuming, as a first approximation, that each cycle iteration executes every input telegram, internal logic and output telegrams code block in some order, we can write for a signal iteration $T \in Q \times Q$:

$$
T = SI_0 ; SI_1; ... ; SI_k ; SL_0; SL_1; ... SL_m; SO_o; SO_1, ..., SO_n
$$

Assuming $I \subseteq Q$ stands for the initial state, a state trace of complete signalling program is then $\{I, T[I], T^2[I], ... \}$.

To complete data semantics definition we shall need to define a procedure map an atomic code block expressed in SSI GDL into a relation over $Q$.

(details to be included)

## Signalling data state space

An SSI program defines thousands of individual variables (a larger interlocking would have around 8 thousand variables) the majority of which are simple boolean flag. For instance, for each signalling plan route there would be a dedicated flag in interlocking computer memory stating whether route is set, available to be set, being requested and so on. 

Fortunately SSI notation is so limited that any given variable can only ever appear as an argument to a small number of functions. For instance, route set flag can only be used in conjunction with route set checking predicate and route setting command and nowhere else. Such rigid specialisation of program variables allows us to come with a compact model of signalling data state space. 

In this model, all boolean flag concerning same function of interlocking (e.g., route setting) are combined into a single variable of the form $v: D \rightarrow \mathbb{B}$. For instance, for route setting function we define $\mathit{route\_s}: \mathsf{Route} \rightarrow \mathbb{B}$ where $\mathsf{Route}$ is the set of all routes (or route names). 

To model predicate route set checking predicate `R123 s` we use application $\mathit{route\_s}(\mathtt{R123})$; for route set command `R123 s` we use function override to define next-state of $\mathit{route\_s}$:  $\mathit{route\_s}' = \mathit{route\_s} \dagger \{(R123, \mathtt{true}) \}$.

In absence of any specific signalling plan, domain of such functions are interpreted as abstract sets. Such schematic definition of state space is used to formulate signalling principles.

## Signalling plan semantics

At a first approximation a railway schema is a graph with a number (significant in practice) of annotation. We found it convenient to express a schema as a number of constant sets. Most of such sets encode relations or functions; for instance, essential track topology of is encoded as a next-state relation over sub routes. 

 Naturally definition of every possible schema adheres to same template so where necessary we can reason about schemas as a theory comprising term definitions and some lemmata without referencing any specific instance of a schema.

(details to be included)

## Signalling principles semantics


We interpret signalling principles $P$ as a rule computing a next-state relation over signalling program state and taking signalling plan as an argument:

$$
P \in D \rightarrow \mathbb{P}(Q \times Q)
$$

(more details on definition of $P$)

We say that such $P$ defines all possible safe signalling data for a given signalling plan. That is, for some signalling program iteration step $T$ to be safe w.r.t. signalling plan $d$ it would be necessary that $T \subseteq P(d)$. 

It is convenient to partition principles $P$ into a collection $P_i$ such that $P = \bigcap_i P_i$. Then we can proceed by showing that some component of $T$, say $SL_j$ satisfies some principle $P_k$ w.r.t. $d$ by demonstrating that $SL_j \subseteq P_k(d)$. An overall test would be met by showing that every part of $T$ satisfies every part of $P$. 


## Safety invariant

(how to derive safety invariant proof obligations from the above)
