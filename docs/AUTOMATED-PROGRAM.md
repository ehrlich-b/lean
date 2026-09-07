# AI-assisted formalization program

This document describes the initial month of AI-assisted research behind this
repository. It is a queue of questions to investigate, not a promise to add 31
theorems. A packet can close because Mathlib already contains the needed result,
because the proposed interface is not useful, or because the mathematics needs
expert direction. Those are useful outcomes.

The organizing rule is **dependency distance from mathematics we care about**.
A helper belongs in the project when a named application needs it and current
libraries do not already supply it. Proof generation follows source search and
statement review rather than creating a growing collection of nearby lemmas.

## Initial research horizon

The first horizon contains 31 bounded source investigations. Each investigation
must identify exact declarations in the pinned Mathlib revision, distinguish a
missing interface from a search miss, propose at most a few statements, and name
concrete consumers before implementation begins.

### Classical coordinates (7)

1. Coordinate descriptions of nonnegative orthants.
2. Dual bases and coordinate functionals for simplicial cones.
3. The finite probability simplex as nonnegative coordinates summing to one.
4. Positive linear maps represented by entrywise nonnegative matrices.
5. Stochastic matrices as simplex-preserving positive maps.
6. Bistochastic maps and the adjoint/transpose operation.
7. Tensor-product coordinates for classical composite systems.

These packets should produce small examples that exercise the existing cone and
tensor APIs. They are the nearest consumers of the library already published
here.

### Positive semidefinite matrices and trace pairing (8)

1. A usable real vector-space carrier for finite Hermitian matrices.
2. The real-valued trace pairing on that carrier.
3. Nondegeneracy of the trace pairing.
4. Rank-one tests for positive semidefiniteness.
5. Preservation of positive semidefiniteness under congruence.
6. Relations among support, kernel, and range for positive semidefinite matrices.
7. Positive semidefinite square roots and Gram factorizations.
8. Closedness and proper-cone structure of the positive semidefinite cone.

This layer must reuse Mathlib's matrix, star-algebra, and positivity interfaces.
It should not introduce a parallel Hermitian-matrix theory merely to make later
proofs syntactically convenient.

### Adjoints and finite-dimensional channels (8)

1. Finite-dimensional adjoints expressed through the chosen pairings.
2. The equivalence between trace preservation and a unital adjoint.
3. Conditions under which the adjoint of a positive map is positive.
4. The seam between Kraus representations and Mathlib's completely positive maps.
5. The seam between Choi matrices and completely positive maps.
6. Composition and tensor products of completely positive maps.
7. Unitary conjugation as a channel.
8. Diagonal quantum channels recovering classical stochastic maps.

This is the first intended application layer. Definitions and normalizations
must be fixed by compiling classical and matrix examples before general APIs are
admitted.

### Ordered composites (4)

1. Exact hypotheses for duality between minimal and maximal tensor cones.
2. The boundary between algebraic cone generation and topological closure.
3. The separable positive semidefinite cone under matrix/tensor equivalences.
4. Testing positivity into a maximal cone through positive bilinear forms.

These packets are especially sensitive to finite-dimensional, closure, and
scalar-field assumptions. A statement that silently crosses the
algebraic/topological boundary is rejected.

### Later bridges (4)

1. Self-adjoint matrices as a concrete Jordan algebra.
2. Quadratic operators in the available Jordan interface.
3. Entropy on a finite probability simplex.
4. Nonnegativity of finite relative entropy.

Jordan and information-theoretic work remains behind the earlier application
layers. It advances only when it has a short, explicit dependency path to a
consumer.

## Admission and verification

AI is used for source reconnaissance, candidate design, implementation, and
review. These roles are separated so that one model's confident prose is not
treated as evidence for its own result.

1. **Source intake.** Record exact source paths and declarations from the pinned
   dependency revision, the result of a duplicate search, bounded candidate
   statements, and at least two plausible consumers.
2. **Independent intake review.** Check citations, restate the mathematical gap,
   and reject candidates already covered by the dependency or too far from an
   application.
3. **Statement admission.** Freeze the imports, namespace, assumptions, result,
   allowed file scope, and validation command. No proof work starts from an
   unreviewed prose description.
4. **Implementation.** Work against the frozen dependency pins. Preserve failed
   attempts and create a linked repair when a statement or proof needs revision.
5. **Mechanical validation.** Compile the complete exported import graph, reject
   placeholders and extra axioms, and replay the environment in a fresh Lean
   kernel.
6. **Editorial review.** Recheck the exact candidate bytes, current source,
   naming, assumptions, duplication, proof shape, and downstream consumers.
7. **Publication.** Export through the curated boundary and require the public
   CI checks described in [CI.md](CI.md).

The intake format has six required sections: source map, existing coverage,
gaps, candidate statements, consumers, and research verdict. It must also contain
an exact Mathlib source path and an illustrative Lean signature. This structural
gate only prevents incomplete reports from consuming more review work; it does
not establish that a citation or statement is correct.

Passing Lean is necessary but does not prove novelty, faithful modeling, API
quality, or relevance. A result becomes a publication candidate only after both
mechanical and editorial review. A layer becomes suitable to show another
project when it has coherent imports, compiling consumer examples, documented
conventions, a current duplicate search, and a reproducible verification record.

## Queue and review cadence

Generation uses a shared, provider-neutral work queue. Lean is intended to be
an ambient mathematical backlog; unrelated repositories can use the same worker
pool when their jobs carry their own source pin, file scope, validation commands,
and review destination. Results never cross repositories merely because they
used the same queue.

The initial 31-packet horizon was sized as roughly one to two days of continuous
two-lane research and review, based on early calls taking about 10–55 minutes.
This is a capacity estimate rather than a productivity claim. Review debt is
measured separately from generated output, and admission slows when independent
review cannot keep pace. Failed, duplicate, and retired packets remain visible
so later coordinators do not unknowingly repeat them.

Coordination is deliberately asynchronous. A result may wait days before review,
and later evidence may require a linked repair. Immutable inputs, dependency
pins, content hashes, and explicit parent/child lineage make that delay
recoverable without accepting a worker's summary on trust.

## Relationship to other projects

This repository is an independent staging ground. Mathlib, Tau Ceti, Palomar,
and domain libraries are sources of existing work and possible consumers, not
automatic destinations. Public CI here does not make a result ready for any of
them.

Any upstream proposal should be small, conventionally factored for its
destination, supported by a real consumer, and reviewed against that project's
current contribution guidance. AI use must be disclosed. No upstream pull
request should be opened simply to keep the queue busy; a proposed contribution
gets a separate, detailed discussion first.
