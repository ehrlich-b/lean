# Initial thirty-day roadmap

Planning horizon: September 7–October 6, 2026. These are review checkpoints,
not promises of theorem completion.

The [AI-assisted formalization program](AUTOMATED-PROGRAM.md) lists the first 31
source investigations and the admission, verification, and asynchronous review
process used to turn a research result into a publication candidate.

| Stage | Target | Evidence of usefulness |
|---|---|---|
| Week 1 | Classical ordered composites | Compiling finite orthant and positive-matrix examples that consume the cone API |
| Week 2 | PSD cones and real trace pairing | Reuse existing duality results and supply missing interfaces; rank-one tests and an adjoint application |
| Week 3 | Positive-map adjoints | Trace-preserving/unital duality with classical and matrix examples |
| Week 4 | Consolidation | Reproducible build, consumer examples, fewer duplicate interfaces, and one coherent application |

As of September 22, the integrated library has classical stochastic/simplex
and diagonal-state results, a PSD real trace-pairing characterization, and an
explicit unitary trace-adjoint channel. Current development focuses on
composition and complete-positivity interoperability, and on reducing the
remaining dependency and review backlog. These are checkpoints for library
quality, not a theorem-count target.

Before admitting new statements, search current Mathlib and related libraries.
Existing coverage closes a task successfully. Specify real versus complex
scalars, normalization conventions, and closure hypotheses explicitly.
Do not silently identify an algebraic cone hull with its closure or infer
complete positivity from positivity.

Prioritize by dependency distance from these applications. Stop generating
nearby helper lemmas when no concrete consumer requires them. Three failed
mathematical attempts call for decomposition or retirement. Review may lag
proof generation; preserve source pins and link repairs to earlier attempts.

The first external contribution should be small, directly useful, and matched
to the destination's contribution rules. Tau Ceti's existing-code improvements
are a possible starting point; new mathematics needs a specific approved roadmap
target. Disclose AI use, request feedback, and address review findings.

Jordan algebra bridges and tensor-duality characterizations are later candidates
only when an application establishes a short missing dependency path. General
reconstruction and classification results are outside the initial commitment.
