# Lean mathematics, with AI

My attempt at contributing to the Lean formalization of mathematics using AI.

I'm starting with mathematics around finite-dimensional quantum theory: ordered
vector spaces, positive cones, tensor products, and positive linear maps. The
hope is to contribute small, reusable pieces that other formalizations can use.
This is an early experiment, and I expect to learn from mistakes and feedback.

## What is here

The initial library contains 32 supporting theorems built on Mathlib's existing
cone definitions. They cover linear-map transport, generators and joins of
minimal tensor cones, scalar units, algebraic duality, and simplicial cones and
basis coordinates. They are supporting API, not claims of new mathematics.

For example, `PointedCone.minTensorProduct_map_le_iff` reduces positivity of a
linear map out of a minimal tensor cone to checking elementary tensors.
`PointedCone.mem_hull_basis_iff` describes a basis-generated cone by nonnegative
coordinates. Import individual modules or the library root:

```lean
import LeanFactory
```

The `Batch`, `Sprint`, and `Overnight` directory names reflect the early
experiments; the module organization and API are not yet stable.

## Initial targets

1. **Classical ordered composites:** concrete nonnegative orthants, tensor
   coordinates, and positive maps represented by nonnegative matrices.
2. **PSD matrices and trace duality:** connect Hermitian positive-semidefinite
   matrices to existing cone and real trace-pairing interfaces.
3. **Positive maps and channel adjoints:** positivity transport and the relation
   between trace preservation and a unital adjoint, with classical and quantum
   examples.

These are targets, not completed features. Existing formalizations should be
reused wherever possible. A useful outcome would be a few coherent interfaces
with compiling applications, rather than a large collection of isolated lemmas.
See the [roadmap](docs/ROADMAP.md).

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake build LeanFactory
```

The toolchain and every dependency revision are pinned. This initial snapshot
uses Lean 4.33.1 and Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`. A compatible dependency cache may not
be available for this toolchain combination, so the first build can be costly.
See [verification](docs/VERIFICATION.md) for what was actually checked.

## AI use and feedback

The Lean proofs were generated with AI. The development experiments used OpenAI
Codex models, Anthropic Claude, and DeepSeek through Arli/OpenCode; AI was also
used for statement design, reviews, orchestration, and this documentation.
Bryan Ehrlich directs the project. This does not imply an expert human has
reviewed every proof or design decision.

Candidates go through isolated checks and AI review before integration. Kernel
acceptance does not establish that a statement is the right one, that the API
is useful, or that a proof is well factored. Those are ongoing review questions.

Feedback is very welcome, especially on duplicate results, assumptions, naming,
placement, proof simplification, and whether these interfaces would be useful in
another project. Please open an issue with a concrete example or source link.

This is an independent project. It is not endorsed by Mathlib, Tau Ceti, or
Palomar, and no result here is currently Palomar-registered. I hope to learn to
make useful contributions to the wider ecosystem.

## License and provenance

Apache-2.0. See [LICENSE](LICENSE), [NOTICE](NOTICE), and
[provenance](docs/PROVENANCE.md). The public repository starts from a curated
snapshot; private machine configuration, account records, agent transcripts,
and unfinished task files are excluded.
