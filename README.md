# Lean mathematics, with AI

My attempt at contributing to the Lean formalization of mathematics using AI.

I'm starting with mathematics around finite-dimensional quantum theory: ordered
vector spaces, positive cones, tensor products, and positive linear maps. The
hope is to contribute small, reusable pieces that other formalizations can use.
This is an early experiment, and I expect to learn from mistakes and feedback.

## What is here

The library now includes cone and tensor-product interfaces, finite classical
stochastic maps, Hermitian positive-semidefinite matrix results, and explicit
trace-adjoint channels. Theorems are standard mathematics formalized as
reusable APIs, not claims of mathematical novelty.

For example, `PointedCone.minTensorProduct_map_le_iff` reduces positivity of a
linear map out of a minimal tensor cone to checking elementary tensors.
`PointedCone.mem_hull_basis_iff` describes a basis-generated cone by nonnegative
coordinates. Import individual modules or the library root:

```lean
import LeanFactory
```

The `Batch`, `Sprint`, and `Overnight` directory names reflect the early
experiments; the module organization and API are not yet stable.

## Current mathematical threads

1. **Classical ordered systems:** orthant cone examples, stochastic maps on
   Mathlib's standard simplex, and diagonal PSD matrices of trace one.
2. **PSD matrices:** rank-one and real trace-pairing tests for positivity, plus
   transport of positivity through a trace-adjoint pair.
3. **Channels:** an explicit trace-pairing adjoint convention, the equivalence
   between trace preservation and adjoint unitality, and a unitary-conjugation
   instance.

The private development repository also checks concrete application callers;
the public import root exports only integrated theorem modules. These interfaces
remain under review for duplication, naming, and abstraction quality. See the
[roadmap](docs/ROADMAP.md).

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake build LeanFactory
```

The toolchain and every dependency revision are pinned. This source
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

The public [validation workflow](docs/CI.md) builds every exported module,
audits transitive axioms and performs a fresh kernel replay. Passing these
checks does not replace mathematical or API review.
