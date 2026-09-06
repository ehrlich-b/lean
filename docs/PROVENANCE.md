# Provenance

Maintainer: Bryan Ehrlich (`ehrlich-b`).

This snapshot contains AI-generated supporting proofs of standard mathematics.
It builds on the Mathlib contributors' cone, tensor-product, basis, and duality
APIs. No claim of mathematical novelty is made.

The source files were selected unchanged from the exported import closure of a
private development repository. `source-manifest.json` records their SHA-256
hashes. The root import and pinned Lake configuration are included. Unfinished
contracts, operational scripts, raw agent conversations, and account records
are not part of this publication. The original development history is retained
privately rather than rewritten or published.

The development used Codex (including Luna and Sol), Claude Sonnet, and DeepSeek
V4 Flash via OpenCode/Arli. Model roles changed across experiments; this is a
project-level disclosure, not a claim of exact per-line attribution. Reviews
were AI reviews, not independent expert human refereeing.

Mathlib references at the pinned revision:

- `Mathlib/Geometry/Convex/Cone/TensorProduct.lean`
- `Mathlib/Geometry/Convex/Cone/Simplicial.lean`
- `Mathlib/Geometry/Convex/Cone/Dual.lean`
- `Mathlib/Analysis/Convex/Cone/TensorProduct.lean`
- `Mathlib/LinearAlgebra/Basis/Basic.lean`

`IsSimplicial.exists_basis` extracts a basis-construction pattern used in
Mathlib's simplicial tensor-product development. Many other proofs specialize
Mathlib's `Submodule.map₂`, span, and map APIs. Dependencies retain their own
licenses and authorship. No Tau Ceti or Physlib implementation is bundled.
