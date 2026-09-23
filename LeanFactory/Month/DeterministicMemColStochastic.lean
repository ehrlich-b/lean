import Mathlib.LinearAlgebra.Matrix.Stochastic

namespace Matrix

/-- The deterministic (0,1)-matrix of a classical channel `f : n → n`: the entry
`(i, j)` is `1` when the channel sends `j` to `i` and `0` otherwise, so each
column contains exactly one `1`. Pinned Mathlib has `PEquiv.toMatrix` (injective
maps) and `Equiv.Perm.permMatrix` (bijections) but no such object for a general,
possibly non-injective `f : n → n`; this definition supplies the missing
function-induced deterministic-channel object. -/
noncomputable def deterministic (R : Type*) [Zero R] [One R] [DecidableEq n]
    (f : n → n) : Matrix n n R :=
  of fun i j => if f j = i then (1 : R) else 0

/-- The matrix of a deterministic classical channel is column-stochastic: all
entries are nonnegative and every column sums to one (exactly one `1` per column).
Composed with `sum_mulVec_of_mem_colStochastic`, membership yields the complete
positivity-and-normalization application
`∑ i, (deterministic R f *ᵥ x) i = ∑ i, x i` for every vector `x`, which is the
Week-1 classical diagonal-channel packet demand (`docs/four-week-consumer-program-2026-09-12.md`):
an application over Mathlib's existing stochastic carrier, not a raw-premise wrapper. -/
lemma deterministic_mem_colStochastic [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [Fintype n] [DecidableEq n] (f : n → n) :
    deterministic R f ∈ colStochastic R n :=
by
  rw [mem_colStochastic_iff_sum]
  constructor
  · intro i j
    by_cases h : f j = i
    · simp [deterministic, h]
    · simp [deterministic, h]
  · intro j
    simp [deterministic]


end Matrix
