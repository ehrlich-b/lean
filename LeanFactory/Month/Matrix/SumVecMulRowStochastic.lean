import Mathlib.LinearAlgebra.Matrix.Stochastic

namespace Matrix

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Applying a row-stochastic matrix on the left (via vecMul) preserves the sum of a vector. -/
lemma sum_vecMul_of_mem_rowStochastic {M : Matrix n n R} {x : n → R}
    (hA : M ∈ rowStochastic R n) : ∑ i, (x ᵥ* M) i = ∑ i, x i :=
by
  simp only [Matrix.vecMul, dotProduct]
  rw [Finset.sum_comm]
  simp [sum_row_of_mem_rowStochastic hA, ← Finset.mul_sum]


end Matrix

