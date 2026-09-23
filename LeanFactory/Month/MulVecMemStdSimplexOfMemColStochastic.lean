import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Analysis.Convex.StdSimplex

open Matrix

namespace LeanFactory

variable {R n : Type*} [Fintype n] [DecidableEq n] [Semiring R] [PartialOrder R]
  [IsOrderedRing R]

/-- A column-stochastic matrix maps the classical-state simplex to itself:
entrywise nonnegativity and unit total mass are preserved together. -/
lemma mulVec_mem_stdSimplex_of_mem_colStochastic {M : Matrix n n R} {x : n → R}
    (hM : M ∈ colStochastic R n) (hx : x ∈ stdSimplex R n) :
    M *ᵥ x ∈ stdSimplex R n :=
by
  rw [stdSimplex]
  exact ⟨nonneg_mulVec_of_mem_colStochastic hM hx.1,
    (sum_mulVec_of_mem_colStochastic hM).trans hx.2⟩


end LeanFactory
