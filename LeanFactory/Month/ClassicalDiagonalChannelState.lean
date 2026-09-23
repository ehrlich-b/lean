import LeanFactory.Month.MulVecMemStdSimplexOfMemColStochastic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace

open Matrix

namespace LeanFactory

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A column-stochastic update of a classical state becomes a positive semidefinite diagonal matrix of trace one. -/
theorem diagonal_mulVec_posSemidef_and_trace_eq_one
    {M : Matrix n n ℝ} {x : n → ℝ}
    (hM : M ∈ colStochastic ℝ n) (hx : x ∈ stdSimplex ℝ n) :
    (diagonal (M *ᵥ x)).PosSemidef ∧ trace (diagonal (M *ᵥ x)) = 1 :=
by
  have hstd : M *ᵥ x ∈ stdSimplex ℝ n :=
    mulVec_mem_stdSimplex_of_mem_colStochastic hM hx
  rw [stdSimplex] at hstd
  constructor
  · rw [PosSemidef]
    constructor
    · exact isHermitian_diagonal (M *ᵥ x)
    · intro y
      refine Finsupp.sum_nonneg' (fun i => ?_)
      refine Finsupp.sum_nonneg' (fun j => ?_)
      by_cases hij : i = j
      · subst hij
        simpa [star_trivial, diagonal_apply_eq, pow_two, mul_assoc, mul_comm,
          mul_left_comm] using mul_nonneg (hstd.1 i) (sq_nonneg (y i))
      · rw [diagonal_apply_ne _ hij]
        simpa
  · simpa [trace_diagonal] using hstd.2


end LeanFactory
