import LeanFactory.Month.MulVecMemStdSimplexOfMemColStochastic
import Mathlib.LinearAlgebra.Matrix.Notation

open Matrix

namespace LeanFactory

/-- A concrete two-state column-stochastic update preserves the classical-state simplex. -/
theorem twoState_stochastic_keeps_state :
    (!![(1 / 2 : ℝ), 1 / 4; 1 / 2, 3 / 4] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ
        ![(1 / 2 : ℝ), 1 / 2] ∈ stdSimplex ℝ (Fin 2) :=
by
  have hM : (!![(1 / 2 : ℝ), 1 / 4; 1 / 2, 3 / 4] : Matrix (Fin 2) (Fin 2) ℝ) ∈
      colStochastic ℝ (Fin 2) := by
    rw [mem_colStochastic_iff_sum]
    constructor
    · intro i j
      fin_cases i <;> fin_cases j <;> norm_num
    · intro j
      fin_cases j <;> norm_num
  have hx : (![(1 / 2 : ℝ), 1 / 2] : Fin 2 → ℝ) ∈ stdSimplex ℝ (Fin 2) := by
    constructor
    · intro i
      fin_cases i <;> norm_num
    · norm_num
  exact mulVec_mem_stdSimplex_of_mem_colStochastic hM hx


end LeanFactory
