import LeanFactory.Month.DeterministicMemColStochastic
import Mathlib.LinearAlgebra.StdBasis

namespace Matrix

variable {R n : Type*} [Semiring R] [Fintype n] [DecidableEq n]

/-- A deterministic classical channel sends the basis state at `j` to the basis state at `f j`, including for non-injective `f`. -/
lemma deterministic_mulVec_basisFun (f : n → n) (j : n) :
    deterministic R f *ᵥ Pi.basisFun R n j = Pi.basisFun R n (f j) :=
by
  rw [Pi.basisFun_apply, Pi.basisFun_apply, mulVec_single_one]
  ext i
  by_cases h : f j = i
  · simp [deterministic, h]
  · simp [deterministic, h]


end Matrix
