import LeanFactory.Month.StarDotMulVecEqTrace
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix

namespace LeanFactory

variable {n R : Type*} [Fintype n] [CommRing R] [PartialOrder R] [StarRing R]

/-- A Hermitian matrix is positive semidefinite iff its trace pairing with every
rank-one matrix `vecMulVec x (star x)` is nonnegative. -/
theorem posSemidef_iff_trace_mul_vecMulVec_nonneg (M : Matrix n n R) :
    M.PosSemidef ↔ M.IsHermitian ∧ ∀ x : n → R,
      0 ≤ trace (M * vecMulVec x (star x)) :=
by
  rw [posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro h
    exact ⟨h.1, fun x => by
      rw [← star_dotProduct_mulVec_eq_trace_mul_vecMulVec M x]
      exact h.2 x⟩
  · intro h
    exact ⟨h.1, fun x => by
      rw [star_dotProduct_mulVec_eq_trace_mul_vecMulVec M x]
      exact h.2 x⟩


end LeanFactory
