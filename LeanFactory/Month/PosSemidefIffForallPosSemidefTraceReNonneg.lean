import LeanFactory.Month.PosSemidefIffTraceRankOneNonneg
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Trace

open Matrix
open scoped ComplexOrder

namespace LeanFactory

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- The Hermitian PSD cone is self-dual under the real trace pairing: a Hermitian
matrix is positive semidefinite iff its real trace pairing with every positive
semidefinite matrix has nonnegative real part. -/
theorem posSemidef_iff_forall_posSemidef_trace_re_nonneg {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    A.PosSemidef ↔ ∀ B : Matrix n n 𝕜, B.PosSemidef → 0 ≤ RCLike.re (trace (A * B)) :=
by
  classical
  constructor
  · intro hApsd B hB
    letI : PartialOrder (Matrix n n 𝕜) := Matrix.instPartialOrder
    haveI : StarOrderedRing (Matrix n n 𝕜) := Matrix.instStarOrderedRing
    haveI : NonnegSpectrumClass ℝ (Matrix n n 𝕜) := Matrix.instNonnegSpectrumClass
    obtain ⟨C, hB_eq⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hB.nonneg : 0 ≤ B)
    have htr : trace (A * B) = trace (C * A * Cᴴ) := by
      rw [hB_eq, trace_mul_cycle', ← mul_assoc, star_eq_conjTranspose]
    have hnonneg : 0 ≤ RCLike.re (trace (C * A * Cᴴ)) :=
      RCLike.nonneg_iff.mp (hApsd.mul_mul_conjTranspose_same C).trace_nonneg |>.1
    rw [htr]
    exact hnonneg
  · intro h
    refine PosSemidef.of_dotProduct_mulVec_nonneg hA ?_
    intro x
    have htrace : 0 ≤ RCLike.re (trace (A * vecMulVec x (star x))) :=
      h (vecMulVec x (star x)) (posSemidef_vecMulVec_self_star x)
    have hxre : 0 ≤ RCLike.re (star x ⬝ᵥ (A *ᵥ x)) := by
      rwa [← star_dotProduct_mulVec_eq_trace_mul_vecMulVec A x] at htrace
    exact RCLike.nonneg_iff.mpr ⟨hxre, hA.im_star_dotProduct_mulVec_self x⟩


end LeanFactory
