import LeanFactory.Month.TracePairingPreservingUnital
import Mathlib.LinearAlgebra.UnitaryGroup

open scoped Matrix

namespace LeanFactory

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [CommRing 𝕜] [StarRing 𝕜]

/-- Conjugation by a unitary matrix as a linear map on square matrices. -/
def unitaryConj (U : Matrix n n 𝕜) (hU : U ∈ Matrix.unitaryGroup n 𝕜) :
    Matrix n n 𝕜 →ₗ[𝕜] Matrix n n 𝕜 :=
  { toFun := fun X => U * X * Uᴴ
    map_add' := by intro X Y; simp [mul_add, add_mul, mul_assoc]
    map_smul' := by intro c X; simp [Matrix.mul_smul, Matrix.smul_mul] }

/-- Unitary conjugation fixes the identity matrix. -/
theorem unitaryConj_unital (U : Matrix n n 𝕜) (hU : U ∈ Matrix.unitaryGroup n 𝕜) :
    unitaryConj U hU 1 = 1 :=
by
  change U * (1 : Matrix n n 𝕜) * Uᴴ = 1
  rw [mul_one, ← Matrix.star_eq_conjTranspose]
  exact Matrix.mem_unitaryGroup_iff.mp hU


end LeanFactory
