import LeanFactory.Month.KrausTraceNormalization
import LeanFactory.Month.TracePairingPreservingUnital

open scoped Matrix

namespace LeanFactory

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [CommRing 𝕜] [StarRing 𝕜]

/-- The finite Kraus action as a linear map, with the same left-action orientation as Matrix.trace_krausMap. -/
def krausMap {κ : Type*} [Fintype κ] (A : κ → Matrix n n 𝕜) :
    Matrix n n 𝕜 →ₗ[𝕜] Matrix n n 𝕜 :=
  { toFun := fun X => ∑ k, A k * X * (A k)ᴴ
    map_add' := by intro X Y; simp [mul_add, add_mul, Finset.sum_add_distrib, mul_assoc]
    map_smul' := by intro c X; simp [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum] }

/-- A finite Kraus action preserves trace exactly when its normalization operator is the identity. -/
theorem krausMap_tracePreserving_iff_sum_star_mul_eq_one
    {κ : Type*} [Fintype κ] (A : κ → Matrix n n 𝕜) :
    TracePreserving (krausMap A) ↔ (∑ k, (A k)ᴴ * A k) = 1 :=
by
  constructor
  · intro hT
    apply Matrix.ext_iff_trace_mul_left.mpr
    intro X
    calc
      (X * (∑ k, (A k)ᴴ * A k)).trace = Matrix.trace (krausMap A X) := (Matrix.trace_krausMap A X).symm
      _ = X.trace := hT X
      _ = (X * (1 : Matrix n n 𝕜)).trace := by simp
  · intro hId
    intro X
    calc
      Matrix.trace (krausMap A X) = (X * (∑ k, (A k)ᴴ * A k)).trace := Matrix.trace_krausMap A X
      _ = (X * (1 : Matrix n n 𝕜)).trace := by rw [hId]
      _ = X.trace := by simp


end LeanFactory
