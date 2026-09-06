import Mathlib.Geometry.Convex.Cone.TensorProduct

open TensorProduct

namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- Membership along the right maximal tensor unit is membership in the algebraic bidual. -/
theorem tmul_one_mem_maxTensorProduct_iff (C : PointedCone R G) (x : G) :
    x ⊗ₜ[R] (1 : R) ∈ maxTensorProduct C (positive R R) ↔
      x ∈ dual (Module.Dual.eval R G).flip (dual (Module.Dual.eval R G) C) :=
by
  simp only [mem_maxTensorProduct, mem_dual, dualDistrib_apply, LinearMap.flip_apply,
    Module.Dual.eval_apply]
  let e : Module.Dual R R := LinearMap.id
  have he : e ∈ dual (Module.Dual.eval R R) (positive R R) := by
    intro r hr
    simpa [e] using hr
  constructor
  · intro h φ hφ
    simpa [e] using h φ hφ e he
  · intro h φ hφ ψ hψ
    exact mul_nonneg (h hφ) (hψ (by simp))

end PointedCone
