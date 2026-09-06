import Mathlib.Geometry.Convex.Cone.TensorProduct

open TensorProduct

namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- The right maximal scalar unit exposes the algebraic bidual cone. -/
theorem maxTensorProduct_rid_bidual (C : PointedCone R G) :
    (maxTensorProduct C (positive R R)).map (TensorProduct.rid R G) =
      dual (Module.Dual.eval R G).flip (dual (Module.Dual.eval R G) C) :=
by
  let e : Module.Dual R R := LinearMap.id
  have he : e ∈ dual (Module.Dual.eval R R) (positive R R) := by
    intro r hr
    simpa [e] using hr
  have hpair (φ : Module.Dual R G) :
      dualDistrib R G R (φ ⊗ₜ[R] e) = φ.comp (TensorProduct.rid R G).toLinearMap := by
    apply TensorProduct.ext'
    intro x r
    simp [e, mul_comm]
  ext x
  simp only [mem_map, mem_dual]
  constructor
  · rintro ⟨z, hz, rfl⟩ φ hφ
    have hz' := mem_maxTensorProduct.mp hz φ hφ e he
    rw [hpair φ] at hz'
    exact hz'
  · intro hx
    refine ⟨(TensorProduct.rid R G).symm x, ?_, (TensorProduct.rid R G).apply_symm_apply x⟩
    apply mem_maxTensorProduct.mpr
    intro φ hφ ψ hψ
    have hψ1 : 0 ≤ ψ 1 := hψ (by simp)
    have hφx : 0 ≤ φ x := hx hφ
    rw [TensorProduct.rid_symm_apply, dualDistrib_apply]
    exact mul_nonneg hφx hψ1

end PointedCone
