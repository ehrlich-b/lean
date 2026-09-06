import Mathlib.Geometry.Convex.Cone.TensorProduct

open TensorProduct

namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H K G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- The maximal scalar-unit image is the algebraic bidual cone; do not silently replace it by C without extra hypotheses. -/
theorem maxTensorProduct_lid_bidual (C : PointedCone R G) :
    (maxTensorProduct (positive R R) C).map (TensorProduct.lid R G) =
      dual (Module.Dual.eval R G).flip (dual (Module.Dual.eval R G) C) :=
by
  let e : Module.Dual R R := LinearMap.id
  have he : e ∈ dual (Module.Dual.eval R R) (positive R R) := by
    intro r hr
    simpa [e] using hr
  have hpair (ψ : Module.Dual R G) :
      dualDistrib R R G (e ⊗ₜ[R] ψ) = ψ.comp (TensorProduct.lid R G).toLinearMap := by
    apply TensorProduct.ext'
    intro r x
    simp [e]
  ext x
  simp only [mem_map, mem_dual]
  constructor
  · rintro ⟨z, hz, rfl⟩ ψ hψ
    have hz' := mem_maxTensorProduct.mp hz e he ψ hψ
    rw [hpair ψ] at hz'
    exact hz'
  · intro hx
    refine ⟨(TensorProduct.lid R G).symm x, ?_,
      (TensorProduct.lid R G).apply_symm_apply x⟩
    apply mem_maxTensorProduct.mpr
    intro φ hφ ψ hψ
    have hφ1 : 0 ≤ φ 1 := hφ (by simp)
    have hψx : 0 ≤ ψ x := hx hψ
    rw [TensorProduct.lid_symm_apply, dualDistrib_apply]
    exact mul_nonneg hφ1 hψx

end PointedCone
