import Mathlib.Geometry.Convex.Cone.TensorProduct

open TensorProduct

namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H K G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- Right scalar unit for ordered composites. -/
theorem minTensorProduct_rid (C : PointedCone R G) :
    (minTensorProduct C (positive R R)).map (TensorProduct.rid R G) = C :=
by
  apply le_antisymm
  · rw [minTensorProduct, PointedCone.map]
    exact (Submodule.map_span_le _ _ _).mpr fun _ ⟨x, hx, r, hr, h⟩ ↦
      h ▸ TensorProduct.rid_tmul x r ▸ C.smul_mem hr hx
  · intro x hx
    rw [PointedCone.mem_map]
    refine ⟨x ⊗ₜ[R] 1, tmul_mem_minTensorProduct hx (by simp), ?_⟩
    simp

end PointedCone
