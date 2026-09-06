import Mathlib.Geometry.Convex.Cone.TensorProduct

open TensorProduct

namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H K G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- The scalar nonnegative cone is the minimal tensor unit. -/
theorem minTensorProduct_lid (C : PointedCone R G) :
    (minTensorProduct (positive R R) C).map (TensorProduct.lid R G) = C :=
by
  apply le_antisymm
  · rw [minTensorProduct, PointedCone.map]
    exact (Submodule.map_span_le _ _ _).mpr fun _ ⟨r, hr, x, hx, h⟩ ↦
      h ▸ TensorProduct.lid_tmul x r ▸ C.smul_mem hr hx
  · intro x hx
    rw [PointedCone.mem_map]
    refine ⟨1 ⊗ₜ[R] x, tmul_mem_minTensorProduct (by simp) hx, ?_⟩
    simp

end PointedCone
