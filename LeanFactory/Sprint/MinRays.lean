import Mathlib.Geometry.Convex.Cone.TensorProduct

open TensorProduct

namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H K G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- Tensor products of rays, including zero generators; a concrete cone example. -/
theorem minTensorProduct_hull_singleton (x : G) (y : H) :
    minTensorProduct (hull R {x}) (hull R {y}) = hull R {x ⊗ₜ[R] y} :=
by
  rw [minTensorProduct]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, b, hb, rfl⟩
    rcases Submodule.mem_span_singleton.mp ha with ⟨a, rfl⟩
    rcases Submodule.mem_span_singleton.mp hb with ⟨b, rfl⟩
    change ((a : R) • x) ⊗ₜ[R] ((b : R) • y) ∈ hull R {x ⊗ₜ[R] y}
    rw [TensorProduct.smul_tmul_smul]
    exact (hull R {x ⊗ₜ[R] y}).smul_mem (mul_nonneg a.2 b.2) (subset_hull (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    rintro _ ⟨rfl⟩
    exact tmul_mem_minTensorProduct (subset_hull (Set.mem_singleton _))
      (subset_hull (Set.mem_singleton _))

end PointedCone
