import Mathlib.Geometry.Convex.Cone.TensorProduct

open TensorProduct

namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- The top cone is also a right absorbing object for the maximal tensor product. -/
theorem maxTensorProduct_top_right (C : PointedCone R G) :
    maxTensorProduct C (⊤ : PointedCone R H) = ⊤ :=
by
  apply le_antisymm le_top
  intro z hz
  rw [mem_maxTensorProduct] at ⊢
  intro φ hφ ψ hψ
  have hψ_zero : ψ = 0 := by
    ext x
    have hx : 0 ≤ ψ x := by
      simpa using hψ (by simp : x ∈ (⊤ : PointedCone R H))
    have hneg : 0 ≤ -ψ x := by
      simpa using hψ (by simp : -x ∈ (⊤ : PointedCone R H))
    exact le_antisymm (neg_nonneg.mp hneg) hx
  rw [hψ_zero]
  simp

end PointedCone
