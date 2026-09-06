import Mathlib.Geometry.Convex.Cone.TensorProduct

open TensorProduct

namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H K G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- Degenerate maximal cone behavior when one factor has zero dual; clarifies the distinction from minimal tensors. -/
theorem maxTensorProduct_top_left (D : PointedCone R H) :
    maxTensorProduct (⊤ : PointedCone R G) D = ⊤ :=
by
  ext z
  constructor
  · intro _
    simp
  · intro _
    rw [mem_maxTensorProduct]
    intro φ hφ ψ hψ
    have hφ_zero : φ = 0 := by
      ext x
      have hx : 0 ≤ φ x := hφ (by simp)
      have hnx : 0 ≤ φ (-x) := hφ (by simp)
      exact le_antisymm (neg_nonneg.mp (by simpa only [map_neg] using hnx)) hx
    rw [hφ_zero]
    simp

end PointedCone
