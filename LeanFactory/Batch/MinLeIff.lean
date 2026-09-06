import Mathlib.Geometry.Convex.Cone.TensorProduct

open TensorProduct

namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H K G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- Universal property for proving positivity of bilinear maps. -/
theorem minTensorProduct_le_iff (C : PointedCone R G) (D : PointedCone R H)
    (E : PointedCone R (G ⊗[R] H)) :
    minTensorProduct C D ≤ E ↔ ∀ x ∈ C, ∀ y ∈ D, x ⊗ₜ[R] y ∈ E :=
by
  constructor
  · intro h x hx y hy
    exact h (tmul_mem_minTensorProduct hx hy)
  · intro h
    exact Submodule.span_le.mpr <| fun _ ⟨x, hx, y, hy, hxy⟩ => hxy ▸ h x hx y hy

end PointedCone
