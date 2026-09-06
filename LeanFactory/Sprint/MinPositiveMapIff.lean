import Mathlib.Geometry.Convex.Cone.TensorProduct

open TensorProduct

namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H K G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- Characterize positive maps out of the minimal tensor cone on elementary generators. -/
theorem minTensorProduct_map_le_iff (C : PointedCone R G) (D : PointedCone R H)
    (E : PointedCone R K) (f : G ⊗[R] H →ₗ[R] K) :
    (minTensorProduct C D).map f ≤ E ↔
      ∀ x ∈ C, ∀ y ∈ D, f (x ⊗ₜ[R] y) ∈ E :=
by
  constructor
  · intro h x hx y hy
    apply h
    exact ⟨x ⊗ₜ[R] y, tmul_mem_minTensorProduct hx hy, rfl⟩
  · intro h
    exact (Submodule.map_span_le _ _ _).mpr fun _ ⟨x, hx, y, hy, hxy⟩ ↦
      hxy ▸ h x hx y hy

end PointedCone
