import Mathlib.Geometry.Convex.Cone.TensorProduct

open TensorProduct

namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- The zero cone is also a right zero for the minimal tensor product. -/
theorem minTensorProduct_bot_right (C : PointedCone R G) :
    minTensorProduct C (⊥ : PointedCone R H) = ⊥ :=
by
  refine le_antisymm ?_ bot_le
  rw [minTensorProduct]
  apply Submodule.span_le.mpr
  rintro _ ⟨x, hx, y, hy, rfl⟩
  have hy0 : y = 0 := by simpa using hy
  simp [hy0]

end PointedCone
