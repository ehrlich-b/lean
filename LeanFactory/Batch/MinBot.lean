import Mathlib.Geometry.Convex.Cone.TensorProduct

open TensorProduct

namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H K G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- Zero-object behavior needed by the complete-lattice API. -/
theorem minTensorProduct_bot_left (D : PointedCone R H) :
    minTensorProduct (⊥ : PointedCone R G) D = ⊥ :=
by
  refine le_antisymm ?_ bot_le
  unfold minTensorProduct
  apply Submodule.span_le.mpr
  rintro _ ⟨x, hx, y, hy, rfl⟩
  have hx0 : x = 0 := by simpa using hx
  simp [hx0]

end PointedCone
