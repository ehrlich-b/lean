import Mathlib.Geometry.Convex.Cone.TensorProduct

open TensorProduct

namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H K G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- Indexed positive-generation API in the second factor, including empty index types. -/
theorem minTensorProduct_iSup_right {ι : Sort*} (C : PointedCone R G) (D : ι → PointedCone R H) :
    minTensorProduct C (⨆ i, D i) = ⨆ i, minTensorProduct C (D i) :=
by
  let f := (TensorProduct.mk R G H).restrictScalars₁₂
    {r : R // 0 ≤ r} {r : R // 0 ≤ r}
  have h (E : PointedCone R H) :
      minTensorProduct C E = Submodule.map₂ f C E := by
    simp [f, minTensorProduct, hull, Submodule.map₂_eq_span_image2]
  calc
    minTensorProduct C (⨆ i, D i) = Submodule.map₂ f C (⨆ i, D i) := h _
    _ = ⨆ i, Submodule.map₂ f C (D i) := Submodule.map₂_iSup_right f C D
    _ = ⨆ i, minTensorProduct C (D i) := by
      congr 1
      funext i
      exact (h (D i)).symm

end PointedCone
