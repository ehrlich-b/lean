import Mathlib.Geometry.Convex.Cone.TensorProduct

open TensorProduct

namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H K G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- Positive decompositions and finite joins. -/
theorem minTensorProduct_sup_left (C C' : PointedCone R G) (D : PointedCone R H) :
    minTensorProduct (C ⊔ C') D = minTensorProduct C D ⊔ minTensorProduct C' D :=
by
  let f : G →ₗ[{c : R // 0 ≤ c}] H →ₗ[{c : R // 0 ≤ c}] (G ⊗[R] H) :=
    (TensorProduct.mk R G H).restrictScalars₁₂ _ _
  simpa [f, minTensorProduct, Submodule.map₂_eq_span_image2] using
    (Submodule.map₂_sup_left f C C' D)

end PointedCone
