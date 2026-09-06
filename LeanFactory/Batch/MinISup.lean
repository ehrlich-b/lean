import Mathlib.Geometry.Convex.Cone.TensorProduct

open TensorProduct

namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H K G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- Directed and arbitrary generation, including an empty indexing sort. -/
theorem minTensorProduct_iSup_left {ι : Sort*} (C : ι → PointedCone R G) (D : PointedCone R H) :
    minTensorProduct (⨆ i, C i) D = ⨆ i, minTensorProduct (C i) D :=
by
  let f : G →ₗ[{c : R // 0 ≤ c}] H →ₗ[{c : R // 0 ≤ c}] (G ⊗[R] H) :=
    (TensorProduct.mk R G H).restrictScalars₁₂ {c : R // 0 ≤ c} {c : R // 0 ≤ c}
  simpa only [minTensorProduct, f, Submodule.map₂_eq_span_image2,
    LinearMap.restrictScalars₁₂_apply_apply, TensorProduct.mk_apply] using
    (Submodule.map₂_iSup_left f C D)

end PointedCone
