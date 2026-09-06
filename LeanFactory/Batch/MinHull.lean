import Mathlib.Geometry.Convex.Cone.TensorProduct

open TensorProduct

namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H K G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- Finite generators and explicit examples, without assuming hulls are closed. -/
theorem minTensorProduct_hull (s : Set G) (t : Set H) :
    minTensorProduct (hull R s) (hull R t) =
      hull R (Set.image2 (fun x y => x ⊗ₜ[R] y) s t) :=
by
  change Submodule.span {c : R // 0 ≤ c} (Set.image2 (fun x y => x ⊗ₜ[R] y)
      (Submodule.span {c : R // 0 ≤ c} s) (Submodule.span {c : R // 0 ≤ c} t)) =
    Submodule.span {c : R // 0 ≤ c} (Set.image2 (fun x y => x ⊗ₜ[R] y) s t)
  let f := (TensorProduct.mk R G H).restrictScalars₁₂
    {c : R // 0 ≤ c} {c : R // 0 ≤ c}
  exact (Submodule.map₂_eq_span_image2 (R := {c : R // 0 ≤ c}) f _ _).symm.trans
    (Submodule.map₂_span_span {c : R // 0 ≤ c} f s t)

end PointedCone
