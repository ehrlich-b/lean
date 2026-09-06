import Mathlib.Geometry.Convex.Cone.TensorProduct

open TensorProduct

namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- Expanding generators in the left factor does not change the generated tensor cone. -/
theorem minTensorProduct_hull_left (s : Set G) (D : PointedCone R H) :
    minTensorProduct (hull R s) D =
      hull R (Set.image2 (fun x y => x ⊗ₜ[R] y) s (D : Set H)) :=
by
  change Submodule.span {c : R // 0 ≤ c} (Set.image2 (fun x y => x ⊗ₜ[R] y)
      (Submodule.span {c : R // 0 ≤ c} s) (D : Set H)) =
    Submodule.span {c : R // 0 ≤ c} (Set.image2 (fun x y => x ⊗ₜ[R] y) s (D : Set H))
  let f := (TensorProduct.mk R G H).restrictScalars₁₂
    {c : R // 0 ≤ c} {c : R // 0 ≤ c}
  exact (Submodule.map₂_eq_span_image2 (R := {c : R // 0 ≤ c}) f _ _).symm.trans
    (by
      simpa only [f, Submodule.span_eq, LinearMap.restrictScalars₁₂_apply_apply,
        TensorProduct.mk_apply] using
        (Submodule.map₂_span_span {c : R // 0 ≤ c} f s (D : Set H)))

end PointedCone
