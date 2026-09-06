import Mathlib.Geometry.Convex.Cone.TensorProduct

open TensorProduct

namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- Linear images commute with the minimal tensor product of pointed cones. -/
theorem minTensorProduct_map (f : G →ₗ[R] G') (g : H →ₗ[R] H')
    (C₁ : PointedCone R G) (C₂ : PointedCone R H) :
    (minTensorProduct C₁ C₂).map (TensorProduct.map f g) =
      minTensorProduct (C₁.map f) (C₂.map g) :=
by
  simp [minTensorProduct, map, hull, Submodule.map_span, Set.image_image2,
    Set.image2_image_left, Set.image2_image_right, map_tmul]

end PointedCone
