import Mathlib.Geometry.Convex.Cone.TensorProduct

open TensorProduct

namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H K G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- Bridge dual cone membership and positive bilinear forms without a finite-dimensional assumption. -/
theorem mem_dual_minTensorProduct_iff (C : PointedCone R G) (D : PointedCone R H)
    (φ : Module.Dual R (G ⊗[R] H)) :
    φ ∈ dual (Module.Dual.eval R (G ⊗[R] H)) (minTensorProduct C D) ↔
      ∀ x ∈ C, ∀ y ∈ D, 0 ≤ φ (x ⊗ₜ[R] y) :=
by
  simp only [minTensorProduct, dual_hull, mem_dual, Set.forall_mem_image2,
    SetLike.mem_coe, Module.Dual.eval_apply]

end PointedCone
