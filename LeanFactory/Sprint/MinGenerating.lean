import Mathlib.Geometry.Convex.Cone.TensorProduct

open TensorProduct

namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H K G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- Generating factors give a generating composite; useful before finite-dimensional duality arguments. -/
theorem minTensorProduct_generating (C : PointedCone R G) (D : PointedCone R H)
    (hC : Submodule.span R (C : Set G) = ⊤)
    (hD : Submodule.span R (D : Set H) = ⊤) :
    Submodule.span R (minTensorProduct C D : Set (G ⊗[R] H)) = ⊤ :=
by
  have hspan :
      Submodule.span R
          (Set.image2 (fun m n => TensorProduct.mk R G H m n) (C : Set G) (D : Set H)) = ⊤ := by
    rw [← Submodule.map₂_span_span R (TensorProduct.mk R G H) (C : Set G) (D : Set H), hC, hD]
    exact TensorProduct.map₂_mk_top_top_eq_top R G H
  apply le_antisymm le_top
  calc
    (⊤ : Submodule R (G ⊗[R] H)) =
        Submodule.span R (Set.image2 (· ⊗ₜ[R] ·) (C : Set G) (D : Set H)) := by
      simpa only [TensorProduct.mk_apply] using hspan.symm
    _ ≤ Submodule.span R (minTensorProduct C D : Set (G ⊗[R] H)) :=
      Submodule.span_mono (tmul_subset_minTensorProduct C D)

end PointedCone
