import Mathlib.Geometry.Convex.Cone.TensorProduct

open TensorProduct

namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- Bilinearity of minimal tensor products over arbitrary joins in both inputs. -/
theorem minTensorProduct_iSup_iSup {ι κ : Sort*} (C : ι → PointedCone R G)
    (D : κ → PointedCone R H) :
    minTensorProduct (⨆ i, C i) (⨆ j, D j) =
      ⨆ i, ⨆ j, minTensorProduct (C i) (D j) :=
by
  let f := (TensorProduct.mk R G H).restrictScalars₁₂
    {r : R // 0 ≤ r} {r : R // 0 ≤ r}
  have h (E : PointedCone R G) (F : PointedCone R H) :
      minTensorProduct E F = Submodule.map₂ f E F := by
    simp [f, minTensorProduct, hull, Submodule.map₂_eq_span_image2]
  calc
    minTensorProduct (⨆ i, C i) (⨆ j, D j) =
        Submodule.map₂ f (⨆ i, C i) (⨆ j, D j) := h _ _
    _ = ⨆ i, Submodule.map₂ f (C i) (⨆ j, D j) :=
      Submodule.map₂_iSup_left f C (⨆ j, D j)
    _ = ⨆ i, ⨆ j, Submodule.map₂ f (C i) (D j) := by
      congr 1
      funext i
      exact Submodule.map₂_iSup_right f (C i) D
    _ = ⨆ i, ⨆ j, minTensorProduct (C i) (D j) := by
      congr 1
      funext i
      congr 1
      funext j
      exact (h (C i) (D j)).symm

end PointedCone
