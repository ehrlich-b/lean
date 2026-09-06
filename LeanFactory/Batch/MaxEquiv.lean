import Mathlib.Geometry.Convex.Cone.TensorProduct

open TensorProduct

namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H K G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- Change of coordinates for maximal tensors with the necessary invertibility. -/
theorem maxTensorProduct_map_equiv (e : G ≃ₗ[R] G') (f : H ≃ₗ[R] H')
    (C : PointedCone R G) (D : PointedCone R H) :
    (maxTensorProduct C D).map (TensorProduct.map e.toLinearMap f.toLinearMap) =
      maxTensorProduct (C.map e.toLinearMap) (D.map f.toLinearMap) :=
by
  have he₁ : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
    ext x
    exact e.apply_symm_apply x
  have he₂ : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
    ext x
    exact e.symm_apply_apply x
  have hf₁ : f.toLinearMap.comp f.symm.toLinearMap = LinearMap.id := by
    ext x
    exact f.apply_symm_apply x
  have hf₂ : f.symm.toLinearMap.comp f.toLinearMap = LinearMap.id := by
    ext x
    exact f.symm_apply_apply x
  apply le_antisymm
  · exact maxTensorProduct_map_le e.toLinearMap f.toLinearMap C D
  · intro z hz
    have hz' := maxTensorProduct_map_le e.symm.toLinearMap f.symm.toLinearMap
      (C.map e.toLinearMap) (D.map f.toLinearMap) ⟨z, hz, rfl⟩
    refine ⟨TensorProduct.map e.symm.toLinearMap f.symm.toLinearMap z, ?_, ?_⟩
    · simpa [PointedCone.map_map, he₂, hf₂] using hz'
    · simpa [he₁, hf₁] using
        (TensorProduct.map_map e.toLinearMap f.toLinearMap e.symm.toLinearMap
          f.symm.toLinearMap z)

end PointedCone
