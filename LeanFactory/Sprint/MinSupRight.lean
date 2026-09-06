import Mathlib.Geometry.Convex.Cone.TensorProduct

open TensorProduct

namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H K G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- Complete the binary-join API for positive decompositions in the second factor. -/
theorem minTensorProduct_sup_right (C : PointedCone R G) (D E : PointedCone R H) :
    minTensorProduct C (D ⊔ E) = minTensorProduct C D ⊔ minTensorProduct C E :=
by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, y, hy, rfl⟩
    rcases Submodule.mem_sup.1 hy with ⟨y₁, hy₁, y₂, hy₂, rfl⟩
    change x ⊗ₜ[R] (y₁ + y₂) ∈ _
    rw [tmul_add]
    exact add_mem
      ((le_sup_left : minTensorProduct C D ≤ minTensorProduct C D ⊔ minTensorProduct C E)
        (tmul_mem_minTensorProduct hx hy₁))
      ((le_sup_right : minTensorProduct C E ≤ minTensorProduct C D ⊔ minTensorProduct C E)
        (tmul_mem_minTensorProduct hx hy₂))
  · exact sup_le (minTensorProduct_mono le_rfl le_sup_left)
      (minTensorProduct_mono le_rfl le_sup_right)

end PointedCone
