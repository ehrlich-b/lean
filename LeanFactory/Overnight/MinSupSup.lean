import Mathlib.Geometry.Convex.Cone.TensorProduct

open TensorProduct

namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- Bilinearity of minimal tensor products over binary joins in both inputs. -/
theorem minTensorProduct_sup_sup (C C' : PointedCone R G) (D D' : PointedCone R H) :
    minTensorProduct (C ⊔ C') (D ⊔ D') =
      (minTensorProduct C D ⊔ minTensorProduct C D') ⊔
        (minTensorProduct C' D ⊔ minTensorProduct C' D') :=
by
  refine le_antisymm (Submodule.span_le.mpr ?_) ?_
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    rcases Submodule.mem_sup.mp hx with ⟨x₁, hx₁, x₂, hx₂, rfl⟩
    rcases Submodule.mem_sup.mp hy with ⟨y₁, hy₁, y₂, hy₂, rfl⟩
    change (x₁ + x₂) ⊗ₜ[R] (y₁ + y₂) ∈ _
    rw [add_tmul, tmul_add, tmul_add]
    exact add_mem
      (add_mem
        (Submodule.mem_sup_left (Submodule.mem_sup_left
          (tmul_mem_minTensorProduct hx₁ hy₁)))
        (Submodule.mem_sup_left (Submodule.mem_sup_right
          (tmul_mem_minTensorProduct hx₁ hy₂))))
      (add_mem
        (Submodule.mem_sup_right (Submodule.mem_sup_left
          (tmul_mem_minTensorProduct hx₂ hy₁)))
        (Submodule.mem_sup_right (Submodule.mem_sup_right
          (tmul_mem_minTensorProduct hx₂ hy₂))))
  · refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
    · exact minTensorProduct_mono le_sup_left le_sup_left
    · exact minTensorProduct_mono le_sup_left le_sup_right
    · exact minTensorProduct_mono le_sup_right le_sup_left
    · exact minTensorProduct_mono le_sup_right le_sup_right

end PointedCone
