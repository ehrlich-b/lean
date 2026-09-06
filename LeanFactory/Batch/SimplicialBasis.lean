import Mathlib.Geometry.Convex.Cone.Simplicial
import Mathlib.LinearAlgebra.Basis.Basic

namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H K G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- Extract the reusable basis construction currently embedded in the existing min/max coincidence proof. -/
theorem IsSimplicial.exists_basis {C : PointedCone R G} (hC : C.IsSimplicial)
    (hgen : Submodule.span R (C : Set G) = ⊤) :
    ∃ (s : Set G) (b : Module.Basis s R G), s.Finite ∧ hull R (Set.range b) = C :=
by
  rcases hC with ⟨s, hs, hli, hcone⟩
  have hsubset : (C : Set G) ⊆ Submodule.span R s := by
    rw [← hcone]
    exact fun x hx => (hull_le_span R s) hx
  have hspan : Submodule.span R s = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact Submodule.span_le.2 hsubset
  let b : Module.Basis s R G :=
    Module.Basis.mk (v := (Subtype.val : s → G))
      (linearIndependent_subtype_iff.mpr hli) <| by
      simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hspan.ge
  refine ⟨s, b, hs, ?_⟩
  simpa only [b, Module.Basis.coe_mk, Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hcone

end PointedCone
