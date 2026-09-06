import Mathlib.Geometry.Convex.Cone.TensorProduct

open TensorProduct

namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H K G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- Ambient tensor-space sanity theorem from conic generation by all elementary tensors. -/
theorem minTensorProduct_top_top :
    minTensorProduct (⊤ : PointedCone R G) (⊤ : PointedCone R H) = ⊤ :=
by
  apply le_antisymm le_top
  change (⊤ : PointedCone R (G ⊗[R] H)) ≤ _
  let s : Set (G ⊗[R] H) :=
    Set.image2 (fun g h => g ⊗ₜ[R] h) (⊤ : Set G) (⊤ : Set H)
  change (⊤ : PointedCone R (G ⊗[R] H)) ≤ PointedCone.hull R s
  have hneg : ∀ x, x ∈ PointedCone.hull R s → -x ∈ PointedCone.hull R s := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨g, hg, h, hh, rfl⟩
        rw [← neg_tmul]
        exact PointedCone.subset_hull (Set.mem_image2_of_mem
          (show -g ∈ (⊤ : Set G) from trivial) hh)
    | zero => simp
    | add x y _ _ hx hy => simpa [add_comm] using (PointedCone.hull R s).add_mem hx hy
    | smul c x _ hx =>
        simpa using (PointedCone.hull R s).smul_mem c.2 hx
  have hspan : Submodule.span R s = ⊤ := by
    apply le_antisymm le_top
    have hpure :
        Submodule.span R {t : G ⊗[R] H | ∃ g h, g ⊗ₜ[R] h = t} ≤ Submodule.span R s := by
      apply Submodule.span_le.2
      rintro _ ⟨g, h, rfl⟩
      exact Submodule.subset_span (Set.mem_image2_of_mem
        (show g ∈ (⊤ : Set G) from trivial)
        (show h ∈ (⊤ : Set H) from trivial))
    exact (TensorProduct.span_tmul_eq_top R G H).symm.le.trans hpure
  intro x hx
  have hx' : x ∈ Submodule.span R s := hspan.symm ▸ hx
  refine Submodule.span_induction (p := fun x _ => x ∈ PointedCone.hull R s) ?_ ?_ ?_ ?_ hx'
  · intro x hx
    exact PointedCone.subset_hull hx
  · exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    exact (PointedCone.hull R s).add_mem hx hy
  · intro c x _ hx
    rcases le_total 0 c with hc | hc
    · exact (PointedCone.hull R s).smul_mem hc hx
    · simpa using (PointedCone.hull R s).smul_mem (neg_nonneg.mpr hc) (hneg x hx)

end PointedCone
