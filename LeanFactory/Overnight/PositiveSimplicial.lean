import Mathlib.Geometry.Convex.Cone.Simplicial


namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]

/-- The nonnegative scalar cone is simplicial. -/
theorem isSimplicial_positive : (positive R R).IsSimplicial :=
by
  have hpos : positive R R = PointedCone.hull R ({1} : Set R) := by
    apply PointedCone.ext
    intro x
    constructor
    · intro hx
      have h1 : (1 : R) ∈ Submodule.span {c : R // 0 ≤ c} ({1} : Set R) :=
        Submodule.subset_span (by simp)
      have hmem :=
        Submodule.smul_mem
          (Submodule.span {c : R // 0 ≤ c} ({1} : Set R)) ⟨x, hx⟩ h1
      change (x : R) * 1 ∈ Submodule.span {c : R // 0 ≤ c} ({1} : Set R) at hmem
      simpa [PointedCone.hull] using hmem
    · intro hx
      exact (Submodule.span_le.2 (by simp [positive])) hx
  rw [hpos]
  exact PointedCone.IsSimplicial.hull (Set.finite_singleton (1 : R))
    (LinearIndepOn.singleton one_ne_zero)

end PointedCone
