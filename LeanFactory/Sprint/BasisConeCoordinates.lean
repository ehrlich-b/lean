import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Geometry.Convex.Cone.TensorProduct

open TensorProduct

namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H K G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- Coordinate description of a basis-generated cone; reusable bridge to nonnegative orthants. -/
theorem mem_hull_basis_iff {ι : Type*} [Fintype ι] (b : Module.Basis ι R G) (x : G) :
    x ∈ hull R (Set.range b) ↔ ∀ i, 0 ≤ b.repr x i :=
by
  classical
  let C := (PointedCone.positive R (ι → R)).comap b.equivFun.toLinearMap
  have hb : Set.range b ⊆ (C : Set G) := by
    rintro y ⟨i, rfl⟩
    change 0 ≤ b.equivFun (b i)
    intro j
    by_cases h : i = j <;> simp [b.equivFun_self, h]
  have hle : PointedCone.hull R (Set.range b) ≤ C := by
    exact Submodule.span_le.2 hb
  constructor
  · intro hx
    have hy : x ∈ C := hle hx
    change 0 ≤ b.equivFun x at hy
    change ∀ i, 0 ≤ b.equivFun x i
    exact hy
  · intro hx
    change ∀ i, 0 ≤ b.equivFun x i at hx
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ =>
      PointedCone.smul_mem (PointedCone.hull R (Set.range b)) (hx i)
        (PointedCone.subset_hull ⟨i, rfl⟩)

end PointedCone
