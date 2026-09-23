import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Pi

namespace PointedCone
open scoped PointedCone

variable (ι : Type*) [Fintype ι]

/-- The nonnegative orthant of a finite real coordinate space linearly generates the space.
This is exactly the `h₁_gen` hypothesis needed to feed the frozen simplicial min/max
coincidence `PointedCone.minTensorProduct_eq_max_of_simplicial_generating_left/_right`.
Small finite-coordinate consumer of the standard-basis span fact `Module.Basis.span_eq`
and of the orthant membership characterization `PointedCone.mem_positive`. -/
theorem span_positive_orthant_eq_top :
    Submodule.span ℝ (PointedCone.positive ℝ (ι → ℝ) : Set (ι → ℝ)) = ⊤ :=
by
  classical
  apply le_antisymm le_top
  rw [← (Pi.basisFun ℝ ι).span_eq]
  apply Submodule.span_mono
  intro x hx
  rcases hx with ⟨i, rfl⟩
  simpa only [SetLike.mem_coe, PointedCone.mem_toConvexCone, PointedCone.mem_positive] using
    (PointedCone.mem_positive (R := ℝ) (E := ι → ℝ)).mpr (by
      intro j
      by_cases h : i = j
      · subst h
        rw [Pi.basisFun_apply, Pi.single_eq_same]
        norm_num
      · rw [Pi.basisFun_apply, Pi.single_eq_of_ne' h]
        norm_num)


end PointedCone
