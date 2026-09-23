import LeanFactory.Month.OrthantBasisConeExample
import LeanFactory.Month.PositiveOrthantGenerating
import Mathlib.Analysis.Convex.Cone.TensorProduct
import Mathlib.LinearAlgebra.StdBasis

namespace PointedCone

open scoped PointedCone

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

/-- The minimal and maximal tensor products of two finite real nonnegative orthants coincide. -/
theorem minTensorProduct_positive_orthant_orthant_eq_max :
    minTensorProduct (PointedCone.positive ℝ (ι → ℝ)) (PointedCone.positive ℝ (κ → ℝ)) =
      maxTensorProduct (PointedCone.positive ℝ (ι → ℝ)) (PointedCone.positive ℝ (κ → ℝ)) :=
by
  classical
  simpa [ProperCone.toPointedCone_positive] using
    minTensorProduct_eq_max_of_simplicial_generating_left
      (C₁ := PointedCone.positive ℝ (ι → ℝ))
      (C₂ := ProperCone.positive ℝ (κ → ℝ))
      (by
        rw [← PointedCone.hull_stbasis_eq_positive]
        exact PointedCone.IsSimplicial.hull
          (Set.finite_range (Pi.basisFun ℝ ι))
          ((Pi.basisFun ℝ ι).linearIndependent.linearIndepOn_id))
      (PointedCone.span_positive_orthant_eq_top ι)


end PointedCone
