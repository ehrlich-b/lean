import LeanFactory.Month.KrausTraceNormalization
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.Matrix.Order
import Mathlib.Algebra.Star.UnitaryStarAlgAut

open scoped CStarAlgebra Matrix MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Unitary conjugation is represented in Mathlib's existing completely-positive-map carrier. -/
theorem unitary_conj_completelyPositive (U : unitary (Matrix n n ℂ)) :
    ∃ φ : Matrix n n ℂ →CP Matrix n n ℂ,
      ∀ X : Matrix n n ℂ, φ X = (U : Matrix n n ℂ) * X * (U : Matrix n n ℂ)ᴴ :=
by
  refine ⟨(Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U : Matrix n n ℂ →CP Matrix n n ℂ), ?_⟩
  intro X
  rfl


end Matrix
