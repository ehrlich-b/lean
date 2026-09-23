import LeanFactory.Month.UnitaryConjChannel

namespace LeanFactory

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [CommRing 𝕜] [StarRing 𝕜]

/-- Unitary conjugation is trace-preserving and its conjugate unitary supplies the explicit trace-pairing adjoint. -/
theorem unitaryConj_tracePreserving_and_isTraceAdjointPair
    (U : Matrix n n 𝕜) (hU : U ∈ Matrix.unitaryGroup n 𝕜)
    (hUstar : star U ∈ Matrix.unitaryGroup n 𝕜) :
    TracePreserving (unitaryConj U hU) ∧
      IsTraceAdjointPair (unitaryConj U hU) (unitaryConj (star U) hUstar) :=
by
  have hAdj : IsTraceAdjointPair (unitaryConj U hU) (unitaryConj (star U) hUstar) := by
    intro X Y
    have hstarU_conj : Matrix.conjTranspose (star U) = U := by
      rw [← Matrix.star_eq_conjTranspose (star U)]
      rw [star_star]
    have hInner : Matrix.conjTranspose ((star U) * Y * Matrix.conjTranspose (star U)) =
        Matrix.conjTranspose U * Matrix.conjTranspose Y * U := by
      calc
        Matrix.conjTranspose ((star U) * Y * Matrix.conjTranspose (star U))
            = Matrix.conjTranspose (Matrix.conjTranspose (star U)) *
              Matrix.conjTranspose Y * Matrix.conjTranspose (star U) := by
              simp [Matrix.mul_assoc]
        _ = Matrix.conjTranspose U * Matrix.conjTranspose Y * U := by
              rw [Matrix.conjTranspose_conjTranspose]
              rw [hstarU_conj]
              rw [Matrix.star_eq_conjTranspose]
    calc
      Matrix.trace (unitaryConj U hU X * Matrix.conjTranspose Y)
          = Matrix.trace ((U * X * Matrix.conjTranspose U) * Matrix.conjTranspose Y) := by
              simp [unitaryConj]
      _ = Matrix.trace (X * (Matrix.conjTranspose U * Matrix.conjTranspose Y * U)) := by
              simpa [Matrix.mul_assoc] using
                Matrix.trace_mul_comm (A := U) (B := X * Matrix.conjTranspose U * Matrix.conjTranspose Y)
      _ = Matrix.trace (X * Matrix.conjTranspose ((star U) * Y * Matrix.conjTranspose (star U))) := by
              rw [← hInner]
      _ = Matrix.trace (X * Matrix.conjTranspose (unitaryConj (star U) hUstar Y)) := by
              simp [unitaryConj]
  constructor
  · exact (tracePreserving_iff_traceAdjoint_unital (Φ := unitaryConj U hU)
      (ΦStar := unitaryConj (star U) hUstar) hAdj).mpr (unitaryConj_unital (star U) hUstar)
  · exact hAdj


end LeanFactory
