import Mathlib.LinearAlgebra.Matrix.Trace

open Matrix

namespace LeanFactory

variable {n R : Type*} [Fintype n] [CommRing R] [StarRing R]

/-- The quadratic form `star x ⬝ᵥ (M *ᵥ x)` is the trace pairing of `M` with the
rank-one matrix `vecMulVec x (star x)` (the outer product of `x` with `star x`),
so a quadratic-form PSD check is equivalently a check on trace pairings against
rank-one matrices. This identity carries no order axioms and reads off the
definitions of `dotProduct`, `mulVec`, `vecMulVec` and `trace` only. -/
lemma star_dotProduct_mulVec_eq_trace_mul_vecMulVec (M : Matrix n n R) (x : n → R) :
    star x ⬝ᵥ (M *ᵥ x) = trace (M * vecMulVec x (star x)) :=
by
  rw [mul_vecMulVec, trace_vecMulVec]
  exact dotProduct_comm (star x) (M *ᵥ x)


end LeanFactory
