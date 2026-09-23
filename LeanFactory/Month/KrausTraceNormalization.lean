import Mathlib.LinearAlgebra.Matrix.Trace

open Matrix

namespace Matrix

variable {n ι R : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [CommRing R] [StarRing R]

/-- Finite Kraus trace-normalization seam: the trace of the left Kraus action
`X ↦ ∑ i, K i * X * (K i)ᴴ` equals the trace of the product of `X` with the dual
dyadic sum `∑ i, (K i)ᴴ * K i` on the right. This pins the single left-action
orientation and the `trace_sum`-over-`Finset.univ` convention; it needs only
`trace_sum`, `trace_mul_cycle`, `trace_mul_comm`, associativity and `Finset.mul_sum`,
so it holds over any commutative ring with star. -/
theorem trace_krausMap (K : ι → Matrix n n R) (X : Matrix n n R) :
    (∑ i, K i * X * (K i)ᴴ).trace = (X * ∑ i, (K i)ᴴ * K i).trace :=
by
  rw [trace_sum, Finset.mul_sum, trace_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  calc
    trace (K i * X * (K i)ᴴ) = trace ((K i)ᴴ * K i * X) := trace_mul_cycle (K i) X (K i)ᴴ
    _ = trace (X * ((K i)ᴴ * K i)) := trace_mul_comm ((K i)ᴴ * K i) X


end Matrix
