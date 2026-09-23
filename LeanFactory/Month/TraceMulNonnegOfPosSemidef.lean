import LeanFactory.Month.StarDotMulVecEqTrace
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.LinearAlgebra.Matrix.Trace

open Matrix
open scoped ComplexOrder

namespace LeanFactory

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- The trace pairing of two positive semidefinite matrices is nonnegative: the
"positive part" of PSD-cone self-duality under the trace pairing, isolated as a
single analytic dependency. -/
theorem trace_mul_nonneg_of_posSemidef {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ trace (A * B) :=
by
  rcases (Matrix.posSemidef_iff_eq_sum_vecMulVec (M := B)).mp hB with ⟨m, v, hBsum⟩
  rw [hBsum, Matrix.mul_sum, Matrix.trace_sum]
  exact Finset.sum_nonneg fun i _ => by
    rw [← star_dotProduct_mulVec_eq_trace_mul_vecMulVec A (v i)]
    exact hA.dotProduct_mulVec_nonneg (v i)


end LeanFactory
