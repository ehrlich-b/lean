import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.RCLike.Basic

open Matrix

namespace LeanFactory

variable {n 𝕜 : Type*} [Fintype n] [RCLike 𝕜]

/-- The trace of a product of Hermitian matrices is fixed by conjugation. -/
theorem star_trace_mul_eq_self_of_isHermitian
    (A B : Matrix n n 𝕜) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    star (trace (A * B)) = trace (A * B) :=
by
  rw [← trace_conjTranspose, conjTranspose_mul, trace_mul_comm, hA, hB]


end LeanFactory
