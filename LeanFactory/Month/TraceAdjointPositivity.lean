import LeanFactory.Month.PosSemidefIffForallPosSemidefTraceReNonneg
import LeanFactory.Month.TraceMulNonnegOfPosSemidef

open Matrix
open scoped ComplexOrder

namespace LeanFactory

variable {n m : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]

/-- Positivity passes to a Hermitian-preserving trace-adjoint partner. -/
theorem traceAdjoint_preserves_posSemidef
    (F : Matrix n n ℂ →ₗ[ℝ] Matrix m m ℂ)
    (G : Matrix m m ℂ →ₗ[ℝ] Matrix n n ℂ)
    (hadj : ∀ A B, A.IsHermitian → B.IsHermitian →
      RCLike.re (trace (F A * B)) = RCLike.re (trace (A * G B)))
    (hG : ∀ B, B.IsHermitian → (G B).IsHermitian)
    (hF : ∀ A, A.PosSemidef → (F A).PosSemidef)
    {B : Matrix m m ℂ} (hB : B.PosSemidef) :
    (G B).PosSemidef :=
by
  apply (posSemidef_iff_forall_posSemidef_trace_re_nonneg
    (hG B hB.1)).2
  intro A hA
  have hpair := hadj A B hA.1 hB.1
  have htrace : 0 ≤ trace (F A * B) :=
    trace_mul_nonneg_of_posSemidef (hF A hA) hB
  have hre : 0 ≤ RCLike.re (trace (F A * B)) :=
    RCLike.nonneg_iff.mp htrace |>.1
  rw [trace_mul_comm, ← hpair]
  exact hre


end LeanFactory
