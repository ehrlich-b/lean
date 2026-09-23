import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

open Matrix

namespace LeanFactory

variable {𝕜 m n : Type*} [Semiring 𝕜] [StarRing 𝕜]
variable [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- A map preserves trace exactly when its explicit trace-pairing adjoint fixes the identity.

The trace pairing is fixed at statement level as `trace (X * Yᴴ)`: this contract does not use
`LinearMap.adjoint` or install a matrix inner-product instance. -/
def TracePreserving (Φ : Matrix n n 𝕜 →ₗ[𝕜] Matrix m m 𝕜) : Prop :=
  ∀ X, trace (Φ X) = trace X

/-- `ΦStar` is the adjoint partner of `Φ` for the explicit matrix trace pairing. -/
def IsTraceAdjointPair
    (Φ : Matrix n n 𝕜 →ₗ[𝕜] Matrix m m 𝕜)
    (ΦStar : Matrix m m 𝕜 →ₗ[𝕜] Matrix n n 𝕜) : Prop :=
  ∀ X Y, trace (Φ X * Yᴴ) = trace (X * (ΦStar Y)ᴴ)

/-- Trace preservation is equivalent to unitality of the explicit trace-pairing adjoint. -/
theorem tracePreserving_iff_traceAdjoint_unital
    (Φ : Matrix n n 𝕜 →ₗ[𝕜] Matrix m m 𝕜)
    (ΦStar : Matrix m m 𝕜 →ₗ[𝕜] Matrix n n 𝕜)
    (hAdj : IsTraceAdjointPair Φ ΦStar) :
    TracePreserving Φ ↔ ΦStar 1 = 1 :=
by
  constructor
  · intro hU
    have hX : ∀ X : Matrix n n 𝕜, trace (X * (ΦStar 1)ᴴ) = trace X := by
      intro X
      calc
        trace (X * (ΦStar 1)ᴴ) = trace (Φ X * (1 : Matrix m m 𝕜)ᴴ) := by
          exact (hAdj X 1).symm
        _ = trace (Φ X) := by simp
        _ = trace X := hU X
    have ht : (ΦStar 1)ᴴ = (1 : Matrix n n 𝕜)ᴴ := by
      apply Matrix.ext_iff_trace_mul_left.mpr
      intro A
      calc
        (A * (ΦStar 1)ᴴ).trace = A.trace := hX A
        _ = (A * (1 : Matrix n n 𝕜)ᴴ).trace := by simp
    exact Matrix.conjTranspose_inj.mp ht
  · intro hTP
    intro X
    calc
      trace (Φ X) = trace (Φ X * (1 : Matrix m m 𝕜)ᴴ) := by simp
      _ = trace (X * (ΦStar 1)ᴴ) := by simpa using hAdj X 1
      _ = trace (X * (1 : Matrix n n 𝕜)ᴴ) := by rw [hTP]
      _ = trace X := by simp


end LeanFactory
