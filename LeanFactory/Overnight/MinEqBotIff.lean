import Mathlib.Geometry.Convex.Cone.TensorProduct

open TensorProduct

namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]

/-- Over a field, the minimal tensor cone is zero exactly when one factor is zero. -/
theorem minTensorProduct_eq_bot_iff (C : PointedCone R G) (D : PointedCone R H) :
    minTensorProduct C D = ⊥ ↔ C = ⊥ ∨ D = ⊥ :=
by
  constructor
  · intro h
    by_contra hCD
    rw [not_or] at hCD
    obtain ⟨x, hx, hx0⟩ := C.ne_bot_iff.mp hCD.1
    obtain ⟨y, hy, hy0⟩ := D.ne_bot_iff.mp hCD.2
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero R hx0
    obtain ⟨g, hg⟩ := Module.Projective.exists_dual_ne_zero R hy0
    have hzero : x ⊗ₜ[R] y = 0 := by
      have hxy := tmul_mem_minTensorProduct hx hy
      rw [h] at hxy
      simpa using hxy
    have hfg : f x * g y = 0 := by
      have hz := congrArg (dualDistrib R G H (f ⊗ₜ[R] g)) hzero
      simpa [dualDistrib_apply] using hz
    exact (mul_ne_zero hf hg) hfg
  · rintro (rfl | rfl) <;> simp [minTensorProduct]

end PointedCone
