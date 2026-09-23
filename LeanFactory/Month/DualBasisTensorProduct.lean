import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Contraction

namespace Module.Basis

variable {R M N ι κ : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The dual basis of the tensor-product basis on the product index is the tensor
product of the dual bases, transported by the dual-distribution equivalence. -/
theorem dualBasis_tensorProduct (b : Basis ι R M) (c : Basis κ R N) :
    (b.tensorProduct c).dualBasis =
      (b.dualBasis.tensorProduct c.dualBasis).map
        (TensorProduct.dualDistribEquivOfBasis b c) :=
by
  apply DFunLike.ext
  rintro ⟨i, j⟩
  apply TensorProduct.ext'
  rintro m n
  simp only [Basis.map_apply, Basis.tensorProduct_apply, TensorProduct.dualDistribEquivOfBasis,
    LinearEquiv.coe_ofLinearMap, TensorProduct.dualDistrib_apply, Module.Basis.dualBasis_apply,
    Basis.tensorProduct_repr_tmul_apply, smul_eq_mul]
  exact mul_comm (c.repr n j) (b.repr m i)


end Module.Basis
