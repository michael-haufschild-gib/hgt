import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Algebra.Hom

/-!
# Scalar evaluations of the full arithmetic coefficient algebra

Every complex algebra homomorphism from the full Dirichlet-convolution algebra of arithmetic
functions to `ℂ` is evaluation at coefficient `1`. No continuity assumption is needed: a family
whose coefficient at `1` is nonzero is a unit, so subtracting the proposed scalar value forces
that value to equal coefficient `1`.

This classifies the full formal coefficient algebra, not a proper algebra with convergence
conditions. In particular it supplies no zero-location theorem and cannot justify extending
analytic Dirichlet evaluation to every formal coefficient family.
-/

noncomputable section

namespace RHTower

/-- Evaluation at the multiplicative unit coefficient, as a complex algebra homomorphism. -/
def arithmeticFunctionAugmentation : ArithmeticFunction ℂ →ₐ[ℂ] ℂ where
  toFun f := f 1
  map_zero' := rfl
  map_one' := ArithmeticFunction.one_one
  map_add' _ _ := rfl
  map_mul' _ _ := ArithmeticFunction.mul_apply_one
  commutes' z := by
    exact ArithmeticFunction.algebraMap_apply_one z

/-- Every scalar-preserving multiplicative evaluation of the full coefficient algebra is forced
to read coefficient `1`; no topological or analytic assumption enters. -/
theorem arithmeticFunctionAlgHom_apply
    (φ : ArithmeticFunction ℂ →ₐ[ℂ] ℂ) (f : ArithmeticFunction ℂ) :
    φ f = f 1 := by
  by_contra h
  have hunit : IsUnit (f - algebraMap ℂ (ArithmeticFunction ℂ) (φ f)) := by
    apply ArithmeticFunction.isUnit_iff_isUnit_apply_one.mpr
    change IsUnit (f 1 - (algebraMap ℂ (ArithmeticFunction ℂ) (φ f)) 1)
    rw [ArithmeticFunction.algebraMap_apply_one]
    exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr fun heq => h heq.symm)
  have hzero : IsUnit (0 : ℂ) := by
    simpa using IsUnit.map φ hunit
  exact not_isUnit_zero hzero

/-- Augmentation is the unique complex algebra homomorphism to `ℂ`. -/
theorem arithmeticFunctionAlgHom_eq_augmentation
    (φ : ArithmeticFunction ℂ →ₐ[ℂ] ℂ) :
    φ = arithmeticFunctionAugmentation := by
  ext f
  exact arithmeticFunctionAlgHom_apply φ f

end RHTower
