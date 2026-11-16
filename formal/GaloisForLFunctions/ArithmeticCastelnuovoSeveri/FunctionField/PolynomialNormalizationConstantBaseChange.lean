import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.PolynomialAlgebra

/-!
# Polynomial normalization under separable constant extension

A finite separable extension of constants makes the polynomial coefficient
extension smooth. Integral closure therefore commutes with this base change.
The polynomial pushout identifies the source with the literal constant tensor
of the original normalization.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
open scoped TensorProduct
attribute [local instance] Polynomial.algebra

variable (K E : Type*) [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]

/-- Polynomial coefficient extension along a finite separable field extension is smooth. -/
theorem finiteSeparablePolynomial_smooth : Algebra.Smooth K[X] E[X] := by
  letI : Algebra.FormallyEtale K E := Algebra.FormallyEtale.of_isSeparable K E
  letI : Algebra.FinitePresentation K E := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  letI : Algebra.Smooth K E := {}
  exact Algebra.Smooth.of_equiv (Algebra.IsPushout.equiv K K[X] E E[X])

variable (L : Type*) [CommRing L] [Algebra K L] [Algebra K[X] L]
    [IsScalarTower K K[X] L]

/-- The normalization after polynomial coefficient extension is the constant tensor of the original integral closure. -/
def polynomialNormalizationConstantTensorEquiv :
    (E ⊗[K] integralClosure K[X] L) ≃ₐ[E]
      integralClosure E[X] (E[X] ⊗[K[X]] L) := by
  letI : Algebra.Smooth K[X] E[X] := finiteSeparablePolynomial_smooth K E
  exact (Algebra.IsPushout.cancelBaseChangeAlg K E K[X] E[X]
    (integralClosure K[X] L)).symm.trans
      ((AlgEquiv.ofBijective (TensorProduct.toIntegralClosure K[X] E[X] L)
        TensorProduct.toIntegralClosure_bijective_of_smooth).restrictScalars E)

/-- The normalization comparison sends a pure constant tensor to the corresponding polynomial tensor. -/
theorem polynomialNormalizationConstantTensorEquiv_tmul (a : E) (b : integralClosure K[X] L) :
    (polynomialNormalizationConstantTensorEquiv K E L (a ⊗ₜ[K] b)).val =
      C a ⊗ₜ[K[X]] (b.val : L) := by
  change ((TensorProduct.toIntegralClosure K[X] E[X] L)
    ((Algebra.IsPushout.cancelBaseChangeAlg K E K[X] E[X]
      (integralClosure K[X] L)).symm (a ⊗ₜ[K] b))).val = _
  rw [Algebra.IsPushout.cancelBaseChangeAlg_symm_tmul]
  rfl

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
