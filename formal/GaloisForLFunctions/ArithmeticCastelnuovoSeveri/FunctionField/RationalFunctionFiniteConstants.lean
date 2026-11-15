import GaloisForLFunctions.HTGeometry.RationalFunctionConstantBaseChange
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Finite extension of rational-function constants

The rational tensor product is a domain for arbitrary enlarged constants.
For finite constant extensions it is finite-dimensional over the original
rational function field, hence is already a field. The resulting literal
tensor equivalence preserves the coordinate and extends coefficients.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
open scoped TensorProduct
variable (K E : Type*) [Field K] [Field E] [Algebra K E]

open GaloisForLFunctions.HTGeometry

/-- The univariate rational function field agrees with the fraction field of the one-variable multivariate polynomial ring. -/
def rationalPolynomialFractionEquiv :
    FractionRing (MvPolynomial PUnit.{1} K) ≃ₐ[K] FractionRing K[X] :=
  IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.uniqueAlgEquiv K PUnit.{1})

/-- The one-variable fraction equivalence preserves the polynomial coordinate. -/
theorem rationalPolynomialFractionEquiv_X :
    rationalPolynomialFractionEquiv K
      (algebraMap (MvPolynomial PUnit.{1} K) (FractionRing (MvPolynomial PUnit.{1} K))
        (MvPolynomial.X PUnit.unit)) = algebraMap K[X] (FractionRing K[X]) X := by
  rw [rationalPolynomialFractionEquiv, IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  change algebraMap K[X] (FractionRing K[X])
    (MvPolynomial.eval₂ Polynomial.C (fun _ : PUnit.{1} => Polynomial.X)
      (MvPolynomial.X PUnit.unit)) = _
  rw [MvPolynomial.eval₂_X]

/-- Extending the constants of a rational function field gives an integral domain. -/
instance rationalConstantTensor_isDomain : IsDomain (FractionRing K[X] ⊗[K] E) :=
  (rightScalarExtensionAlgEquiv K E (rationalPolynomialFractionEquiv K).symm).toMulEquiv.isDomain

/-- The fraction field of the constant tensor product is the rational function field over the enlarged constants. -/
def rationalConstantFractionEquiv :
    FractionRing (FractionRing K[X] ⊗[K] E) ≃ₐ[E] FractionRing E[X] :=
  (rightFractionScalarExtensionAlgEquiv K E (rationalPolynomialFractionEquiv K).symm).trans
    ((rationalFunctionConstantBaseChange K E PUnit.{1}).trans (rationalPolynomialFractionEquiv E))

/-- The fraction-field constant-extension equivalence preserves the rational coordinate. -/
theorem rationalConstantFractionEquiv_X :
    rationalConstantFractionEquiv K E
      (algebraMap (FractionRing K[X] ⊗[K] E)
        (FractionRing (FractionRing K[X] ⊗[K] E))
        ((algebraMap K[X] (FractionRing K[X]) X) ⊗ₜ[K] (1 : E))) =
      algebraMap E[X] (FractionRing E[X]) X := by
  rw [rationalConstantFractionEquiv, AlgEquiv.trans_apply,
    rightFractionScalarExtensionAlgEquiv_algebraMap, rightScalarExtensionAlgEquiv_tmul,
    ← rationalPolynomialFractionEquiv_X K, AlgEquiv.symm_apply_apply, AlgEquiv.trans_apply,
    rationalFunctionConstantBaseChange_X, rationalPolynomialFractionEquiv_X]

/-- A finite constant tensor product is a field: it is a finite-dimensional domain over the original rational function field. -/
@[implicit_reducible] def rationalConstantTensorField [FiniteDimensional K E] :
    Field (FractionRing K[X] ⊗[K] E) := by
  letI : FiniteDimensional (FractionRing K[X]) (FractionRing K[X] ⊗[K] E) := inferInstance
  letI : IsArtinianRing (FractionRing K[X] ⊗[K] E) :=
    isArtinian_of_tower (FractionRing K[X]) inferInstance
  exact IsField.toField (IsArtinianRing.isField_of_isDomain _)

/-- Finite extension in the right tensor factor gives the rational function field over the enlarged constants. -/
def rationalConstantRightTensorEquiv [FiniteDimensional K E] :
    (FractionRing K[X] ⊗[K] E) ≃ₐ[E] FractionRing E[X] := by
  letI := rationalConstantTensorField K E
  exact ((IsFractionRing.algEquiv (FractionRing K[X] ⊗[K] E)
    (FractionRing K[X] ⊗[K] E) (FractionRing (FractionRing K[X] ⊗[K] E))).restrictScalars E).trans
      (rationalConstantFractionEquiv K E)

/-- The raw tensor equivalence agrees with the corresponding fraction-field equivalence. -/
theorem rationalConstantRightTensorEquiv_apply [FiniteDimensional K E]
    (x : FractionRing K[X] ⊗[K] E) :
    rationalConstantRightTensorEquiv K E x = rationalConstantFractionEquiv K E
      (algebraMap (FractionRing K[X] ⊗[K] E) (FractionRing (FractionRing K[X] ⊗[K] E)) x) := rfl

/-- Finite constant extension identifies the literal scalar tensor product with the enlarged rational function field. -/
def rationalConstantTensorEquiv [FiniteDimensional K E] :
    (E ⊗[K] FractionRing K[X]) ≃ₐ[E] FractionRing E[X] :=
  (AlgEquiv.ofRingEquiv
    (f := (Algebra.TensorProduct.comm K E (FractionRing K[X])).toRingEquiv)
    (by intro a; rfl)).trans (rationalConstantRightTensorEquiv K E)

/-- The scalar tensor identification preserves the original rational coordinate. -/
theorem rationalConstantTensorEquiv_X [FiniteDimensional K E] :
    rationalConstantTensorEquiv K E ((1 : E) ⊗ₜ[K] algebraMap K[X] (FractionRing K[X]) X) =
      algebraMap E[X] (FractionRing E[X]) X := by
  change rationalConstantRightTensorEquiv K E ((algebraMap K[X] (FractionRing K[X]) X) ⊗ₜ[K] (1 : E)) = _
  rw [rationalConstantRightTensorEquiv_apply, rationalConstantFractionEquiv_X]

/-- The canonical inclusion of rational function fields obtained by finite constant extension. -/
def rationalConstantInclusion [FiniteDimensional K E] :
    FractionRing K[X] →ₐ[K] FractionRing E[X] :=
  ((rationalConstantTensorEquiv K E).toAlgHom.restrictScalars K).comp Algebra.TensorProduct.includeRight

/-- The constant-extension inclusion fixes the rational coordinate. -/
theorem rationalConstantInclusion_X [FiniteDimensional K E] :
    rationalConstantInclusion K E (algebraMap K[X] (FractionRing K[X]) X) =
      algebraMap E[X] (FractionRing E[X]) X := rationalConstantTensorEquiv_X K E

/-- The inclusion extends every polynomial coefficient through the given constant-field map. -/
theorem rationalConstantInclusion_polynomial [FiniteDimensional K E] (P : K[X]) :
    rationalConstantInclusion K E (algebraMap K[X] (FractionRing K[X]) P) =
      algebraMap E[X] (FractionRing E[X]) (P.map (algebraMap K E)) := by
  have heq :
      (rationalConstantInclusion K E).comp (IsScalarTower.toAlgHom K K[X] (FractionRing K[X])) =
        (IsScalarTower.toAlgHom K E[X] (FractionRing E[X])).comp
          (Polynomial.mapAlgHom (Algebra.ofId K E)) := by
    apply Polynomial.algHom_ext
    change rationalConstantInclusion K E (algebraMap K[X] (FractionRing K[X]) X) =
      algebraMap E[X] (FractionRing E[X]) (Polynomial.map (algebraMap K E) X)
    rw [Polynomial.map_X, rationalConstantInclusion_X]
  exact AlgHom.congr_fun heq P

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
