import GaloisForLFunctions.HTGeometry.DifferentialPolynomialOver

/-!
# The total derivation of a multivariate polynomial ring over a differential ring

Differentiating the coefficients is a derivation, and adding to it the derivation with prescribed
values on the variables gives the general derivation of a polynomial ring extending the derivation
of the coefficients.  This is the index-free form of the jet derivation used for differential
polynomials, and it is what turns a linear differential system into a differential coordinate ring:
prescribing `δX_{ij} = ∑ₖ A_{ik} X_{kj}` makes the generic matrix a solution.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable (σ R : Type*) [CommRing R] [Differential R]

/-- Differentiating the coefficients of a multivariate polynomial. -/
def mvCoeffLinear : MvPolynomial σ R →ₗ[ℤ] MvPolynomial σ R :=
  (AddMonoidAlgebra.coeffLinearEquiv ℤ).symm.toLinearMap.comp <|
    (Finsupp.mapRange.linearMap Differential.deriv.toLinearMap).comp <|
      (AddMonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

@[simp] theorem mvCoeffLinear_monomial (s : σ →₀ ℕ) (a : R) :
    mvCoeffLinear σ R (MvPolynomial.monomial s a) = MvPolynomial.monomial s (Differential.deriv a) := by
  simp [mvCoeffLinear, MvPolynomial.monomial]

/-- The coefficientwise derivation of a multivariate polynomial ring over a differential ring. -/
def mvCoeffDerivation : Derivation ℤ (MvPolynomial σ R) (MvPolynomial σ R) where
  toLinearMap := mvCoeffLinear σ R
  map_one_eq_zero' := by
    rw [MvPolynomial.one_def, mvCoeffLinear_monomial]
    simp
  leibniz' P Q := by
    induction P using MvPolynomial.induction_on' with
    | add P₁ P₂ hP₁ hP₂ =>
        simp only [add_mul, map_add, add_smul, smul_add, hP₁, hP₂]
        abel
    | monomial s a =>
        induction Q using MvPolynomial.induction_on' with
        | add Q₁ Q₂ hQ₁ hQ₂ =>
            simp only [mul_add, map_add, add_smul, smul_add, hQ₁, hQ₂]
            abel
        | monomial t b =>
            rw [MvPolynomial.monomial_mul]
            change mvCoeffLinear σ R (MvPolynomial.monomial (s + t) (a * b)) = _
            have ht := mvCoeffLinear_monomial σ R t b
            have hs := mvCoeffLinear_monomial σ R s a
            calc mvCoeffLinear σ R (MvPolynomial.monomial (s + t) (a * b))
                = MvPolynomial.monomial (s + t) (Differential.deriv (a * b)) :=
                  mvCoeffLinear_monomial _ _ _ _
              _ = MvPolynomial.monomial (s + t) (a * Differential.deriv b) +
                  MvPolynomial.monomial (s + t) (b * Differential.deriv a) := by
                rw [Derivation.leibniz, map_add]
                simp only [smul_eq_mul]
              _ = MvPolynomial.monomial s a * MvPolynomial.monomial t (Differential.deriv b) +
                  MvPolynomial.monomial t b * MvPolynomial.monomial s (Differential.deriv a) := by
                rw [MvPolynomial.monomial_mul, MvPolynomial.monomial_mul, add_comm t s]
              _ = MvPolynomial.monomial s a * mvCoeffLinear σ R (MvPolynomial.monomial t b) +
                  MvPolynomial.monomial t b * mvCoeffLinear σ R (MvPolynomial.monomial s a) := by
                exact congrArg₂ (· + ·)
                  (congrArg (MvPolynomial.monomial s a * ·) ht.symm)
                  (congrArg (MvPolynomial.monomial t b * ·) hs.symm)

@[simp] theorem mvCoeffDerivation_C (a : R) :
    mvCoeffDerivation σ R (MvPolynomial.C a) = MvPolynomial.C (Differential.deriv a) := by
  rw [MvPolynomial.C_apply]
  exact mvCoeffLinear_monomial σ R 0 a

@[simp] theorem mvCoeffDerivation_X (i : σ) :
    mvCoeffDerivation σ R (MvPolynomial.X i) = 0 := by
  rw [MvPolynomial.X]
  simp [mvCoeffDerivation]

variable {σ R}

/-- The total derivation of a multivariate polynomial ring: differentiate the coefficients and give
the variables prescribed derivatives. -/
def mvTotalDerivation (f : σ → MvPolynomial σ R) :
    Derivation ℤ (MvPolynomial σ R) (MvPolynomial σ R) :=
  mvCoeffDerivation σ R + (MvPolynomial.mkDerivation R f).restrictScalars ℤ

@[simp] theorem mvTotalDerivation_C (f : σ → MvPolynomial σ R) (a : R) :
    mvTotalDerivation f (MvPolynomial.C a) = MvPolynomial.C (Differential.deriv a) := by
  simp [mvTotalDerivation]

@[simp] theorem mvTotalDerivation_X (f : σ → MvPolynomial σ R) (i : σ) :
    mvTotalDerivation f (MvPolynomial.X i) = f i := by
  simp [mvTotalDerivation]

end

end GaloisForLFunctions.HTGeometry
