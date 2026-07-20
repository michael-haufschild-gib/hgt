import GaloisForLFunctions.HTGeometry.GammaPoleMovingCoefficientLaurent
import GaloisForLFunctions.HTGeometry.SimplePoleJetLatticeHorizon

/-!
# Gamma moving-pole jet Laurent evaluation

This file joins two previously separate value interfaces:

* polynomial coefficients are shifted to the moving Gamma pole and expanded in
  the physical factorial scale;
* the universal simple-pole jet profiles are evaluated on the actual Taylor
  derivatives of the regular Gamma unit.

The resulting ring homomorphism is an exact `ℂ[z]`-coefficient interface for
finite differential-polynomial expressions in Gamma jets.  It supplies the
composition law needed before a maximal-weight Laurent extraction; it does not
assert the final meromorphic-order intersection theorem.
-/

open Polynomial LaurentPolynomial MvPolynomial

namespace GaloisForLFunctions

noncomputable section

/-- The actual derivative boundary of the regular Gamma unit, with constant
term normalized to one. -/
def gammaPoleUnitDerivativeBoundaryFamily : ℕ → NatGerm
  | 0 => 1
  | k + 1 => gammaPoleUnitPositiveDerivativeRationalGerm k

/-- Evaluation of universal regular-unit jet polynomials on the actual Gamma
boundary derivatives. -/
def gammaPoleUnitDerivativeBoundaryEval :
    MvPolynomial ℕ ℂ →+* NatGerm :=
  MvPolynomial.eval₂Hom complexNatGerm
    gammaPoleUnitDerivativeBoundaryFamily

/-- Laurent profile of the `j`-th Gamma derivative at the moving pole. -/
def gammaPoleDerivativeLaurentProfile (j : ℕ) : NatGerm[T;T⁻¹] :=
  LaurentPolynomial.C (-gammaPolePhysicalScaleGerm⁻¹ ^ j) *
    Polynomial.toLaurent
      ((HTGeometry.universalSimplePoleJetProfile j).map
        gammaPoleUnitDerivativeBoundaryEval)

theorem gammaPoleDerivativeLaurentProfile_zero :
    gammaPoleDerivativeLaurentProfile 0 =
      LaurentPolynomial.C (-1 : NatGerm) * LaurentPolynomial.T 1 := by
  simp [gammaPoleDerivativeLaurentProfile,
    HTGeometry.universalSimplePoleJetProfile,
    HTGeometry.universalSimplePoleRegularProfile,
    gammaPoleUnitDerivativeBoundaryEval,
    gammaPoleUnitDerivativeBoundaryFamily]

/-- Simultaneous moving-pole Laurent evaluation of a polynomial-coefficient
jet expression. -/
def gammaPolePolynomialJetLaurentEval (n : ℕ) :
    MvPolynomial (Fin (n + 1)) (Polynomial ℂ) →+* NatGerm[T;T⁻¹] :=
  MvPolynomial.eval₂Hom gammaPoleMovingCoefficientLaurent fun j =>
    gammaPoleDerivativeLaurentProfile (j : ℕ)

@[simp] theorem gammaPolePolynomialJetLaurentEval_C
    (n : ℕ) (p : Polynomial ℂ) :
    gammaPolePolynomialJetLaurentEval n (MvPolynomial.C p) =
      gammaPoleMovingCoefficientLaurent p := by
  simp [gammaPolePolynomialJetLaurentEval]

@[simp] theorem gammaPolePolynomialJetLaurentEval_X
    (n : ℕ) (j : Fin (n + 1)) :
    gammaPolePolynomialJetLaurentEval n (MvPolynomial.X j) =
      gammaPoleDerivativeLaurentProfile (j : ℕ) := by
  simp [gammaPolePolynomialJetLaurentEval]

theorem gammaPolePolynomialJetLaurentEval_monomial
    (n : ℕ) (d : Fin (n + 1) →₀ ℕ) (p : Polynomial ℂ) :
    gammaPolePolynomialJetLaurentEval n (MvPolynomial.monomial d p) =
      gammaPoleMovingCoefficientLaurent p *
        d.prod fun j e => gammaPoleDerivativeLaurentProfile (j : ℕ) ^ e := by
  simp [gammaPolePolynomialJetLaurentEval, MvPolynomial.eval₂_monomial]

/-- Exact coefficient reflection for the polynomial-coefficient subring. -/
theorem gammaPolePolynomialJetLaurentEval_C_coeff_neg
    (n b : ℕ) (p : Polynomial ℂ) :
    gammaPolePolynomialJetLaurentEval n (MvPolynomial.C p) (-(b : ℤ)) =
      ratNatEval (gammaPoleCenterHasseRational p b) *
        gammaPolePhysicalScaleGerm ^ b := by
  rw [gammaPolePolynomialJetLaurentEval_C,
    gammaPoleMovingCoefficientLaurent_coeff_neg]

end

end GaloisForLFunctions
