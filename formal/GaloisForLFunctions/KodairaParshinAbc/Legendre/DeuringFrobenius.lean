import GaloisForLFunctions.KodairaParshinAbc.Legendre.DeuringPolynomials
import GaloisForLFunctions.HTGeometry.Polynomial.FrobeniusResidues
import Mathlib.Data.Nat.Choose.Lucas

/-!
# Frobenius digit factorization of binomial-square polynomials

Lucas's congruence gives `H_n(X) = H_(n mod p)(X) H_(n/p)(X^p)` over `𝔽_p`.
Differentiation kills the second factor, so the weight-two numerator has exactly the
same high-digit factor. This isolates the new numerator from inherited Frobenius zeros.
-/

noncomputable section

namespace GaloisForLFunctions.KodairaParshinAbc.Legendre

open Polynomial

/-- Squared-binomial coefficients split into their low digit and remaining digits. -/
theorem binomialSquare_lucas_coeff (p n k : ℕ) [Fact p.Prime] :
    (binomialSquare n : (ZMod p)[X]).coeff k =
      (binomialSquare (n % p) : (ZMod p)[X]).coeff (k % p) *
        (binomialSquare (n / p) : (ZMod p)[X]).coeff (k / p) := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div (n := n) (k := k) (p := p)
  rw [← ZMod.intCast_eq_intCast_iff] at h
  have hc : (n.choose k : ZMod p) =
      ((n % p).choose (k % p) : ZMod p) * ((n / p).choose (k / p) : ZMod p) := by
    simpa only [Int.cast_natCast, Int.cast_mul] using h
  rw [coeff_binomialSquare, coeff_binomialSquare, coeff_binomialSquare, hc, mul_pow]

/-- The complete binomial-square polynomial has an exact Frobenius digit factorization. -/
theorem binomialSquare_frobenius_factor (p n : ℕ) [Fact p.Prime] :
    (binomialSquare n : (ZMod p)[X]) =
      binomialSquare (n % p) * Polynomial.expand (ZMod p) p (binomialSquare (n / p)) := by
  ext k
  rw [coeff_mul_expand_of_natDegree_lt (Fact.out : p.Prime).pos _ _
    (by rw [binomialSquare_natDegree]; exact Nat.mod_lt n (Fact.out : p.Prime).pos),
    binomialSquare_lucas_coeff]

/-- The Legendre differential operator retains a Frobenius-expanded factor unchanged. -/
theorem legendreOperator_mul_expand {R : Type*} [CommRing R]
    (p : ℕ) [CharP R p] (f g : R[X]) :
    legendreOperator (f * Polynomial.expand R p g) =
      Polynomial.expand R p g * legendreOperator f := by
  simp only [legendreOperator, derivative_mul, derivative_expand,
    CharP.cast_eq_zero, zero_mul, mul_zero, add_zero]
  ring

/-- The high-digit factor is shared by the period polynomial and its weight-two numerator. -/
theorem binomialSquare_operator_frobenius_factor (p n : ℕ) [Fact p.Prime] :
    legendreOperator (binomialSquare n : (ZMod p)[X]) =
      Polynomial.expand (ZMod p) p (binomialSquare (n / p)) *
        legendreOperator (binomialSquare (n % p)) := by
  conv_lhs => rw [binomialSquare_frobenius_factor p n]
  exact legendreOperator_mul_expand p _ _

end GaloisForLFunctions.KodairaParshinAbc.Legendre
