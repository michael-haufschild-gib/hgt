import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.MaskedHeatIndex
import GaloisForLFunctions.HTGeometry.PolynomialHeatFactorBounds

/-!
# The full heat cone of a centrally masked adverse pair

All even coefficients of `exp(sD²)[X^(2m)(X²-a)²]` are retained. The monomial heat formula
connects their signs to the finite quadratic-index family, including the highest adverse order.
-/

open Polynomial
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry
noncomputable section

/-- The even coefficient of the heat of a monomial, with its exact vanishing range. -/
def evenHeatMonomialCoeff (s : ℝ) (r j : ℕ) : ℝ :=
  if j ≤ r then s ^ (r - j) / (r - j).factorial *
    ((2 * r).factorial / (2 * j).factorial : ℝ) else 0

theorem forwardPolyHeat_even_monomial_coeff (s : ℝ) (r j : ℕ) :
    (forwardPolyHeat s (X ^ (2 * r))).coeff (2 * j) = evenHeatMonomialCoeff s r j := by
  rw [forwardPolyHeat_eq_sum (N := r + 1) (by rw [natDegree_X_pow]; omega)]
  simp only [finsetSum_coeff, coeff_C_mul, coeff_iterate_derivative, nsmul_eq_mul,
    coeff_X_pow, descFactorial_two_mul_cast, mul_ite, mul_one, mul_zero]
  by_cases hj : j ≤ r
  · rw [evenHeatMonomialCoeff, if_pos hj, Finset.sum_eq_single (r - j)]
    · rw [if_pos (show 2 * j + 2 * (r - j) = 2 * r by omega),
        show 2 * j + 2 * (r - j) = 2 * r by omega]
    · intro k hk hne
      rw [if_neg (show ¬ 2 * j + 2 * k = 2 * r by omega)]
    · intro hn
      exact (hn (Finset.mem_range.mpr (by omega))).elim
  · rw [evenHeatMonomialCoeff, if_neg hj]
    apply Finset.sum_eq_zero
    intro k hk
    rw [if_neg (show ¬ 2 * j + 2 * k = 2 * r by omega)]

theorem forwardPolyHeat_even_monomial_coeff_odd (s : ℝ) (r j : ℕ) :
    (forwardPolyHeat s (X ^ (2 * r))).coeff (2 * j + 1) = 0 := by
  rw [forwardPolyHeat_eq_sum (N := r + 1) (by rw [natDegree_X_pow]; omega)]
  simp only [finsetSum_coeff, coeff_C_mul, coeff_iterate_derivative, nsmul_eq_mul, coeff_X_pow]
  apply Finset.sum_eq_zero
  intro k hk
  rw [if_neg (show ¬ 2 * j + 1 + 2 * k = 2 * r by omega)]
  ring

/-- An adverse pair at its ordinate, behind a central zero of multiplicity `m`. -/
def centralMaskedPair (a : ℝ) (m : ℕ) : ℝ[X] := X ^ (2 * m) * (X ^ 2 - C a) ^ 2

theorem centralMaskedPair_eq (a : ℝ) (m : ℕ) :
    centralMaskedPair a m = X ^ (2 * (m + 2)) + C (-2 * a) * X ^ (2 * (m + 1)) +
      C (a ^ 2) * X ^ (2 * m) := by
  simp only [centralMaskedPair, mul_add, pow_add, map_mul, map_neg, map_ofNat, map_pow]
  ring

theorem centralMaskedPair_heat_coeff_even (a s : ℝ) (m j : ℕ) :
    (forwardPolyHeat s (centralMaskedPair a m)).coeff (2 * j) =
      evenHeatMonomialCoeff s (m + 2) j - 2 * a * evenHeatMonomialCoeff s (m + 1) j +
        a ^ 2 * evenHeatMonomialCoeff s m j := by
  rw [centralMaskedPair_eq, forwardPolyHeat_add, forwardPolyHeat_add,
    forwardPolyHeat_C_mul, forwardPolyHeat_C_mul]
  simp only [coeff_add, coeff_C_mul, forwardPolyHeat_even_monomial_coeff]
  ring

theorem centralMaskedPair_heat_coeff_odd (a s : ℝ) (m j : ℕ) :
    (forwardPolyHeat s (centralMaskedPair a m)).coeff (2 * j + 1) = 0 := by
  rw [centralMaskedPair_eq, forwardPolyHeat_add, forwardPolyHeat_add,
    forwardPolyHeat_C_mul, forwardPolyHeat_C_mul]
  simp only [coeff_add, coeff_C_mul, forwardPolyHeat_even_monomial_coeff_odd, mul_zero, add_zero]

end
end GaloisForLFunctions.ArithmeticLocalDivisorGeometry
