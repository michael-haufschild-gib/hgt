import GaloisForLFunctions.HilbertMetric.QuantumInformation.ExteriorReflection
import Mathlib.Algebra.Polynomial.Derivative

/-!
# The differential and recurrence laws of exterior reflection traces

The exact reflection determinant polynomial satisfies a first-order
polynomial differential identity. Comparing coefficients gives the
three-term Krawtchouk recurrence for the actual exterior-sector traces.
-/

noncomputable section
open Polynomial Module
namespace GaloisForLFunctions.HilbertMetric.ExteriorReflection
open _root_.RHTower _root_.RHTower.ParityForecast

private theorem minus_weighted_derivative (s : ℕ) :
    (1 - X : Polynomial ℂ) * derivative ((1 - X : Polynomial ℂ) ^ s) =
      -C (s : ℂ) * (1 - X) ^ s := by
  cases s with
  | zero => simp
  | succ s =>
    rw [derivative_pow_succ]
    simp only [derivative_sub, derivative_one, derivative_X, zero_sub,
      Nat.cast_succ, pow_succ]
    ring

private theorem plus_weighted_derivative (s : ℕ) :
    (1 + X : Polynomial ℂ) * derivative ((1 + X : Polynomial ℂ) ^ s) =
      C (s : ℂ) * (1 + X) ^ s := by
  cases s with
  | zero => simp
  | succ s =>
    rw [derivative_pow_succ]
    simp only [derivative_add, derivative_one, derivative_X, zero_add,
      Nat.cast_succ, pow_succ]
    ring

private theorem multiplicityPolynomial_derivative (s t : ℕ) :
    (1 - X ^ 2 : Polynomial ℂ) * derivative ((1 - X) ^ s * (1 + X) ^ t) =
      (C ((t : ℂ) - (s : ℂ)) - C ((s : ℂ) + (t : ℂ)) * X) *
        ((1 - X) ^ s * (1 + X) ^ t) := by
  calc
    _ = ((1 - X) * derivative ((1 - X) ^ s)) * (1 + X) * (1 + X) ^ t +
        ((1 + X) * derivative ((1 + X) ^ t)) * (1 - X) * (1 - X) ^ s := by
      rw [derivative_mul]
      ring
    _ = _ := by
      rw [minus_weighted_derivative, plus_weighted_derivative, C_sub, C_add]
      ring

/-- The actual exterior-character polynomial solves the exact Krawtchouk differential identity. -/
theorem characterPolynomial_derivative {r : ℕ} (S : Finset (Fin r)) :
    (1 - X ^ 2 : Polynomial ℂ) * derivative (characterPolynomial S) =
      (C ((r : ℂ) - 2 * (S.card : ℂ)) - C (r : ℂ) * X) * characterPolynomial S := by
  simp_rw [characterPolynomial_eq]
  rw [multiplicityPolynomial_derivative]
  have hc : S.card ≤ r := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ S
  have hs : (S.card : ℂ) + ((r - S.card : ℕ) : ℂ) = (r : ℂ) := by
    exact_mod_cast Nat.add_sub_of_le hc
  have hd : ((r - S.card : ℕ) : ℂ) - (S.card : ℂ) = (r : ℂ) - 2 * (S.card : ℂ) := by
    linear_combination hs
  rw [hs, hd]

private theorem character_coefficient_recurrence {r : ℕ} (S : Finset (Fin r)) (j : ℕ) :
    (j + 2 : ℂ) * (characterPolynomial S).coeff (j + 2) =
      ((r : ℂ) - 2 * (S.card : ℂ)) * (characterPolynomial S).coeff (j + 1) -
        ((r : ℂ) - (j : ℂ)) * (characterPolynomial S).coeff j := by
  have h := congrArg (fun P : Polynomial ℂ => P.coeff (j + 1))
    (characterPolynomial_derivative S)
  simp only [sub_mul, one_mul, mul_assoc, coeff_sub, coeff_C_mul,
    coeff_X_mul, coeff_derivative] at h
  cases j with
  | zero =>
    simp only [Nat.cast_zero, zero_add, sub_zero] at h ⊢
    have hz : (X ^ 2 * derivative (characterPolynomial S)).coeff 1 = 0 := by
      rw [coeff_X_pow_mul']
      norm_num
    rw [hz] at h
    linear_combination h
  | succ j =>
    have hx : (X ^ 2 * derivative (characterPolynomial S)).coeff (j + 1 + 1) =
        (characterPolynomial S).coeff (j + 1) * (j + 1 : ℂ) := by
      rw [coeff_X_pow_mul']
      rw [if_pos (by omega : 2 ≤ j + 1 + 1)]
      rw [show j + 1 + 1 - 2 = j by omega, coeff_derivative]
    rw [hx] at h
    simp only [Nat.cast_succ] at h ⊢
    linear_combination h

/-- Successive actual exterior traces obey the exact three-term Krawtchouk recurrence. -/
theorem exterior_signOperator_trace_recurrence {r : ℕ} (S : Finset (Fin r)) (j : ℕ) :
    (j + 2 : ℂ) *
      LinearMap.trace ℂ (⋀[ℂ]^(j + 2) (FiniteIndexClockSpace (Fin r)))
        (exteriorPower.map (j + 2) (signOperator S)) =
      ((r : ℂ) - 2 * (S.card : ℂ)) *
        LinearMap.trace ℂ (⋀[ℂ]^(j + 1) (FiniteIndexClockSpace (Fin r)))
          (exteriorPower.map (j + 1) (signOperator S)) -
      ((r : ℂ) - (j : ℂ)) *
        LinearMap.trace ℂ (⋀[ℂ]^j (FiniteIndexClockSpace (Fin r)))
          (exteriorPower.map j (signOperator S)) := by
  simp_rw [exterior_signOperator_trace_eq_coeff]
  exact character_coefficient_recurrence S j

#print axioms characterPolynomial_derivative
#print axioms exterior_signOperator_trace_recurrence
end GaloisForLFunctions.HilbertMetric.ExteriorReflection
