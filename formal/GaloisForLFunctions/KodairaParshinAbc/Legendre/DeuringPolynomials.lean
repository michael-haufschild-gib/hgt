import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# Binomial-square polynomials and the Deuring differential equation

The coefficient recurrence for `H_n = Σ binom(n,k)² X^k` gives its terminating Gauss
equation over every commutative ring. At `2n = -1` in odd characteristic this becomes
the Legendre Picard--Fuchs equation, without using a geometric Hasse-invariant premise.
-/

noncomputable section

namespace GaloisForLFunctions.KodairaParshinAbc.Legendre

open Polynomial

variable {R : Type*} [CommRing R]

/-- The integral binomial-square polynomial, interpreted in any coefficient ring. -/
def binomialSquare (n : ℕ) : R[X] :=
  ∑ k ∈ Finset.range (n + 1), monomial k ((n.choose k : R) ^ 2)

theorem coeff_binomialSquare (n k : ℕ) :
    (binomialSquare n : R[X]).coeff k = (n.choose k : R) ^ 2 := by
  by_cases hk : k < n + 1
  · simp [binomialSquare, coeff_monomial, hk]
  · have hnk : n < k := by omega
    simp [binomialSquare, coeff_monomial, hk, Nat.choose_eq_zero_of_lt hnk]

/-- Binomial-square polynomials commute with change of coefficient ring. -/
theorem map_binomialSquare {S : Type*} [CommRing S] (φ : R →+* S) (n : ℕ) :
    (binomialSquare n : R[X]).map φ = binomialSquare n := by
  ext k
  simp only [coeff_map, coeff_binomialSquare, map_pow, map_natCast]

theorem binomialSquare_natDegree [Nontrivial R] (n : ℕ) :
    (binomialSquare n : R[X]).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    simp only [coeff_binomialSquare, Nat.choose_eq_zero_of_lt hk, Nat.cast_zero, zero_pow
      (by omega : (2 : ℕ) ≠ 0)]
  · simp only [coeff_binomialSquare, Nat.choose_self, Nat.cast_one, one_pow, ne_eq,
      one_ne_zero, not_false_eq_true]

theorem binomialSquare_monic [Nontrivial R] (n : ℕ) :
    (binomialSquare n : R[X]).Monic := by
  change (binomialSquare n : R[X]).coeff (binomialSquare n).natDegree = 1
  rw [binomialSquare_natDegree, coeff_binomialSquare, Nat.choose_self, Nat.cast_one, one_pow]

theorem binomialSquare_eval_zero (n : ℕ) : (binomialSquare n : R[X]).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, coeff_binomialSquare, Nat.choose_zero_right,
    Nat.cast_one, one_pow]

/-- The other cusp value is the central binomial coefficient. -/
theorem binomialSquare_eval_one (n : ℕ) :
    (binomialSquare n : R[X]).eval 1 = ((2 * n).choose n : R) := by
  simpa only [binomialSquare, eval_finsetSum, eval_monomial, one_pow, mul_one,
    Nat.cast_sum, Nat.cast_pow] using
      congrArg (fun t : ℕ => (t : R)) (Nat.sum_range_choose_sq n)

private theorem choose_step (n k : ℕ) :
    ((k : R) + 1) * (n.choose (k + 1) : R) =
      ((n : R) - k) * (n.choose k : R) := by
  by_cases hk : k ≤ n
  · have h := congrArg (fun t : ℕ => (t : R)) (Nat.choose_succ_right_eq n k)
    push_cast [Nat.cast_sub hk] at h
    linear_combination h
  · have hnk : n < k := by omega
    rw [Nat.choose_eq_zero_of_lt hnk,
      Nat.choose_eq_zero_of_lt (hnk.trans (Nat.lt_succ_self k))]
    simp

/-- The coefficient recurrence includes the terminating coefficient and the zero tail. -/
theorem binomialSquare_coefficient_recurrence (n k : ℕ) :
    ((k : R) + 1) ^ 2 * (binomialSquare n : R[X]).coeff (k + 1) =
      ((n : R) - k) ^ 2 * (binomialSquare n : R[X]).coeff k := by
  rw [coeff_binomialSquare, coeff_binomialSquare, ← mul_pow, choose_step, mul_pow]

/-- The terminating Gauss equation is an integral polynomial identity. -/
theorem binomialSquare_gauss (n : ℕ) :
    X * (1 - X) * (binomialSquare n : R[X]).derivative.derivative +
      (1 + C (2 * (n : R) - 1) * X) * (binomialSquare n).derivative -
      C ((n : R) ^ 2) * binomialSquare n = 0 := by
  have hexpand : X * (1 - X) * (binomialSquare n : R[X]).derivative.derivative +
      (1 + C (2 * (n : R) - 1) * X) * (binomialSquare n).derivative -
      C ((n : R) ^ 2) * binomialSquare n =
      X * (binomialSquare n).derivative.derivative -
      X * (X * (binomialSquare n).derivative.derivative) +
      (binomialSquare n).derivative + C (2 * (n : R) - 1) *
      (X * (binomialSquare n).derivative) - C ((n : R) ^ 2) * binomialSquare n := by ring
  rw [hexpand]
  ext k
  rcases k with _ | (_ | k)
  · simp only [coeff_sub, coeff_add, coeff_X_mul_zero, coeff_C_mul, coeff_derivative,
      coeff_zero, Nat.cast_zero]
    linear_combination binomialSquare_coefficient_recurrence (R := R) n 0
  · simp only [coeff_sub, coeff_add, coeff_X_mul, coeff_X_mul_zero, coeff_C_mul,
      coeff_derivative, coeff_zero, Nat.cast_zero]
    linear_combination binomialSquare_coefficient_recurrence (R := R) n 1
  · simp only [coeff_sub, coeff_add, coeff_X_mul, coeff_C_mul, coeff_derivative,
      coeff_zero, Nat.cast_add, Nat.cast_one]
    have h := binomialSquare_coefficient_recurrence (R := R) n (k + 2)
    push_cast at h
    linear_combination h

/-- At characteristic `2n+1`, the terminating Gauss equation is the Legendre equation. -/
theorem binomialSquare_picardFuchs_of_char (n : ℕ) [CharP R (2 * n + 1)] :
    4 * X * (1 - X) * (binomialSquare n : R[X]).derivative.derivative +
      4 * (1 - 2 * X) * (binomialSquare n).derivative - binomialSquare n = 0 := by
  have hn : 2 * (n : R) + 1 = 0 := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      (CharP.cast_eq_zero R (2 * n + 1))
  have hl : 2 * (n : R) - 1 = -2 := by linear_combination hn
  have hq : 4 * (n : R) ^ 2 = 1 := by
    linear_combination (2 * (n : R) - 1) * hn
  have hlinear : C (2 * (n : R) - 1) = (-2 : R[X]) := by rw [hl, map_neg, map_ofNat]
  have hquad : 4 * C ((n : R) ^ 2) = (1 : R[X]) := by
    simpa only [map_mul, map_ofNat, map_one] using congrArg C hq
  have h := binomialSquare_gauss (R := R) n
  rw [hlinear] at h
  linear_combination 4 * h + (binomialSquare n : R[X]) * hquad

/-- The Legendre Picard--Fuchs identity holds modulo every odd modulus `2n+1`. -/
theorem binomialSquare_picardFuchs (n : ℕ) :
    4 * X * (1 - X) * (binomialSquare n : (ZMod (2 * n + 1))[X]).derivative.derivative +
      4 * (1 - 2 * X) * (binomialSquare n).derivative - binomialSquare n = 0 :=
  binomialSquare_picardFuchs_of_char n

/-- The weight-two Legendre differential operator on polynomials. -/
def legendreOperator (f : R[X]) : R[X] :=
  (1 - 2 * X) * f + 6 * X * (1 - X) * f.derivative

/-- Each numerator coefficient depends on exactly two adjacent period coefficients. -/
theorem coeff_legendreOperator_succ (f : R[X]) (k : ℕ) :
    (legendreOperator f).coeff (k + 1) =
      (6 * (k : R) + 7) * f.coeff (k + 1) - (6 * (k : R) + 2) * f.coeff k := by
  have he : legendreOperator f = f - 2 * (X * f) +
      6 * (X * f.derivative) - 6 * (X * (X * f.derivative)) := by
    unfold legendreOperator
    ring
  rw [he]
  cases k with
  | zero =>
    simp only [coeff_sub, coeff_add, coeff_ofNat_mul, coeff_X_mul, coeff_X_mul_zero,
      coeff_derivative, Nat.cast_zero]
    ring
  | succ k =>
    simp only [coeff_sub, coeff_add, coeff_ofNat_mul, coeff_X_mul, coeff_derivative,
      Nat.cast_add, Nat.cast_one]
    ring

/-- The top numerator coefficient is one even over a composite odd-modulus ring. -/
theorem binomialSquare_operator_top_coeff (n : ℕ) [CharP R (2 * n + 1)] :
    (legendreOperator (binomialSquare n : R[X])).coeff (n + 1) = 1 := by
  rw [coeff_legendreOperator_succ, coeff_binomialSquare, coeff_binomialSquare,
    Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n), Nat.choose_self,
    Nat.cast_zero, Nat.cast_one]
  have hn := CharP.cast_eq_zero R (2 * n + 1)
  push_cast at hn
  linear_combination -3 * hn

/-- The Deuring numerator has exact degree `n+1`. -/
theorem binomialSquare_operator_natDegree [Nontrivial R] (n : ℕ) [CharP R (2 * n + 1)] :
    (legendreOperator (binomialSquare n : R[X])).natDegree = n + 1 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    cases k with
    | zero => omega
    | succ k =>
      rw [coeff_legendreOperator_succ, coeff_binomialSquare, coeff_binomialSquare,
        Nat.choose_eq_zero_of_lt (by omega : n < k + 1),
        Nat.choose_eq_zero_of_lt (by omega : n < k), Nat.cast_zero]
      ring
  · rw [binomialSquare_operator_top_coeff]
    exact one_ne_zero

/-- The weight-two numerator is monic in its natural odd characteristic. -/
theorem binomialSquare_operator_monic [Nontrivial R] (n : ℕ) [CharP R (2 * n + 1)] :
    (legendreOperator (binomialSquare n : R[X])).Monic := by
  change (legendreOperator (binomialSquare n : R[X])).coeff
    (legendreOperator (binomialSquare n)).natDegree = 1
  rw [binomialSquare_operator_natDegree, binomialSquare_operator_top_coeff]

/-- The period equation reduces the numerator derivative to a first-order expression. -/
theorem binomialSquare_operator_derivative (n : ℕ) [CharP R (2 * n + 1)] :
    2 * (legendreOperator (binomialSquare n : R[X])).derivative =
      2 * (1 - 2 * X) * (binomialSquare n).derivative - binomialSquare n := by
  simp only [legendreOperator, derivative_add, derivative_mul, derivative_sub,
    derivative_one, derivative_ofNat, derivative_X]
  linear_combination 3 * (binomialSquare_picardFuchs_of_char (R := R) n)

/-- The second numerator derivative retains the two-state period system. -/
theorem binomialSquare_operator_secondDerivative (n : ℕ) [CharP R (2 * n + 1)] :
    2 * (legendreOperator (binomialSquare n : R[X])).derivative.derivative =
      2 * (1 - 2 * X) * (binomialSquare n).derivative.derivative -
        5 * (binomialSquare n).derivative := by
  have h := congrArg Polynomial.derivative (binomialSquare_operator_derivative (R := R) n)
  simp only [derivative_mul, derivative_sub, derivative_one, derivative_ofNat,
    derivative_X] at h
  linear_combination h

/-- The Riccati defect is exactly the linear Picard--Fuchs defect times `9 X(1-X) f`. -/
theorem legendreOperator_riccati_defect (f : R[X]) :
    6 * X * (1 - X) * ((legendreOperator f).derivative * f - legendreOperator f * f.derivative) +
      legendreOperator f ^ 2 - 2 * (1 - 2 * X) * legendreOperator f * f +
      (X ^ 2 - X + 1) * f ^ 2 =
    9 * X * (1 - X) * f *
      (4 * X * (1 - X) * f.derivative.derivative + 4 * (1 - 2 * X) * f.derivative - f) := by
  simp only [legendreOperator, derivative_add, derivative_sub, derivative_mul,
    derivative_one, derivative_X, derivative_ofNat]
  ring

/-- The finite-characteristic normalized numerator satisfies the denominator-free Riccati law. -/
theorem binomialSquare_riccati (n : ℕ) :
    6 * X * (1 - X) *
        ((legendreOperator (binomialSquare n : (ZMod (2 * n + 1))[X])).derivative * binomialSquare n -
          legendreOperator (binomialSquare n) * (binomialSquare n).derivative) =
      -(legendreOperator (binomialSquare n) ^ 2) +
        2 * (1 - 2 * X) * legendreOperator (binomialSquare n) * binomialSquare n -
        (X ^ 2 - X + 1) * binomialSquare n ^ 2 := by
  have h := legendreOperator_riccati_defect (binomialSquare n : (ZMod (2 * n + 1))[X])
  rw [binomialSquare_picardFuchs, mul_zero] at h
  linear_combination h

end GaloisForLFunctions.KodairaParshinAbc.Legendre
