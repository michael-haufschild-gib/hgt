import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FrobeniusTracePolynomials
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic.Linarith

/-!
# Two-term Frobenius differences

A nonzero linear coefficient forces a chain of nonzero coefficients at
successive Frobenius powers. The chain can terminate only at the other
nonconstant term. Thus a polynomial whose Frobenius difference has just
these two terms forces divisibility of the Frobenius periods.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Polynomial
variable (p : ℕ) [Fact p.Prime] {K : Type*} [CommRing K] [CharP K p]

private theorem frobenius_coefficient_mul (P : K[X]) (r j : ℕ) :
    (P ^ p ^ r).coeff (p ^ r * j) = (P.coeff j) ^ p ^ r := by
  rw [← map_iterateFrobenius_expand p, coeff_map,
    coeff_expand_mul' (pow_pos (Fact.out : p.Prime).pos r)]
  rfl

private theorem frobenius_coefficient_one (P : K[X]) (r : ℕ) :
    (P ^ p ^ (r + 1)).coeff 1 = 0 := by
  have hp : 1 < p ^ (r + 1) := Nat.one_lt_pow (Nat.succ_ne_zero r)
    (Fact.out : p.Prime).one_lt
  have hn : ¬ p ^ (r + 1) ∣ 1 := by
    intro h
    have := Nat.le_of_dvd (by omega : 0 < 1) h
    omega
  rw [← map_iterateFrobenius_expand p, coeff_map,
    coeff_expand (pow_pos (Fact.out : p.Prime).pos (r + 1)), if_neg hn, map_zero]

variable [IsDomain K]

/-- A two-term polynomial Frobenius difference with nonzero linear term
forces divisibility of its two Frobenius periods. -/
theorem polynomial_frobenius_two_term_dvd (r n : ℕ) (P : K[X]) (a b c : K)
    (hb : b ≠ 0)
    (hP : P ^ p ^ (r + 1) - P = C a * X ^ p ^ n + C b * X + C c) :
    r + 1 ∣ n := by
  by_contra hdiv
  have hn : n ≠ 0 := by
    intro h
    apply hdiv
    rw [h]
    exact dvd_zero _
  have hpn : 1 < p ^ n := Nat.one_lt_pow hn (Fact.out : p.Prime).one_lt
  have hbase : P.coeff 1 ≠ 0 := by
    have h := congrArg (fun F : K[X] => F.coeff 1) hP
    simp only [coeff_sub, frobenius_coefficient_one, coeff_add, coeff_C_mul,
      coeff_X_pow, if_neg (ne_of_lt hpn), mul_zero, coeff_X_one, mul_one,
      zero_add, coeff_C, one_ne_zero, if_false, add_zero] at h
    intro hz
    rw [hz, sub_self] at h
    exact hb h.symm
  have hchain (j : ℕ) : P.coeff (p ^ ((r + 1) * j)) ≠ 0 := by
    induction j with
    | zero => simpa only [Nat.mul_zero, pow_zero] using hbase
    | succ j ih =>
      have hneq : (r + 1) * (j + 1) ≠ n := by
        intro h
        exact hdiv ⟨j + 1, h.symm⟩
      have hexp : p ^ ((r + 1) * (j + 1)) ≠ p ^ n := by
        rcases lt_or_gt_of_ne hneq with hlt | hgt
        · exact ne_of_lt (Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt hlt)
        · exact ne_of_gt (Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt hgt)
      have hpos : 1 < p ^ ((r + 1) * (j + 1)) := Nat.one_lt_pow
        (Nat.mul_ne_zero (Nat.succ_ne_zero r) (Nat.succ_ne_zero j))
        (Fact.out : p.Prime).one_lt
      have h := congrArg (fun F : K[X] => F.coeff (p ^ ((r + 1) * (j + 1)))) hP
      simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, if_neg hexp,
        coeff_X, if_neg (Ne.symm (ne_of_gt hpos)), coeff_C,
        if_neg (ne_of_gt (lt_trans Nat.zero_lt_one hpos)), mul_zero, add_zero] at h
      have he : p ^ ((r + 1) * (j + 1)) = p ^ (r + 1) * p ^ ((r + 1) * j) := by
        rw [Nat.mul_succ, pow_add, Nat.mul_comm]
      have hF : (P ^ p ^ (r + 1)).coeff (p ^ ((r + 1) * (j + 1))) =
          (P.coeff (p ^ ((r + 1) * j))) ^ p ^ (r + 1) := by
        rw [he, frobenius_coefficient_mul]
      rw [hF] at h
      intro hz
      rw [hz, sub_zero] at h
      exact pow_ne_zero _ ih h
  have hgrowth (j : ℕ) : j + 1 ≤ p ^ ((r + 1) * j) := by
    induction j with
    | zero => simp only [Nat.mul_zero, pow_zero, Nat.zero_add, le_refl]
    | succ j ih =>
      have hp : 2 ≤ p ^ (r + 1) := Nat.one_lt_pow (Nat.succ_ne_zero r)
        (Fact.out : p.Prime).one_lt
      rw [Nat.mul_succ, pow_add]
      nlinarith [Nat.mul_le_mul ih hp]
  have hdeg := le_natDegree_of_ne_zero (hchain (P.natDegree + 1))
  have hg := hgrowth (P.natDegree + 1)
  omega

/-- A pure Frobenius difference admits a polynomial primitive exactly when
its period is a multiple of the prescribed shorter period. -/
theorem exists_polynomial_frobenius_difference_iff (r n : ℕ) :
    (∃ P : K[X], P ^ p ^ (r + 1) - P = X ^ p ^ n - X) ↔ r + 1 ∣ n := by
  constructor
  · rintro ⟨P, hP⟩
    exact polynomial_frobenius_two_term_dvd p r n P 1 (-1) 0 (neg_ne_zero.mpr one_ne_zero)
      (by simpa only [map_one, one_mul, map_neg, neg_mul, map_zero, add_zero,
        sub_eq_add_neg] using hP)
  · rintro ⟨m, rfl⟩
    refine ⟨frobeniusTraceSum p (r + 1) m X, ?_⟩
    have h := frobeniusTraceSum_sub_pow p (r + 1) m (X : K[X])
    linear_combination -h

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
