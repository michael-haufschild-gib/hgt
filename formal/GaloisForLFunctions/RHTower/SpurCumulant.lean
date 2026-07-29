/-
Finite cumulant/exponential truncation infrastructure for the MWM spur multiplier.

`SpurRescale` proves analytic inequalities for

    φ_d(j) = ∏_{i<j} (1 - i/d).

This file packages the algebraic side of doc 34 Lemma R/R1: the logarithmic cumulant
truncation as a polynomial in `T = 1/d`, the formal truncation of `exp (-x)`, and the
composite multiplier polynomial whose coefficients are the finite-order `e_p(j)`.
-/
import GaloisForLFunctions.RHTower.PolynomialTruncation
import GaloisForLFunctions.RHTower.SpurRescale

namespace RHTower

open Polynomial

noncomputable section

/-- Positive logarithmic cumulant truncation in the formal variable `T = 1 / d`.

The signed logarithmic approximation to `φ_d(j)` is `-cumulantLogPoly n j` evaluated
at `T = 1/d`. -/
def cumulantLogPoly (n j : ℕ) : ℝ[X] :=
  ∑ l ∈ Finset.range n,
    Polynomial.C (rescalePowerSum (l + 1) j / (l + 1 : ℝ)) * Polynomial.X ^ (l + 1)

/-- Exponential truncation for `exp (-x)`, through powers `< P`. -/
def expNegTruncPoly (P : ℕ) : ℝ[X] :=
  ∑ p ∈ Finset.range P,
    Polynomial.C (((-1 : ℝ) ^ p) / (p.factorial : ℝ)) * Polynomial.X ^ p

/-- R1's finite multiplier polynomial: the formal truncation of
`exp (-(positive cumulants))`. -/
def multiplierTruncPoly (P n j : ℕ) : ℝ[X] :=
  (expNegTruncPoly P).comp (cumulantLogPoly n j)

/-- Coefficient notation for the finite multiplier expansion.  These are the `e_p(j)`
coefficients from doc 34 R1, after choosing truncation orders `P` and `n`. -/
def multiplierCoeff (P n j p : ℕ) : ℝ :=
  (multiplierTruncPoly P n j).coeff p

/-- The low-degree jet of the finite multiplier polynomial, retaining terms `< P`.

Doc 34's `Σ_{p<P} e_p(j)/d^p` is the evaluation of this polynomial at `T = 1/d`.
The discarded tail is exactly divisible by `T^P`; see
`X_pow_dvd_multiplierTruncPoly_sub_jet`. -/
def multiplierJetPoly (P n j : ℕ) : ℝ[X] :=
  PolynomialTruncation.lowTrunc (multiplierTruncPoly P n j) P

/-- Evaluate the positive logarithmic cumulant polynomial. -/
theorem eval_cumulantLogPoly (n j : ℕ) (t : ℝ) :
    (cumulantLogPoly n j).eval t =
      ∑ l ∈ Finset.range n,
        (rescalePowerSum (l + 1) j / (l + 1 : ℝ)) * t ^ (l + 1) := by
  rw [cumulantLogPoly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- Coefficients of the logarithmic cumulant polynomial. -/
theorem coeff_cumulantLogPoly (n j k : ℕ) :
    (cumulantLogPoly n j).coeff k =
      if 0 < k ∧ k ≤ n then rescalePowerSum k j / (k : ℝ) else 0 := by
  rw [cumulantLogPoly, Polynomial.finsetSum_coeff]
  by_cases hk0 : k = 0
  · subst k
    simp
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    by_cases hkn : k ≤ n
    · simp only [hkpos, hkn, and_self, if_true]
      rw [Finset.sum_eq_single (k - 1)]
      · have hks : k - 1 + 1 = k := Nat.sub_one_add_one hk0
        have hkcast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by exact_mod_cast hks
        rw [hks, hkcast]
        rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
      · intro l _hl hlne
        have hneq : k ≠ l + 1 := by
          intro heq
          have : l = k - 1 := by omega
          exact hlne this
        simp [hneq]
      · intro hmem
        exfalso
        exact hmem (Finset.mem_range.mpr (by omega))
    · simp only [hkpos, true_and, hkn, if_false]
      apply Finset.sum_eq_zero
      intro l hl
      have hneq : k ≠ l + 1 := by
        intro heq
        have lk : l + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hl)
        omega
      simp [hneq]

/-- Coarse coefficient growth for the logarithmic cumulant polynomial. -/
theorem abs_coeff_cumulantLogPoly_le_pow_succ (n j k : ℕ) :
    |(cumulantLogPoly n j).coeff k| ≤ (j : ℝ) ^ (k + 1) := by
  rw [coeff_cumulantLogPoly]
  by_cases h : 0 < k ∧ k ≤ n
  · rw [if_pos h]
    have hsum := sum_range_pow_cast_le_pow_succ k j
    have hkRpos : 0 < (k : ℝ) := by exact_mod_cast h.1
    have hdiv : rescalePowerSum k j / (k : ℝ) ≤ (j : ℝ) ^ (k + 1) / (k : ℝ) :=
      div_le_div_of_nonneg_right hsum (le_of_lt hkRpos)
    have hdiv_le : (j : ℝ) ^ (k + 1) / (k : ℝ) ≤ (j : ℝ) ^ (k + 1) := by
      have hkRge : (1 : ℝ) ≤ k := by exact_mod_cast h.1
      exact div_le_self (by positivity) hkRge
    have hnum_nonneg : 0 ≤ rescalePowerSum k j := by
      rw [rescalePowerSum]
      exact Finset.sum_nonneg (fun _ _ => by positivity)
    have hnonneg : 0 ≤ rescalePowerSum k j / (k : ℝ) :=
      div_nonneg hnum_nonneg (le_of_lt hkRpos)
    rw [abs_of_nonneg hnonneg]
    exact le_trans hdiv hdiv_le
  · rw [if_neg h]
    simp

/-- Evaluate the exponential truncation polynomial. -/
theorem eval_expNegTruncPoly (P : ℕ) (x : ℝ) :
    (expNegTruncPoly P).eval x =
      ∑ p ∈ Finset.range P, (((-1 : ℝ) ^ p) / (p.factorial : ℝ)) * x ^ p := by
  rw [expNegTruncPoly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- Evaluate the finite multiplier polynomial as a composed truncation. -/
theorem eval_multiplierTruncPoly (P n j : ℕ) (t : ℝ) :
    (multiplierTruncPoly P n j).eval t =
      (expNegTruncPoly P).eval ((cumulantLogPoly n j).eval t) := by
  rw [multiplierTruncPoly, Polynomial.eval_comp]

/-- Fully expanded finite-sum form of the multiplier truncation. -/
theorem eval_multiplierTruncPoly_expanded (P n j : ℕ) (t : ℝ) :
    (multiplierTruncPoly P n j).eval t =
      ∑ p ∈ Finset.range P,
        (((-1 : ℝ) ^ p) / (p.factorial : ℝ)) *
          ((∑ l ∈ Finset.range n,
            (rescalePowerSum (l + 1) j / (l + 1 : ℝ)) * t ^ (l + 1)) ^ p) := by
  rw [eval_multiplierTruncPoly, eval_expNegTruncPoly, eval_cumulantLogPoly]

/-- Coefficients of the finite multiplier polynomial expanded by exponential
truncation order. -/
theorem coeff_multiplierTruncPoly_expansion (P n j k : ℕ) :
    multiplierCoeff P n j k =
      ∑ q ∈ Finset.range P,
        (((-1 : ℝ) ^ q) / (q.factorial : ℝ)) * ((cumulantLogPoly n j) ^ q).coeff k := by
  rw [multiplierCoeff, multiplierTruncPoly, expNegTruncPoly]
  rw [Polynomial.sum_comp]
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl (fun _ _ => ?_)
  rw [Polynomial.C_mul_comp, Polynomial.X_pow_comp, Polynomial.coeff_C_mul]

/-- Triangle-inequality form of `coeff_multiplierTruncPoly_expansion`.

This is the first sharpening of the R1 high-coefficient provider: it replaces
opaque `multiplierCoeff` bounds by bounds for powers of the cumulant polynomial. -/
theorem abs_multiplierCoeff_le_cumulant_power_coeff_sum (P n j k : ℕ) :
    |multiplierCoeff P n j k| ≤
      ∑ q ∈ Finset.range P,
        (1 / (q.factorial : ℝ)) * |((cumulantLogPoly n j) ^ q).coeff k| := by
  rw [coeff_multiplierTruncPoly_expansion]
  calc
    |∑ q ∈ Finset.range P,
        (((-1 : ℝ) ^ q) / (q.factorial : ℝ)) * ((cumulantLogPoly n j) ^ q).coeff k|
        ≤ ∑ q ∈ Finset.range P,
            |(((-1 : ℝ) ^ q) / (q.factorial : ℝ)) *
              ((cumulantLogPoly n j) ^ q).coeff k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ q ∈ Finset.range P,
        (1 / (q.factorial : ℝ)) * |((cumulantLogPoly n j) ^ q).coeff k| := by
      apply Finset.sum_congr rfl
      intro q _
      rw [abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, one_div]
      have hfac_nonneg : 0 ≤ ((q.factorial : ℕ) : ℝ) := by positivity
      rw [abs_of_nonneg hfac_nonneg]
      ring

/-- Coarse coefficient growth for powers of the logarithmic cumulant polynomial.

The factor `(m+1)^q` is the number-of-Cauchy-products cost from repeatedly
using the antidiagonal coefficient formula.  The exponent `m+q` is the important
part for R1: after setting `m = P+r`, the range arithmetic absorbs
`j^(P+r+q) |1/d|^r` into `j^(2P)`. -/
theorem abs_coeff_cumulantLogPoly_pow_le (n j q m : ℕ) :
    |((cumulantLogPoly n j) ^ q).coeff m| ≤
      ((m + 1 : ℕ) : ℝ) ^ q * (j : ℝ) ^ (m + q) := by
  induction q generalizing m with
  | zero =>
      by_cases hm : m = 0
      · subst m
        simp
      · rw [pow_zero]
        simp [Polynomial.coeff_one, hm]
  | succ q ih =>
      rw [pow_succ]
      rw [Polynomial.coeff_mul]
      calc
        |∑ x ∈ Finset.HasAntidiagonal.antidiagonal m,
            ((cumulantLogPoly n j) ^ q).coeff x.1 * (cumulantLogPoly n j).coeff x.2|
            ≤ ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m,
                |((cumulantLogPoly n j) ^ q).coeff x.1 *
                  (cumulantLogPoly n j).coeff x.2| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _x ∈ Finset.HasAntidiagonal.antidiagonal m,
              (((m + 1 : ℕ) : ℝ) ^ q * (j : ℝ) ^ (m + q + 1)) := by
              apply Finset.sum_le_sum
              intro x hx
              have hxsum : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
              have hx1le : x.1 + 1 ≤ m + 1 := by omega
              have hx1leR : ((x.1 + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
                exact_mod_cast hx1le
              have hpow_x1 : ((x.1 + 1 : ℕ) : ℝ) ^ q ≤ ((m + 1 : ℕ) : ℝ) ^ q :=
                pow_le_pow_left₀ (by positivity) hx1leR q
              have hcoeff1 := ih x.1
              have hcoeff2 := abs_coeff_cumulantLogPoly_le_pow_succ n j x.2
              have hmul := mul_le_mul hcoeff1 hcoeff2 (abs_nonneg _)
                (by positivity : 0 ≤ ((x.1 + 1 : ℕ) : ℝ) ^ q * (j : ℝ) ^ (x.1 + q))
              calc
                |((cumulantLogPoly n j) ^ q).coeff x.1 *
                    (cumulantLogPoly n j).coeff x.2|
                    = |((cumulantLogPoly n j) ^ q).coeff x.1| *
                        |(cumulantLogPoly n j).coeff x.2| := abs_mul _ _
                _ ≤ (((x.1 + 1 : ℕ) : ℝ) ^ q * (j : ℝ) ^ (x.1 + q)) *
                      (j : ℝ) ^ (x.2 + 1) := hmul
                _ = ((x.1 + 1 : ℕ) : ℝ) ^ q * (j : ℝ) ^ (m + q + 1) := by
                      have hsum : x.1 + q + (x.2 + 1) = m + q + 1 := by omega
                      rw [mul_assoc, ← pow_add, hsum]
                _ ≤ ((m + 1 : ℕ) : ℝ) ^ q * (j : ℝ) ^ (m + q + 1) :=
                      mul_le_mul_of_nonneg_right hpow_x1 (by positivity)
        _ = ((m + 1 : ℕ) : ℝ) ^ (q + 1) * (j : ℝ) ^ (m + (q + 1)) := by
              rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
              ring

/-- The logarithmic cumulant polynomial has degree at most its truncation order. -/
theorem natDegree_cumulantLogPoly_le (n j : ℕ) :
    (cumulantLogPoly n j).natDegree ≤ n := by
  rw [cumulantLogPoly]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun l hl => ?_)
  have hln : l + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hl)
  calc
    (Polynomial.C (rescalePowerSum (l + 1) j / (l + 1 : ℝ)) *
        Polynomial.X ^ (l + 1)).natDegree
        ≤ (Polynomial.C (rescalePowerSum (l + 1) j / (l + 1 : ℝ))).natDegree +
            (Polynomial.X ^ (l + 1 : ℕ)).natDegree := Polynomial.natDegree_mul_le
    _ ≤ n := by
      rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
      omega

/-- The `exp (-x)` truncation has degree at most its term count. -/
theorem natDegree_expNegTruncPoly_le (P : ℕ) :
    (expNegTruncPoly P).natDegree ≤ P := by
  rw [expNegTruncPoly]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun p hp => ?_)
  have hpP : p ≤ P := Nat.le_of_lt (Finset.mem_range.mp hp)
  calc
    (Polynomial.C (((-1 : ℝ) ^ p) / (p.factorial : ℝ)) * Polynomial.X ^ p).natDegree
        ≤ (Polynomial.C (((-1 : ℝ) ^ p) / (p.factorial : ℝ))).natDegree +
            (Polynomial.X ^ p).natDegree := Polynomial.natDegree_mul_le
    _ ≤ P := by
      rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
      omega

/-- Degree filtration for the finite multiplier coefficients. -/
theorem natDegree_multiplierTruncPoly_le (P n j : ℕ) :
    (multiplierTruncPoly P n j).natDegree ≤ P * n := by
  rw [multiplierTruncPoly, Polynomial.natDegree_comp]
  exact Nat.mul_le_mul (natDegree_expNegTruncPoly_le P) (natDegree_cumulantLogPoly_le n j)

/-- Coefficient-sum expansion over a fixed range large enough for the whole truncation.

This is the algebraic carrier for the finite `Σ e_p(j) / d^p` side of R1. -/
theorem eval_multiplierTruncPoly_coeff_sum (P n j : ℕ) (t : ℝ) :
    (multiplierTruncPoly P n j).eval t =
      ∑ p ∈ Finset.range (P * n + 1), multiplierCoeff P n j p * t ^ p := by
  rw [show (∑ p ∈ Finset.range (P * n + 1), multiplierCoeff P n j p * t ^ p) =
      ∑ p ∈ Finset.range (P * n + 1), (multiplierTruncPoly P n j).coeff p * t ^ p by
        simp [multiplierCoeff]]
  exact Polynomial.eval_eq_sum_range' (p := multiplierTruncPoly P n j) (x := t)
    (by exact Nat.lt_succ_of_le (natDegree_multiplierTruncPoly_le P n j))

/-- Evaluate the retained low-degree multiplier jet. -/
theorem eval_multiplierJetPoly (P n j : ℕ) (t : ℝ) :
    (multiplierJetPoly P n j).eval t =
      ∑ p ∈ Finset.range P, multiplierCoeff P n j p * t ^ p := by
  simpa [multiplierJetPoly, multiplierCoeff] using
    PolynomialTruncation.eval_lowTrunc (P := multiplierTruncPoly P n j) P t

/-- Coefficients of the retained jet agree with the multiplier coefficients below the
cutoff. -/
theorem coeff_multiplierJetPoly_of_lt (P n j p : ℕ) (hp : p < P) :
    (multiplierJetPoly P n j).coeff p = multiplierCoeff P n j p := by
  simpa [multiplierJetPoly, multiplierCoeff] using
    PolynomialTruncation.coeff_lowTrunc_of_lt (P := multiplierTruncPoly P n j) hp

/-- Below the cutoff, the retained jet has exactly the same coefficients as the full
finite multiplier polynomial. -/
theorem coeff_multiplierJetPoly_eq_coeff_of_lt (P n j p : ℕ) (hp : p < P) :
    (multiplierJetPoly P n j).coeff p = (multiplierTruncPoly P n j).coeff p := by
  rw [coeff_multiplierJetPoly_of_lt P n j p hp, multiplierCoeff]

/-- The part discarded by `multiplierJetPoly` is divisible by `T^P`. -/
theorem X_pow_dvd_multiplierTruncPoly_sub_jet (P n j : ℕ) :
    Polynomial.X ^ P ∣ multiplierTruncPoly P n j - multiplierJetPoly P n j := by
  simpa [PolynomialTruncation.highTail, multiplierJetPoly] using
    PolynomialTruncation.X_pow_dvd_highTail (P := multiplierTruncPoly P n j) P

/-- Exact tail factorization of the full multiplier polynomial beyond the retained jet. -/
theorem exists_multiplierTailPoly (P n j : ℕ) :
    ∃ Q : ℝ[X], multiplierTruncPoly P n j =
      multiplierJetPoly P n j + Polynomial.X ^ P * Q := by
  simpa [multiplierJetPoly] using
    PolynomialTruncation.exists_tailFactor (P := multiplierTruncPoly P n j) P

/-- Evaluated form of the exact tail factorization. -/
theorem exists_eval_multiplierTailPoly (P n j : ℕ) (t : ℝ) :
    ∃ Q : ℝ[X], (multiplierTruncPoly P n j).eval t =
      (multiplierJetPoly P n j).eval t + t ^ P * Q.eval t := by
  simpa [multiplierJetPoly] using
    PolynomialTruncation.exists_eval_tailFactor (P := multiplierTruncPoly P n j) P t

end

end RHTower
