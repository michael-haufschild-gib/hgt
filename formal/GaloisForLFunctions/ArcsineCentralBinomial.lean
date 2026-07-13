import Mathlib

/-!
# Central-binomial coefficients and the `(1-u²)^{-1/2}` generating function

The arcsine Taylor coefficients `c_j = binom(2j,j)/(4^j (2j+1))` arise from the generalized
binomial series of `(1+y)^{-1/2}`.  This module records the two coefficient facts underlying that
expansion:

* `Ring.choose (-1/2) n = (-1)^n · centralBinom n / 4^n` — the negative-half binomial coefficient in
  closed central-binomial form, proved from the descending-Pochhammer recurrence of `Ring.choose`
  and the central-binomial recurrence; and
* `centralBinom_gf` — the resulting `HasSum` expansion of `(1+y)^{-1/2}` on `‖y‖ < 1`.

Together these give the central-binomial generating function `∑ centralBinom n / 4^n · u^{2n}
= (1-u²)^{-1/2}`, the derivative series of `arcsin`.
-/

namespace GaloisForLFunctions

open scoped Nat
open Polynomial

/-- One-step descending recurrence for the generalized binomial coefficient over a field:
`(n+1)·choose a (n+1) = choose a n · (a - n)`, from `descPochhammer (n+1) = descPochhammer n · (X-n)`. -/
theorem choose_succ_field (a : ℝ) (n : ℕ) :
    ((n : ℝ) + 1) * Ring.choose a (n + 1) = Ring.choose a n * (a - n) := by
  have key := Ring.descPochhammer_eq_factorial_smul_choose (R := ℝ) a (n + 1)
  rw [descPochhammer_succ_right, Polynomial.smeval_mul,
      Ring.descPochhammer_eq_factorial_smul_choose (R := ℝ) a n] at key
  simp only [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast,
    npow_one, pow_zero, mul_one, nsmul_eq_mul, Nat.factorial_succ] at key
  push_cast at key
  have hfac : (n ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have h2 : (n ! : ℝ) * (((n : ℝ) + 1) * Ring.choose a (n + 1))
      = (n ! : ℝ) * (Ring.choose a n * (a - n)) := by linear_combination -key
  exact mul_left_cancel₀ hfac h2

/-- The negative-half generalized binomial coefficient in closed central-binomial form:
`Ring.choose (-1/2) n = (-1)^n · centralBinom n / 4^n`. -/
theorem choose_neg_half (n : ℕ) :
    Ring.choose (-1 / 2 : ℝ) n = (-1) ^ n * (Nat.centralBinom n : ℝ) / 4 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hrec := choose_succ_field (-1 / 2 : ℝ) n
    rw [ih] at hrec
    have hpos : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hcb : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ)
        = 2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    have hchoose : Ring.choose (-1 / 2 : ℝ) (n + 1)
        = ((-1) ^ n * (Nat.centralBinom n : ℝ) / 4 ^ n) * (-1 / 2 - (n : ℝ)) / ((n : ℝ) + 1) := by
      rw [eq_div_iff hpos]; linear_combination hrec
    have hkey : (Nat.centralBinom n : ℝ) * (-1 / 2 - (n : ℝ)) / ((n : ℝ) + 1)
        = -(Nat.centralBinom (n + 1) : ℝ) / 4 := by
      rw [div_eq_div_iff hpos (by norm_num : (4 : ℝ) ≠ 0)]
      linear_combination hcb
    rw [hchoose, pow_succ (-1 : ℝ), pow_succ (4 : ℝ),
        show ((-1 : ℝ) ^ n * (Nat.centralBinom n : ℝ) / 4 ^ n) * (-1 / 2 - (n : ℝ)) / ((n : ℝ) + 1)
          = ((-1 : ℝ) ^ n / 4 ^ n)
              * ((Nat.centralBinom n : ℝ) * (-1 / 2 - (n : ℝ)) / ((n : ℝ) + 1)) by ring,
        hkey]
    have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
    field_simp

/-- Generalized binomial expansion of `(1+y)^{-1/2}` on the unit ball, with the coefficients in
`Ring.choose` form. -/
theorem negHalf_rpow_hasSum (y : ℝ) (hy : ‖y‖ < 1) :
    HasSum (fun n : ℕ => Ring.choose (-1 / 2 : ℝ) n • y ^ n) ((1 + y) ^ (-1 / 2 : ℝ)) := by
  have hball := Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := (-1 / 2 : ℝ))
  have hy' : y ∈ Metric.eball (0 : ℝ) 1 := by
    simp only [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
    exact ENNReal.ofReal_lt_one.mpr hy
  have hsum := hball.hasSum hy'
  simp only [zero_add] at hsum
  convert hsum using 2 with n
  rw [binomialSeries_apply]
  congr 1
  rw [List.ofFn_const, List.prod_replicate]

/-- **Central-binomial generating function.**  On `|u| < 1`,
`∑ centralBinom n / 4^n · u^{2n} = (1 - u²)^{-1/2}` — the derivative series of `arcsin`. -/
theorem centralBinom_gf (u : ℝ) (hu : |u| < 1) :
    HasSum (fun n : ℕ => (Nat.centralBinom n : ℝ) / 4 ^ n * u ^ (2 * n))
      ((1 - u ^ 2) ^ (-1 / 2 : ℝ)) := by
  have hy : ‖-u ^ 2‖ < 1 := by
    rw [norm_neg, norm_pow, Real.norm_eq_abs]
    calc |u| ^ 2 < 1 ^ 2 := by
          apply pow_lt_pow_left₀ hu (abs_nonneg u); norm_num
      _ = 1 := one_pow 2
  have h := negHalf_rpow_hasSum (-u ^ 2) hy
  have hbase : (1 + -u ^ 2) = (1 - u ^ 2) := by ring
  rw [hbase] at h
  convert h using 2 with n
  rw [choose_neg_half, smul_eq_mul, show (-u ^ 2 : ℝ) = (-1) * u ^ 2 by ring, mul_pow,
      ← pow_mul u 2 n]
  have he : ((-1 : ℝ)) ^ n * (-1) ^ n = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨n, by ring⟩
  have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
  field_simp
  linear_combination (-(Nat.centralBinom n : ℝ) * u ^ (2 * n)) * he

end GaloisForLFunctions
