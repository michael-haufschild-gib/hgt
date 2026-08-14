import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Data.Nat.Choose.Central

/-!
# The central binomial generating function

The generalised binomial coefficient at `-1/2` is the central binomial coefficient divided by a
power of four,

`Ring.choose (-1/2) n = (-1)^n C(2n,n)/4^n`,

proved from the descending Pochhammer recursion and the central binomial recursion.  Substituting
`x ↦ -x` in the binomial series therefore gives the classical generating function

`(1-x)^{-1/2} = ∑_n C(2n,n) x^n / 4^n`  for `|x| < 1`,

the scalar identity behind the binomial resolvent expansion of the prime-normal cross-section.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-- The descending Pochhammer value at `-1/2`. -/
theorem descPochhammer_smeval_neg_half (n : ℕ) :
    (descPochhammer ℤ n).smeval (-(1 : ℝ) / 2)
      = (-1) ^ n * (Nat.centralBinom n : ℝ) * (n.factorial : ℝ) / 4 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hrec : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ)
        = 2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) := by
      have h := Nat.succ_mul_centralBinom_succ n
      have := congrArg (fun m : ℕ => ((m : ℝ))) h
      push_cast at this
      linarith [this]
    rw [descPochhammer_succ_right, Polynomial.smeval_mul, ih]
    have hval : (Polynomial.X - (n : Polynomial ℤ)).smeval (-(1 : ℝ) / 2)
        = -(1 : ℝ) / 2 - (n : ℝ) := by
      rw [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast]
      simp
    rw [hval]
    have hfac : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [hfac]
    have h4 : (4 : ℝ) ^ (n + 1) = 4 * 4 ^ n := by ring
    rw [h4, pow_succ]
    have h4n : (4 : ℝ) ^ n ≠ 0 := by positivity
    field_simp
    nlinarith [hrec, h4n]

/-- **The generalised binomial coefficient at `-1/2`.** -/
theorem ringChoose_neg_half (n : ℕ) :
    Ring.choose (-(1 : ℝ) / 2) n = (-1) ^ n * (Nat.centralBinom n : ℝ) / 4 ^ n := by
  rw [Ring.choose_eq_smul, descPochhammer_smeval_neg_half, smul_eq_mul]
  have hne : ((n.factorial : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp

/-- **The central binomial generating function.** -/
theorem hasSum_centralBinom {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => ((Nat.centralBinom n : ℝ) / 4 ^ n) * x ^ n)
      ((1 - x) ^ (-(1 : ℝ) / 2)) := by
  have hb := Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := -(1 : ℝ) / 2)
  have hy : (-x) ∈ Metric.eball (0 : ℝ) 1 := by
    show edist (-x) (0 : ℝ) < 1
    rw [edist_dist, Real.dist_eq, sub_zero, abs_neg]
    exact ENNReal.ofReal_lt_one.mpr hx
  have hsum := hb.hasSum hy
  have hval : ((1 : ℝ) + (0 + -x)) ^ (-(1 : ℝ) / 2) = (1 - x) ^ (-(1 : ℝ) / 2) := by
    congr 1
    ring
  rw [hval] at hsum
  refine hsum.congr_fun fun n => ?_
  rw [binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
    ringChoose_neg_half]
  have hsq : ((-1 : ℝ)) ^ n * ((-1 : ℝ)) ^ n = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have hxn : ((-x : ℝ)) ^ n = ((-1 : ℝ)) ^ n * x ^ n := by
    rw [← neg_one_mul, mul_pow]
  rw [hxn]
  calc ((Nat.centralBinom n : ℝ) / 4 ^ n) * x ^ n
      = (((-1 : ℝ)) ^ n * ((-1 : ℝ)) ^ n) * ((Nat.centralBinom n : ℝ) / 4 ^ n * x ^ n) := by
        rw [hsq, one_mul]
    _ = ((-1 : ℝ) ^ n * (Nat.centralBinom n : ℝ) / 4 ^ n) * ((-1 : ℝ) ^ n * x ^ n) := by ring

end GaloisForLFunctions.HTGeometry
