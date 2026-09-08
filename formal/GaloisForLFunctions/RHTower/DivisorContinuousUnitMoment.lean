import GaloisForLFunctions.RHTower.RetainedPrimeSourceInterpolation
import GaloisForLFunctions.RHTower.Sieve.InghamExponentialMellinInversion
import GaloisForLFunctions.RHTower.DivisorSmoothSquareMaximum

/-!
# Positive inverse-cube moment of the literal divisor head

The full absolute-convergence half-plane of log(n)-tau(n)+2gamma reaches
the inverse-cube moment of its square-root summatory primitive. The primitive
is the literal unit head at every integer and positive on its first open
block, giving an absolutely convergent strictly positive moment.
No numerical result or source sign hypothesis is used.
-/

noncomputable section
open MeasureTheory Set Finset
namespace RHTower

/-- Literal unit head, interpolated in the square-root clock. -/
def divisorContinuousUnitHead (x : ℝ) : ℝ :=
  (squareRootSummatoryPrimitive (fun n => (primeFreeDivisorIncrement n : ℂ)) x).re

/-- Absolute convergence of the literal divisor source on its full absolute half-plane. -/
theorem LSeriesSummable_primeFreeDivisorIncrement_right {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (primeFreeDivisorIncrement n : ℂ)) s := by
  have hlog : LSeriesSummable (LSeries.logMul (1 : ℕ → ℂ)) s :=
    LSeriesSummable_logMul_of_lt_re (by
      rw [LSeries.abscissaOfAbsConv_one]; exact_mod_cast hs)
  have hd := Sieve.LSeriesSummable_card_divisors hs
  have hc := (LSeriesSummable_one_iff.mpr hs).smul (2 * (Real.eulerMascheroniConstant : ℂ))
  have he : (fun n => (primeFreeDivisorIncrement n : ℂ)) =
      LSeries.logMul (1 : ℕ → ℂ) - (fun n => (n.divisors.card : ℂ)) +
        (2 * (Real.eulerMascheroniConstant : ℂ)) • (1 : ℕ → ℂ) := by
    ext n
    simp [primeFreeDivisorIncrement, LSeries.logMul, Complex.natCast_log]
  rw [he]
  exact (hlog.sub hd).add hc

/-- No source mass occurs before the first integer. -/
theorem divisorContinuousUnitHead_eq_zero {x : ℝ} (hx : x ≤ 1) :
    divisorContinuousUnitHead x = 0 := by
  simp [divisorContinuousUnitHead, squareRootSummatoryPrimitive_eq_integral,
    Set.Ioo_eq_empty_of_le hx]

/-- All integer samples agree with the literal unsigned divisor channel. -/
theorem divisorContinuousUnitHead_nat (M : ℕ) :
    divisorContinuousUnitHead M = divisorUnsignedDilationChannel M 1 := by
  rw [divisorContinuousUnitHead, squareRootSummatoryPrimitive_nat]
  simp only [← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re,
    sum_primeFreeDivisorIncrement, divisorUnsignedDilationChannel, Nat.div_one]

/-- The signed summatory defect is the exact slope between adjacent square-root samples. -/
theorem divisorContinuousUnitHead_between {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hkx : (k : ℝ) ≤ x) (hxk : x ≤ (k+1 : ℕ)) :
    divisorContinuousUnitHead x = divisorUnsignedDilationChannel k 1 +
      (Real.sqrt x-Real.sqrt k)*primeFreeDivisorDefect k := by
  unfold divisorContinuousUnitHead
  rw [squareRootSummatoryPrimitive_between _ hk hkx hxk,
    ← Complex.ofReal_sum, sum_primeFreeDivisorIncrement]
  simp only [Complex.add_re, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [← divisorContinuousUnitHead, divisorContinuousUnitHead_nat]

/-- The continuous unit head is nonnegative everywhere. -/
theorem divisorContinuousUnitHead_nonneg (x : ℝ) : 0 ≤ divisorContinuousUnitHead x := by
  by_cases hx : x ≤ 1
  · rw [divisorContinuousUnitHead_eq_zero hx]
  · exact squareRootSummatoryPrimitive_re_nonneg _ (fun N => by
      change 0 ≤ divisorContinuousUnitHead N
      rw [divisorContinuousUnitHead_nat]
      exact divisorUnsignedDilationChannel_nonneg N 1) (le_of_not_ge hx)

private lemma unit_mellin :
    HasMellin (squareRootSummatoryPrimitive (fun n => (primeFreeDivisorIncrement n : ℂ))) (-2)
      (LSeries (fun n => (primeFreeDivisorIncrement n : ℂ)) (3/2) / 6) := by
  have hb (N : ℕ) : ‖∑ n ∈ Icc 1 N, (primeFreeDivisorIncrement n : ℂ)‖ ≤
      24 * (N : ℝ) ^ (1/2 : ℝ) := by
    rw [← Complex.ofReal_sum, sum_primeFreeDivisorIncrement,
      Complex.norm_real, Real.norm_eq_abs, ← Real.sqrt_eq_rpow]
    rcases N.eq_zero_or_pos with rfl | hN
    · simp [primeFreeDivisorDefect]
    · exact abs_primeFreeDivisorDefect_le hN
  have h := hasMellin_squareRootSummatoryPrimitive (by norm_num : (0:ℝ)≤24)
    hb (s := 2) (by norm_num) (by norm_num)
    (LSeriesSummable_primeFreeDivisorIncrement_right (by norm_num))
  norm_num at h ⊢
  exact h

private lemma moment_integrand (x : ℝ) :
    (((x : ℂ) ^ ((-2 : ℂ)-1)) *
      squareRootSummatoryPrimitive (fun n => (primeFreeDivisorIncrement n : ℂ)) x).re =
        divisorContinuousUnitHead x / x^3 := by
  norm_num [show (-2 : ℂ)-1 = -(3 : ℂ) by ring, Complex.cpow_neg,
    Complex.cpow_ofNat, ← Complex.ofReal_pow, ← Complex.ofReal_inv,
    Complex.mul_re, divisorContinuousUnitHead, div_eq_mul_inv, mul_comm]

/-- The inverse-cube moment is absolutely integrable on the full positive ray. -/
theorem integrable_divisorContinuousUnitHead_moment :
    IntegrableOn (fun x => divisorContinuousUnitHead x / x^3) (Ioi 0) := by
  apply unit_mellin.1.re.congr
  filter_upwards with x
  exact moment_integrand x

/-- Exact inverse-cube moment of the literal continuous divisor head. -/
theorem integral_divisorContinuousUnitHead_moment :
    (∫ x in Ioi (0 : ℝ), divisorContinuousUnitHead x / x^3) =
      (LSeries (fun n => (primeFreeDivisorIncrement n : ℂ)) (3/2)).re / 6 := by
  have h := congrArg Complex.re unit_mellin.2
  have hr := integral_re unit_mellin.1
  simp only [RCLike.re_to_complex, smul_eq_mul, moment_integrand] at hr
  simp only [mellin, smul_eq_mul] at h
  rw [← hr] at h
  simpa using h

private lemma first_defect_pos : 0 < primeFreeDivisorDefect 1 := by
  have h := (harmonic_mascheroni_half_bounds (n := 4) (by norm_num)).2
  norm_num [harmonic,Finset.sum_range_succ,Real.log_four_eq] at h
  norm_num [primeFreeDivisorDefect]
  linarith [Real.log_two_lt_d9]

/-- Strict source positivity on the first open block. -/
theorem divisorContinuousUnitHead_pos_first {x : ℝ} (hx : x ∈ Ioo (1 : ℝ) 2) :
    0 < divisorContinuousUnitHead x := by
  rw [divisorContinuousUnitHead_between (k := 1) le_rfl (by simpa using hx.1.le) (by simpa using hx.2.le)]
  have hz : divisorUnsignedDilationChannel 1 1 = 0 := by simp [divisorUnsignedDilationChannel]
  rw [hz, zero_add]
  exact mul_pos (sub_pos.mpr (Real.sqrt_lt_sqrt (by norm_num) (by simpa using hx.1))) first_defect_pos

/-- The signed-source unit moment is strictly positive, without numerical input. -/
theorem integral_divisorContinuousUnitHead_moment_pos :
    0 < ∫ x in Ioi (0 : ℝ), divisorContinuousUnitHead x / x^3 := by
  apply (integral_pos_iff_support_of_nonneg_ae _ integrable_divisorContinuousUnitHead_moment).mpr
  · have hsub : Ioo (1 : ℝ) 2 ⊆ Function.support (fun x => divisorContinuousUnitHead x/x^3) := by
      intro x hx
      exact ne_of_gt (div_pos (divisorContinuousUnitHead_pos_first hx) (pow_pos (by have := hx.1; linarith) 3))
    apply lt_of_lt_of_le _ (measure_mono hsub)
    rw [Measure.restrict_apply measurableSet_Ioo]
    have he : Ioo (1 : ℝ) 2 ∩ Ioi 0 = Ioo (1 : ℝ) 2 :=
      inter_eq_left.mpr (fun x hx => by have := hx.1; exact show 0<x by linarith)
    rw [he, Real.volume_Ioo]
    norm_num
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact div_nonneg (divisorContinuousUnitHead_nonneg x) (pow_nonneg hx.le _)

end RHTower
