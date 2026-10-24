import GaloisForLFunctions.HTGeometry.LogConcaveIntegralComposition
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspKernelLogConcavity
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspSchwartz
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # Gaussian integer masses and positive theta kernels

The power-weighted Gaussian integer sum has a positive integral representation
through the actual theta source. The causal kernels in that representation
preserve two-by-two positivity, including the common Gaussian scale shared
by distinct divisibility events.
-/

open MeasureTheory Set Filter Topology

namespace RHTower.GaussianDivisibility

open GaloisForLFunctions.HTGeometry

noncomputable section
set_option autoImplicit false

/-- The literal positive-integer Gaussian mass, with a real power weight. -/
def integerGaussianMass (σ y : ℝ) : ℝ :=
  ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ (-σ)) *
    Real.exp (-y * ((n + 1 : ℕ) : ℝ) ^ 2)

/-- The positive second Gaussian moment before normalization. -/
def gaussianSecondMass (y : ℝ) : ℝ :=
  ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ 2 *
    Real.exp (-y * ((n + 1 : ℕ) : ℝ) ^ 2)

theorem summable_integerGaussianMass {σ y : ℝ} (hσ : 0 ≤ σ) (hy : 0 < y) :
    Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (-σ)) *
      Real.exp (-y * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
  have hs : Summable (fun n : ℕ => Real.exp (-y * (n : ℝ) ^ 2)) := by
    simpa only [pow_zero, one_mul] using summable_pow_mul_exp_neg_nat_sq 0 hy
  apply Summable.of_norm_bounded ((summable_nat_add_iff 1).mpr hs)
  intro n
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hp := Real.rpow_le_one_of_one_le_of_nonpos hn (neg_nonpos.mpr hσ)
  rw [Real.norm_of_nonneg (mul_nonneg
    (Real.rpow_nonneg (zero_le_one.trans hn) _) (Real.exp_pos _).le)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le

theorem summable_gaussianSecondMass {y : ℝ} (hy : 0 < y) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2 *
      Real.exp (-y * ((n + 1 : ℕ) : ℝ) ^ 2)) :=
  (summable_nat_add_iff 1).mpr (summable_pow_mul_exp_neg_nat_sq 2 hy)

/-- The native logarithmic theta tail is the unweighted literal Gaussian mass. -/
theorem tail_zero_eq_integerGaussianMass (t : ℝ) :
    thetaCuspTailDerivative 0 t =
      Real.exp (t / 2) * integerGaussianMass 0 (Real.pi * Real.exp (2 * t)) := by
  rw [integerGaussianMass, ← tsum_mul_left, thetaCuspTailDerivative]
  apply tsum_congr
  intro n
  have he : Real.exp (2 * t) = Real.exp t ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simp only [thetaCuspTailDerivativePolynomial, thetaCuspPolynomialAtom,
    Polynomial.eval_one, neg_zero, Real.rpow_zero, one_mul, mul_one, he, mul_pow]
  congr 2
  ring

/-- The first theta-tail derivative is the literal second Gaussian moment. -/
theorem tail_first_sub_half_eq_gaussianSecondMass (t : ℝ) :
    thetaCuspTailDerivative 1 t - (1 / 2 : ℝ) * thetaCuspTailDerivative 0 t =
      -(2 * Real.pi) * Real.exp (5 * t / 2) *
        gaussianSecondMass (Real.pi * Real.exp (2 * t)) := by
  have hs₁ := summable_thetaCuspTailDerivative 1 t
  have hs₀ := summable_thetaCuspTailDerivative 0 t
  rw [thetaCuspTailDerivative, thetaCuspTailDerivative, ← tsum_mul_left,
    ← hs₁.tsum_sub (hs₀.mul_left (1 / 2 : ℝ)),
    gaussianSecondMass, ← tsum_mul_left]
  apply tsum_congr
  intro n
  have he : Real.exp (2 * t) = Real.exp t ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have he' : Real.exp (5 * t / 2) = Real.exp (t / 2) * Real.exp t ^ 2 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp only [thetaCuspTailDerivativePolynomial, thetaCuspLogDerivativeStep,
    thetaCuspPolynomialAtom, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow, Polynomial.eval_one, Polynomial.derivative_one,
    mul_zero, add_zero, mul_one, he, he', mul_pow]
  ring

/-- The first-order flux whose derivative is the positively weighted theta source. -/
def thetaGaussianFlux (t : ℝ) : ℝ :=
  Real.exp (t / 2) *
    (thetaCuspTailDerivative 1 t - (1 / 2 : ℝ) * thetaCuspTailDerivative 0 t)

theorem hasDerivAt_thetaGaussianFlux (t : ℝ) :
    HasDerivAt thetaGaussianFlux
      (Real.exp (t / 2) * thetaCuspFullSource t) t := by
  have he : HasDerivAt (fun u : ℝ => Real.exp (u / 2))
      ((1 / 2 : ℝ) * Real.exp (t / 2)) t := by
    simpa only [id_eq, mul_comm] using ((hasDerivAt_id t).div_const 2).exp
  have h := he.mul ((hasDerivAt_thetaCuspTailDerivative 1 t).sub
    ((hasDerivAt_thetaCuspTailDerivative 0 t).const_mul (1 / 2 : ℝ)))
  change HasDerivAt (fun u => Real.exp (u / 2) *
    (thetaCuspTailDerivative 1 u - (1 / 2 : ℝ) * thetaCuspTailDerivative 0 u)) _ t
  refine h.congr_deriv ?_
  rw [thetaCuspFullSource_eq_tail_second_sub]
  simp only [Pi.sub_apply]
  norm_num only [Nat.add_zero, Nat.reduceAdd]
  ring

private theorem tendsto_exp_half_mul_tail (m : ℕ) :
    Tendsto (fun x : ℝ => Real.exp (x / 2) * thetaCuspTailDerivative m x)
      atTop (nhds 0) := by
  have hmajor : Tendsto
      (fun x : ℝ => thetaCuspTailDerivativeExpConstant m * Real.exp (-x / 2))
      atTop (nhds 0) := by
    have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))).const_mul
      (thetaCuspTailDerivativeExpConstant m)
    simpa only [mul_zero, neg_div, Function.comp_apply, id_eq] using h
  apply squeeze_zero_norm' _ hmajor
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
  calc
    _ ≤ Real.exp (x / 2) * (thetaCuspTailDerivativeExpConstant m * Real.exp (-x)) :=
      mul_le_mul_of_nonneg_left (abs_thetaCuspTailDerivative_le_exp_neg m hx)
        (Real.exp_pos _).le
    _ = _ := by rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

theorem tendsto_thetaGaussianFlux : Tendsto thetaGaussianFlux atTop (nhds 0) := by
  have h := (tendsto_exp_half_mul_tail 1).sub
    ((tendsto_exp_half_mul_tail 0).const_mul (1 / 2 : ℝ))
  have heq : (fun x : ℝ => Real.exp (x / 2) * thetaCuspTailDerivative 1 x -
      (1 / 2 : ℝ) * (Real.exp (x / 2) * thetaCuspTailDerivative 0 x)) =
      thetaGaussianFlux := by
    funext x
    unfold thetaGaussianFlux
    ring
  rw [heq] at h
  simpa only [mul_zero, sub_zero] using h

theorem integrable_exp_half_mul_theta :
    Integrable (fun x : ℝ => Real.exp (x / 2) * thetaCuspFullSource x) := by
  have hsource (x : ℝ) : |thetaCuspFullSource x| ≤
      thetaCuspDerivativeExpConstant 0 * Real.exp (-|x|) := by
    rcases le_or_gt 0 x with hx | hx
    · simpa only [iteratedDeriv_zero, abs_of_nonneg hx] using
        abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg 0 hx
    · have h := abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg 0
        (show 0 ≤ -x by linarith)
      simpa only [iteratedDeriv_zero, thetaCuspFullSource_neg, abs_of_neg hx, neg_neg] using h
  have hC : 0 ≤ thetaCuspDerivativeExpConstant 0 := by
    have h := (abs_nonneg (thetaCuspFullSource 0)).trans (hsource 0)
    simpa only [abs_zero, neg_zero, Real.exp_zero, mul_one] using h
  have hbase : Integrable (fun x : ℝ => Real.exp (-|x| / 2)) := by
    have h := RHTower.integrable_exp_neg_abs.comp_mul_left'
      (by norm_num : (1 / 2 : ℝ) ≠ 0)
    simpa only [one_div_mul_eq_div, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), neg_div] using h
  refine (hbase.const_mul (thetaCuspDerivativeExpConstant 0)).mono'
    (by have hc := contDiff_thetaCuspFullSource.continuous; fun_prop) ?_
  filter_upwards with x
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
  calc
    _ ≤ Real.exp (x / 2) * (thetaCuspDerivativeExpConstant 0 * Real.exp (-|x|)) :=
      mul_le_mul_of_nonneg_left (hsource x) (Real.exp_pos _).le
    _ = thetaCuspDerivativeExpConstant 0 * Real.exp (x / 2 - |x|) := by
      rw [mul_left_comm, ← Real.exp_add, sub_eq_add_neg]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith [le_abs_self x])) hC

/-- Integrating the first-order source flux gives a positive Gaussian tail identity. -/
theorem integral_exp_half_theta_tail (t : ℝ) :
    (∫ u in Ioi t, Real.exp (u / 2) * thetaCuspFullSource u) =
      -thetaGaussianFlux t := by
  have hcont : Continuous thetaGaussianFlux :=
    continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_thetaGaussianFlux x).continuousAt)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := t)
    hcont.continuousAt.continuousWithinAt
    (fun x _ => hasDerivAt_thetaGaussianFlux x)
    integrable_exp_half_mul_theta.integrableOn tendsto_thetaGaussianFlux
  simpa only [zero_sub] using h

/-- A causal exponential times a nonnegative power of the exponential increment. -/
def causalPowerExp (α c x : ℝ) : ℝ :=
  if 0 < x then (Real.exp (2 * x) - 1) ^ α * Real.exp (c * x) else 0

theorem theta_source_four_point : LogFourPoint thetaCuspFullSource :=
  logFourPoint_of_concaveOn_log thetaCuspFullSource_pos_all
    strictConcaveOn_thetaCuspLogSource.concaveOn

theorem causalPowerExp_nonneg (α c x : ℝ) : 0 ≤ causalPowerExp α c x := by
  unfold causalPowerExp
  split_ifs with hx
  · have hb : 0 ≤ Real.exp (2 * x) - 1 :=
      sub_nonneg.mpr (Real.one_le_exp (by linarith))
    exact mul_nonneg (Real.rpow_nonneg hb _) (Real.exp_pos _).le
  · exact le_rfl

/-- Exponential increments have an exact positive four-point difference. -/
theorem exp_increment_four_point (x : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.exp (2 * x) - 1) * (Real.exp (2 * (x + a + b)) - 1) ≤
      (Real.exp (2 * (x + a)) - 1) * (Real.exp (2 * (x + b)) - 1) := by
  have hdiff :
      (Real.exp (2 * (x + a)) - 1) * (Real.exp (2 * (x + b)) - 1) -
        (Real.exp (2 * x) - 1) * (Real.exp (2 * (x + a + b)) - 1) =
      Real.exp (2 * x) * (Real.exp (2 * a) - 1) * (Real.exp (2 * b) - 1) := by
    simp only [mul_add, Real.exp_add]
    ring
  have hnonneg := mul_nonneg
    (mul_nonneg (Real.exp_pos (2 * x)).le
      (sub_nonneg.mpr (Real.one_le_exp (by linarith : 0 ≤ 2 * a))))
    (sub_nonneg.mpr (Real.one_le_exp (by linarith : 0 ≤ 2 * b)))
  linarith only [hdiff, hnonneg]

/-- Every nonnegative power preserves the causal kernel's four-point inequality. -/
theorem causalPowerExp_four_point {α : ℝ} (hα : 0 ≤ α) (c : ℝ) :
    LogFourPoint (causalPowerExp α c) := by
  intro x a b ha hb
  by_cases hx : 0 < x
  · have hxa : 0 < x + a := by linarith
    have hxb : 0 < x + b := by linarith
    have hxab : 0 < x + a + b := by linarith
    have hbase (z : ℝ) (hz : 0 < z) : 0 ≤ Real.exp (2 * z) - 1 :=
      sub_nonneg.mpr (Real.one_le_exp (by linarith))
    have hp := Real.rpow_le_rpow
      (mul_nonneg (hbase x hx) (hbase (x + a + b) hxab))
      (exp_increment_four_point x ha hb) hα
    rw [Real.mul_rpow (hbase x hx) (hbase (x + a + b) hxab),
      Real.mul_rpow (hbase (x + a) hxa) (hbase (x + b) hxb)] at hp
    have he : Real.exp (c * x) * Real.exp (c * (x + a + b)) =
        Real.exp (c * (x + a)) * Real.exp (c * (x + b)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    simp only [causalPowerExp, if_pos hx, if_pos hxa, if_pos hxb, if_pos hxab]
    calc
      _ = ((Real.exp (2 * x) - 1) ^ α * (Real.exp (2 * (x + a + b)) - 1) ^ α) *
          (Real.exp (c * x) * Real.exp (c * (x + a + b))) := by ring
      _ ≤ ((Real.exp (2 * (x + a)) - 1) ^ α *
          (Real.exp (2 * (x + b)) - 1) ^ α) *
          (Real.exp (c * x) * Real.exp (c * (x + a + b))) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
      _ = _ := by rw [he]; ring
  · rw [causalPowerExp, if_neg hx, zero_mul]
    exact mul_nonneg (causalPowerExp_nonneg α c (x + a))
      (causalPowerExp_nonneg α c (x + b))

/-- Reflection turns right-add integral composition into ordinary convolution. -/
theorem logFourPoint_future_integral {f g : ℝ → ℝ}
    (hf : LogFourPoint f) (hg : LogFourPoint g)
    (hfg : ∀ x, Integrable (fun u => f (x + u) * g u)) :
    LogFourPoint (fun x => ∫ u, f (x + u) * g u) := by
  have hint (x : ℝ) : Integrable (fun u => f (x - u) * g (-u)) := by
    simpa only [sub_eq_add_neg] using (hfg x).comp_neg
  have h := logFourPoint_convolution hf (logFourPoint_reflect hg) hint
  have heq (x : ℝ) : (∫ u, f (x - u) * g (-u)) = ∫ u, f (x + u) * g u := by
    simpa only [sub_eq_add_neg] using
      integral_neg_eq_self (fun u : ℝ => f (x + u) * g u) volume
  simp_rw [heq] at h
  exact h

/-- The positive future theta tail is a first-order Gaussian moment. -/
def thetaGaussianFuture (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * thetaCuspTailDerivative 0 t - thetaCuspTailDerivative 1 t

theorem thetaGaussianFuture_eq_secondMass (t : ℝ) :
    thetaGaussianFuture t = 2 * Real.pi * Real.exp (5 * t / 2) *
      gaussianSecondMass (Real.pi * Real.exp (2 * t)) := by
  have h := tail_first_sub_half_eq_gaussianSecondMass t
  unfold thetaGaussianFuture
  linarith only [h]

theorem integrable_thetaGaussianFuture_integrand (t : ℝ) :
    Integrable (fun u : ℝ => Real.exp (u / 2) * thetaCuspFullSource (t + u)) := by
  have h := (integrable_exp_half_mul_theta.comp_add_right t).const_mul
    (Real.exp (-t / 2))
  have heq : (fun u : ℝ => Real.exp (-t / 2) *
      (Real.exp ((u + t) / 2) * thetaCuspFullSource (u + t))) =
      fun u : ℝ => Real.exp (u / 2) * thetaCuspFullSource (t + u) := by
    funext u
    rw [← mul_assoc, ← Real.exp_add]
    congr 2 <;> ring
  rw [heq] at h
  exact h

theorem thetaGaussianFuture_eq_integral (t : ℝ) :
    thetaGaussianFuture t =
      ∫ u in Ioi (0 : ℝ), Real.exp (u / 2) * thetaCuspFullSource (t + u) := by
  have heq : (fun v : ℝ => (Ioi t).indicator
      (fun u => Real.exp (u / 2) * thetaCuspFullSource u) (v + t)) =
      (Ioi (0 : ℝ)).indicator (fun v => Real.exp (t / 2) *
        (Real.exp (v / 2) * thetaCuspFullSource (t + v))) := by
    funext v
    by_cases hv : 0 < v
    · have hvt : t < v + t := by linarith
      simp only [Set.indicator, mem_Ioi, if_pos hvt, if_pos hv, ← mul_assoc,
        ← Real.exp_add]
      congr 2 <;> ring
    · have hvt : ¬t < v + t := by linarith
      simp only [Set.indicator, mem_Ioi, if_neg hvt, if_neg hv]
  have hs := integral_add_right_eq_self (μ := volume)
    ((Ioi t).indicator (fun u : ℝ => Real.exp (u / 2) * thetaCuspFullSource u)) t
  rw [heq, integral_indicator measurableSet_Ioi,
    integral_indicator measurableSet_Ioi, integral_const_mul,
    integral_exp_half_theta_tail] at hs
  apply (mul_left_cancel₀ (Real.exp_ne_zero (t / 2)))
  rw [hs]
  unfold thetaGaussianFuture thetaGaussianFlux
  ring

theorem thetaGaussianFuture_eq_causal_integral (t : ℝ) :
    thetaGaussianFuture t =
      ∫ u : ℝ, thetaCuspFullSource (t + u) * causalPowerExp 0 (1 / 2) u := by
  rw [thetaGaussianFuture_eq_integral, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with u
  by_cases hu : 0 < u
  · simp only [Set.indicator, mem_Ioi, causalPowerExp, if_pos hu, Real.rpow_zero,
      one_mul]
    rw [mul_comm]
    congr 2
    ring
  · simp only [Set.indicator, mem_Ioi, causalPowerExp, if_neg hu, mul_zero]

theorem thetaGaussianFuture_four_point : LogFourPoint thetaGaussianFuture := by
  have hint (t : ℝ) : Integrable
      (fun u : ℝ => thetaCuspFullSource (t + u) * causalPowerExp 0 (1 / 2) u) := by
    have h := (integrable_thetaGaussianFuture_integrand t).indicator
      (measurableSet_Ioi (a := (0 : ℝ)))
    have heq : (Ioi (0 : ℝ)).indicator
        (fun u => Real.exp (u / 2) * thetaCuspFullSource (t + u)) =
        fun u => thetaCuspFullSource (t + u) * causalPowerExp 0 (1 / 2) u := by
      funext u
      by_cases hu : 0 < u
      · simp only [Set.indicator, mem_Ioi, causalPowerExp, if_pos hu, Real.rpow_zero,
          one_mul]
        rw [mul_comm]
        congr 2
        ring
      · simp only [Set.indicator, mem_Ioi, causalPowerExp, if_neg hu, mul_zero]
    rw [heq] at h
    exact h
  have h := logFourPoint_future_integral theta_source_four_point
    (causalPowerExp_four_point (α := 0) le_rfl (1 / 2)) hint
  simpa only [← thetaGaussianFuture_eq_causal_integral] using h

private theorem gaussian_moment_factor (α y k : ℝ) :
    (fun u : ℝ => u ^ α * (k ^ 2 * Real.exp (-(y + u) * k ^ 2))) =
      fun u : ℝ => (k ^ 2 * Real.exp (-y * k ^ 2)) *
        (u ^ α * Real.exp (-(k ^ 2) * u)) := by
  funext u
  rw [show -(y + u) * k ^ 2 = -y * k ^ 2 + -(k ^ 2) * u by ring,
    Real.exp_add]
  ring

private theorem integrable_gaussian_moment_term {α k : ℝ}
    (hα : 0 ≤ α) (hk : 0 < k) (y : ℝ) :
    IntegrableOn (fun u : ℝ => u ^ α *
      (k ^ 2 * Real.exp (-(y + u) * k ^ 2))) (Ioi 0) := by
  rw [gaussian_moment_factor]
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := 1) (s := α) (b := k ^ 2) (by linarith) le_rfl (sq_pos_of_pos hk)
  simp only [Real.rpow_one] at h
  exact h.const_mul _

private theorem integral_gaussian_moment_term {α k : ℝ}
    (hα : 0 ≤ α) (hk : 0 < k) (y : ℝ) :
    (∫ u in Ioi (0 : ℝ), u ^ α * (k ^ 2 * Real.exp (-(y + u) * k ^ 2))) =
      Real.Gamma (α + 1) * k ^ (-(2 * α)) * Real.exp (-y * k ^ 2) := by
  rw [gaussian_moment_factor, integral_const_mul]
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := 1) (q := α) (b := k ^ 2) (by norm_num) (by linarith) (sq_pos_of_pos hk)
  simp only [Real.rpow_one, div_one, mul_one] at h
  rw [h]
  have hp : k ^ 2 * (k ^ 2) ^ (-(α + 1)) = k ^ (-(2 * α)) := by
    rw [← Real.rpow_natCast k 2, ← Real.rpow_mul hk.le, ← Real.rpow_add hk]
    congr 1
    norm_num
    ring
  calc
    _ = Real.Gamma (α + 1) * (k ^ 2 * (k ^ 2) ^ (-(α + 1))) *
        Real.exp (-y * k ^ 2) := by ring
    _ = _ := by rw [hp]

theorem integerGaussianMass_pos {σ y : ℝ} (hσ : 0 ≤ σ) (hy : 0 < y) :
    0 < integerGaussianMass σ y := by
  exact (summable_integerGaussianMass hσ hy).tsum_pos
    (fun n => by positivity) 0 (by positivity)

/-- The gamma transform of the literal second Gaussian moment recovers every
nonnegative power weight, including zero. -/
theorem integral_rpow_gaussianSecondMass {α y : ℝ} (hα : 0 ≤ α) (hy : 0 < y) :
    (∫ u in Ioi (0 : ℝ), u ^ α * gaussianSecondMass (y + u)) =
      Real.Gamma (α + 1) * integerGaussianMass (2 * α) y := by
  let F : ℕ → ℝ → ℝ := fun n u => u ^ α *
    (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-(y + u) * ((n + 1 : ℕ) : ℝ) ^ 2))
  have hn (n : ℕ) : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hint (n : ℕ) : IntegrableOn (F n) (Ioi 0) :=
    integrable_gaussian_moment_term hα (hn n) y
  have hval (n : ℕ) : (∫ u in Ioi (0 : ℝ), F n u) =
      Real.Gamma (α + 1) * (((n + 1 : ℕ) : ℝ) ^ (-(2 * α)) *
        Real.exp (-y * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
    rw [integral_gaussian_moment_term hα (hn n) y]
    ring
  have hnorm (n : ℕ) : (∫ u in Ioi (0 : ℝ), ‖F n u‖) =
      ∫ u in Ioi (0 : ℝ), F n u := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    apply Real.norm_of_nonneg
    dsimp [F]
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt hu) _)
      (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  have hsum : Summable (fun n => ∫ u in Ioi (0 : ℝ), ‖F n u‖) := by
    simp_rw [hnorm, hval]
    exact (summable_integerGaussianMass (by positivity : 0 ≤ 2 * α) hy).mul_left _
  have h := integral_tsum_of_summable_integral_norm hint hsum
  simp_rw [hval] at h
  rw [tsum_mul_left] at h
  have heq : (fun u : ℝ => ∑' n : ℕ, F n u) =
      fun u : ℝ => u ^ α * gaussianSecondMass (y + u) := by
    funext u
    exact tsum_mul_left
  rw [heq] at h
  exact h.symm

theorem integrable_rpow_gaussianSecondMass {α y : ℝ} (hα : 0 ≤ α) (hy : 0 < y) :
    IntegrableOn (fun u : ℝ => u ^ α * gaussianSecondMass (y + u)) (Ioi 0) := by
  by_contra hnot
  have h := integral_rpow_gaussianSecondMass hα hy
  rw [integral_undef hnot] at h
  have hp := mul_pos (Real.Gamma_pos_of_pos (by linarith : 0 < α + 1))
    (integerGaussianMass_pos (by positivity : 0 ≤ 2 * α) hy)
  linarith only [h, hp]

/-- The exponential scale increment maps the positive ray onto itself. -/
private theorem image_gaussianScaleIncrement {y : ℝ} (hy : 0 < y) :
    (fun r : ℝ => y * (Real.exp (2 * r) - 1)) '' Ioi 0 = Ioi 0 := by
  ext u
  constructor
  · rintro ⟨r, hr, rfl⟩
    change 0 < r at hr
    exact mul_pos hy (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith)))
  · intro hu
    change 0 < u at hu
    have hp : 0 < 1 + u / y := by positivity
    refine ⟨Real.log (1 + u / y) / 2,
      div_pos (Real.log_pos (by have : 0 < u / y := div_pos hu hy; linarith))
        (by norm_num), ?_⟩
    dsimp only
    rw [show 2 * (Real.log (1 + u / y) / 2) = Real.log (1 + u / y) by ring,
      Real.exp_log hp]
    field_simp [hy.ne']
    ring

private theorem hasDerivAt_gaussianScaleIncrement (y r : ℝ) :
    HasDerivAt (fun v : ℝ => y * (Real.exp (2 * v) - 1))
      (2 * y * Real.exp (2 * r)) r := by
  have h := (((hasDerivAt_id r).const_mul 2).exp.sub_const 1).const_mul y
  exact h.congr_deriv (by dsimp; ring)

private theorem injOn_gaussianScaleIncrement {y : ℝ} (hy : 0 < y) :
    InjOn (fun r : ℝ => y * (Real.exp (2 * r) - 1)) (Ioi 0) := by
  intro a _ b _ hab
  have he := mul_left_cancel₀ hy.ne' hab
  have he' : Real.exp (2 * a) = Real.exp (2 * b) := by linarith only [he]
  have := Real.exp_injective he'
  linarith

private theorem integral_gaussianScaleIncrement {y : ℝ} (hy : 0 < y) (g : ℝ → ℝ) :
    (∫ u in Ioi (0 : ℝ), g u) =
      ∫ r in Ioi (0 : ℝ), (2 * y * Real.exp (2 * r)) *
        g (y * (Real.exp (2 * r) - 1)) := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun r _ => (hasDerivAt_gaussianScaleIncrement y r).hasDerivWithinAt)
    (injOn_gaussianScaleIncrement hy) g
  rw [image_gaussianScaleIncrement hy] at h
  simpa only [abs_of_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hy)
    (Real.exp_pos _)), smul_eq_mul] using h

private theorem integrable_gaussianScaleIncrement {y : ℝ} (hy : 0 < y) (g : ℝ → ℝ) :
    IntegrableOn g (Ioi 0) ↔
      IntegrableOn (fun r : ℝ => (2 * y * Real.exp (2 * r)) *
        g (y * (Real.exp (2 * r) - 1))) (Ioi 0) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun r _ => (hasDerivAt_gaussianScaleIncrement y r).hasDerivWithinAt)
    (injOn_gaussianScaleIncrement hy) g
  rw [image_gaussianScaleIncrement hy] at h
  simpa only [abs_of_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hy)
    (Real.exp_pos _)), smul_eq_mul] using h

/-- The second positive transform of the theta source. -/
def gaussianPowerFuture (α t : ℝ) : ℝ :=
  ∫ r in Ioi (0 : ℝ), thetaGaussianFuture (t + r) *
    ((Real.exp (2 * r) - 1) ^ α * Real.exp (-r / 2))

private theorem gaussianScaleIncrement_moment_factor (α t : ℝ) {r : ℝ}
    (hr : 0 < r) :
    (2 * (Real.pi * Real.exp (2 * t)) * Real.exp (2 * r)) *
      (((Real.pi * Real.exp (2 * t)) * (Real.exp (2 * r) - 1)) ^ α *
        gaussianSecondMass ((Real.pi * Real.exp (2 * t)) +
          (Real.pi * Real.exp (2 * t)) * (Real.exp (2 * r) - 1))) =
      (Real.pi ^ α * Real.exp ((2 * α - 1 / 2) * t)) *
        (thetaGaussianFuture (t + r) *
          ((Real.exp (2 * r) - 1) ^ α * Real.exp (-r / 2))) := by
  have hy : 0 < Real.pi * Real.exp (2 * t) := mul_pos Real.pi_pos (Real.exp_pos _)
  have hrb : 0 ≤ Real.exp (2 * r) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp (by linarith))
  have harg : Real.pi * Real.exp (2 * t) +
      (Real.pi * Real.exp (2 * t)) * (Real.exp (2 * r) - 1) =
      Real.pi * Real.exp (2 * (t + r)) := by
    rw [mul_add, Real.exp_add]
    ring
  have he : Real.exp (2 * t) * Real.exp (2 * r) * Real.exp ((2 * t) * α) =
      Real.exp ((2 * α - 1 / 2) * t) * Real.exp (5 * (t + r) / 2) *
        Real.exp (-r / 2) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [harg, Real.mul_rpow hy.le hrb,
    Real.mul_rpow Real.pi_pos.le (Real.exp_pos _).le,
    Real.rpow_def_of_pos (Real.exp_pos (2 * t)), Real.log_exp,
    thetaGaussianFuture_eq_secondMass]
  calc
    _ = (2 * Real.pi * Real.pi ^ α) *
        (Real.exp (2 * t) * Real.exp (2 * r) * Real.exp ((2 * t) * α)) *
        (Real.exp (2 * r) - 1) ^ α *
        gaussianSecondMass (Real.pi * Real.exp (2 * (t + r))) := by ring
    _ = _ := by rw [he]; ring

/-- A positive gamma transform, identified with the original integer series. -/
theorem gamma_mul_integerGaussianMass_eq_powerFuture {α : ℝ} (hα : 0 ≤ α) (t : ℝ) :
    Real.Gamma (α + 1) * integerGaussianMass (2 * α) (Real.pi * Real.exp (2 * t)) =
      (Real.pi ^ α * Real.exp ((2 * α - 1 / 2) * t)) * gaussianPowerFuture α t := by
  have hy : 0 < Real.pi * Real.exp (2 * t) := mul_pos Real.pi_pos (Real.exp_pos _)
  rw [← integral_rpow_gaussianSecondMass hα hy,
    integral_gaussianScaleIncrement hy]
  have heq := integral_congr_ae (μ := volume.restrict (Ioi (0 : ℝ)))
    (show (fun r : ℝ => (2 * (Real.pi * Real.exp (2 * t)) * Real.exp (2 * r)) *
        (((Real.pi * Real.exp (2 * t)) * (Real.exp (2 * r) - 1)) ^ α *
          gaussianSecondMass ((Real.pi * Real.exp (2 * t)) +
            (Real.pi * Real.exp (2 * t)) * (Real.exp (2 * r) - 1)))) =ᵐ[_]
      (fun r : ℝ => (Real.pi ^ α * Real.exp ((2 * α - 1 / 2) * t)) *
        (thetaGaussianFuture (t + r) *
          ((Real.exp (2 * r) - 1) ^ α * Real.exp (-r / 2)))) by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact gaussianScaleIncrement_moment_factor α t hr)
  rw [heq, integral_const_mul]
  rfl

theorem integrable_gaussianPowerFuture_integrand {α : ℝ} (hα : 0 ≤ α) (t : ℝ) :
    IntegrableOn (fun r : ℝ => thetaGaussianFuture (t + r) *
      ((Real.exp (2 * r) - 1) ^ α * Real.exp (-r / 2))) (Ioi 0) := by
  have hy : 0 < Real.pi * Real.exp (2 * t) := mul_pos Real.pi_pos (Real.exp_pos _)
  have h := (integrable_gaussianScaleIncrement hy
    (fun u : ℝ => u ^ α * gaussianSecondMass (Real.pi * Real.exp (2 * t) + u))).mp
    (integrable_rpow_gaussianSecondMass hα hy)
  have h' := h.congr_fun (fun r hr => gaussianScaleIncrement_moment_factor α t hr)
    measurableSet_Ioi
  have hc : Real.pi ^ α * Real.exp ((2 * α - 1 / 2) * t) ≠ 0 := by positivity
  have h'' := h'.const_mul (Real.pi ^ α * Real.exp ((2 * α - 1 / 2) * t))⁻¹
  have heq : (fun r : ℝ => (Real.pi ^ α * Real.exp ((2 * α - 1 / 2) * t))⁻¹ *
      ((Real.pi ^ α * Real.exp ((2 * α - 1 / 2) * t)) *
        (thetaGaussianFuture (t + r) *
          ((Real.exp (2 * r) - 1) ^ α * Real.exp (-r / 2))))) =
      fun r => thetaGaussianFuture (t + r) *
        ((Real.exp (2 * r) - 1) ^ α * Real.exp (-r / 2)) := by
    funext r
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [heq] at h''
  exact h''

private theorem gaussianPowerFuture_indicator (α t : ℝ) :
    (Ioi (0 : ℝ)).indicator (fun r => thetaGaussianFuture (t + r) *
      ((Real.exp (2 * r) - 1) ^ α * Real.exp (-r / 2))) =
      fun r => thetaGaussianFuture (t + r) * causalPowerExp α (-1 / 2) r := by
  funext r
  by_cases hr : 0 < r
  · simp only [Set.indicator, mem_Ioi, causalPowerExp, if_pos hr]
    congr 3
    ring
  · simp only [Set.indicator, mem_Ioi, causalPowerExp, if_neg hr, mul_zero]

theorem gaussianPowerFuture_four_point {α : ℝ} (hα : 0 ≤ α) :
    LogFourPoint (gaussianPowerFuture α) := by
  have hint (t : ℝ) : Integrable
      (fun r => thetaGaussianFuture (t + r) * causalPowerExp α (-1 / 2) r) := by
    have h := (integrable_indicator_iff (measurableSet_Ioi (a := (0 : ℝ)))).mpr
      (integrable_gaussianPowerFuture_integrand hα t)
    rw [gaussianPowerFuture_indicator] at h
    exact h
  have heq (t : ℝ) : (∫ r : ℝ,
      thetaGaussianFuture (t + r) * causalPowerExp α (-1 / 2) r) =
      gaussianPowerFuture α t := by
    rw [← gaussianPowerFuture_indicator, integral_indicator measurableSet_Ioi]
    rfl
  have h := logFourPoint_future_integral thetaGaussianFuture_four_point
    (causalPowerExp_four_point hα (-1 / 2)) hint
  simpa only [heq] using h

private theorem logFourPoint_mul_exponential {f : ℝ → ℝ} (hf : LogFourPoint f)
    (C c : ℝ) : LogFourPoint (fun t => C * Real.exp (c * t) * f t) := by
  intro x a b ha hb
  have he : Real.exp (c * x) * Real.exp (c * (x + a + b)) =
      Real.exp (c * (x + a)) * Real.exp (c * (x + b)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hw : 0 ≤ C ^ 2 * (Real.exp (c * x) * Real.exp (c * (x + a + b))) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  calc
    _ = (C ^ 2 * (Real.exp (c * x) * Real.exp (c * (x + a + b)))) *
        (f x * f (x + a + b)) := by ring
    _ ≤ (C ^ 2 * (Real.exp (c * x) * Real.exp (c * (x + a + b)))) *
        (f (x + a) * f (x + b)) := mul_le_mul_of_nonneg_left (hf x a b ha hb) hw
    _ = _ := by rw [he]; ring

/-- The original power-weighted integer Gaussian mass satisfies the global
four-point log-concavity inequality in logarithmic scale. -/
theorem integerGaussianMass_log_four_point {σ : ℝ} (hσ : 0 ≤ σ) :
    LogFourPoint (fun t => integerGaussianMass σ (Real.pi * Real.exp (2 * t))) := by
  have hα : 0 ≤ σ / 2 := div_nonneg hσ (by norm_num)
  have h := logFourPoint_mul_exponential (gaussianPowerFuture_four_point hα)
    (Real.pi ^ (σ / 2)) (2 * (σ / 2) - 1 / 2)
  have hid (t : ℝ) : (Real.pi ^ (σ / 2) * Real.exp ((2 * (σ / 2) - 1 / 2) * t)) *
      gaussianPowerFuture (σ / 2) t =
      Real.Gamma (σ / 2 + 1) * integerGaussianMass σ (Real.pi * Real.exp (2 * t)) := by
    rw [← gamma_mul_integerGaussianMass_eq_powerFuture hα]
    congr 2
    ring
  simp only [hid] at h
  intro x a b ha hb
  have hi := h x a b ha hb
  have hg : 0 < Real.Gamma (σ / 2 + 1) := Real.Gamma_pos_of_pos (by linarith)
  dsimp only at hi ⊢
  by_contra hbad
  have hp := mul_pos (sq_pos_of_pos hg) (sub_pos.mpr (lt_of_not_ge hbad))
  nlinarith only [hi, hp]

private theorem gaussian_scale_log_shift (t : ℝ) {a : ℝ} (ha : 0 < a) :
    Real.pi * Real.exp (2 * (t + Real.log a)) =
      a ^ 2 * (Real.pi * Real.exp (2 * t)) := by
  have he : Real.exp (2 * Real.log a) = a ^ 2 := by
    rw [show 2 * Real.log a = Real.log a + Real.log a by ring,
      Real.exp_add, Real.exp_log ha, pow_two]
  rw [mul_add, Real.exp_add, he]
  ring

/-- Multiplicative scale increments of the literal Gaussian mass are negatively
correlated, for arbitrary real dilation factors at least one. -/
theorem integerGaussianMass_scale_submultiplicative {σ y a b : ℝ}
    (hσ : 0 ≤ σ) (hy : 0 < y) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    integerGaussianMass σ y * integerGaussianMass σ (a ^ 2 * b ^ 2 * y) ≤
      integerGaussianMass σ (a ^ 2 * y) * integerGaussianMass σ (b ^ 2 * y) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hla : 0 ≤ Real.log a := by
    apply Real.exp_le_exp.mp
    simpa only [Real.exp_zero, Real.exp_log ha0] using ha
  have hlb : 0 ≤ Real.log b := by
    apply Real.exp_le_exp.mp
    simpa only [Real.exp_zero, Real.exp_log hb0] using hb
  have hbase : Real.pi * Real.exp (2 * (Real.log (y / Real.pi) / 2)) = y := by
    rw [show 2 * (Real.log (y / Real.pi) / 2) = Real.log (y / Real.pi) by ring,
      Real.exp_log (div_pos hy Real.pi_pos)]
    field_simp
  have hA := gaussian_scale_log_shift (Real.log (y / Real.pi) / 2) ha0
  have hB := gaussian_scale_log_shift (Real.log (y / Real.pi) / 2) hb0
  have hAB := gaussian_scale_log_shift (Real.log (y / Real.pi) / 2 + Real.log a) hb0
  rw [hA, hbase, show b ^ 2 * (a ^ 2 * y) = a ^ 2 * b ^ 2 * y by ring] at hAB
  rw [hbase] at hA hB
  have h := integerGaussianMass_log_four_point hσ
    (Real.log (y / Real.pi) / 2) (Real.log a) (Real.log b) hla hlb
  dsimp only at h
  rw [hbase, hA, hB, hAB] at h
  exact h

end

end RHTower.GaussianDivisibility
