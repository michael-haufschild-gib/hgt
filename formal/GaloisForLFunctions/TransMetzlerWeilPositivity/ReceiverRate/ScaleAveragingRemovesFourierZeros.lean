import GaloisForLFunctions.HTGeometry.InterfinityGeometry.ParametricSmoothness
import GaloisForLFunctions.TransMetzlerWeilPositivity.ReceiverRate.TheSincProfileHasAnExactCriticalOverlap

/-!
# Scale averages of autocorrelations

Averaging normalized dilations over scales `[1,2]` turns an autocorrelation's
Fourier transform into a band average of the original squared transform.
Thus an integrated Fourier lower bound yields a pointwise lower bound.
The substitution `s = 1 + t²` keeps the averaging integrand globally smooth.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff FourierTransform

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open SpacingScaleHarmonicAnalysis

private theorem hasDerivAt_paramAvg_of_smooth {F D : ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (x : ℝ)
    (hD : ∀ t, HasDerivAt (fun y => F y t) (D x t) x) :
    HasDerivAt (HTGeometry.Interfinity.paramAvg F)
      (∫ t in (0 : ℝ)..1, D x t) x := by
  have hF1 := hF.of_le (natCast_le_infty 1)
  have hI := ((HTGeometry.Interfinity.continuous_partialFderiv hF1).comp
    (Continuous.prodMk_right x)).intervalIntegrable (0 : ℝ) 1
  have hd := (HTGeometry.Interfinity.hasFDerivAt_paramAvg hF1 x).hasDerivAt
  rw [ContinuousLinearMap.intervalIntegral_apply hI] at hd
  convert hd using 1
  apply intervalIntegral.integral_congr
  intro t _
  exact (hD t).unique (HTGeometry.Interfinity.hasFDerivAt_partial hF1 x t).hasDerivAt

/-- The average of mass-preserving dilations over scales from one to two. -/
def scaleAverage (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, 2 * t / (1 + t ^ 2) * f (x / (1 + t ^ 2))

private theorem contDiff_scaleAverage_integrand {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      2 * p.2 / (1 + p.2 ^ 2) * f (p.1 / (1 + p.2 ^ 2))) := by
  have hd : ContDiff ℝ ∞ (fun p : ℝ × ℝ => 1 + p.2 ^ 2) :=
    contDiff_const.add (contDiff_snd.pow 2)
  have hn : ∀ p : ℝ × ℝ, (1 : ℝ) + p.2 ^ 2 ≠ 0 := fun p => by positivity
  exact ((contDiff_const.mul contDiff_snd).div hd hn).mul
    (hf.comp (contDiff_fst.div hd hn))

theorem contDiff_scaleAverage {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (scaleAverage f) := by
  rw [contDiff_infty]
  intro k
  exact HTGeometry.Interfinity.contDiff_paramAvg k
    ((contDiff_scaleAverage_integrand hf).of_le (natCast_le_infty k))

private theorem contDiff_scaleAverage_derivative_integrand {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (q : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      2 * p.2 / (1 + p.2 ^ 2) ^ (q + 1) * iteratedDeriv q f (p.1 / (1 + p.2 ^ 2))) := by
  have hd : ContDiff ℝ ∞ (fun p : ℝ × ℝ => 1 + p.2 ^ 2) :=
    contDiff_const.add (contDiff_snd.pow 2)
  have hn : ∀ p : ℝ × ℝ, (1 : ℝ) + p.2 ^ 2 ≠ 0 := fun p => by positivity
  have hfq : ContDiff ℝ ∞ (iteratedDeriv q f) := by
    rw [iteratedDeriv_eq_iterate]
    exact hf.iterate_deriv q
  exact ((contDiff_const.mul contDiff_snd).div (hd.pow _) (fun p => pow_ne_zero _ (hn p))).mul
    (hfq.comp (contDiff_fst.div hd hn))

/-- Each derivative pays an additional inverse dilation factor. -/
theorem iteratedDeriv_scaleAverage {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (q : ℕ) :
    iteratedDeriv q (scaleAverage f) = fun x =>
      ∫ t in (0 : ℝ)..1,
        2 * t / (1 + t ^ 2) ^ (q + 1) * iteratedDeriv q f (x / (1 + t ^ 2)) := by
  induction q with
  | zero => simp only [iteratedDeriv_zero, zero_add, pow_one, scaleAverage]
  | succ q ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    apply HasDerivAt.deriv
    apply hasDerivAt_paramAvg_of_smooth (contDiff_scaleAverage_derivative_integrand hf q) x
    intro t
    have hfq : Differentiable ℝ (iteratedDeriv q f) :=
      hf.differentiable_iteratedDeriv q (by exact_mod_cast ENat.coe_lt_top q)
    have hd := ((hfq (x / (1 + t ^ 2))).hasDerivAt.comp x
      ((hasDerivAt_id x).div_const (1 + t ^ 2))).const_mul
        (2 * t / (1 + t ^ 2) ^ (q + 1))
    convert hd using 1
    rw [iteratedDeriv_succ, pow_succ]
    field_simp [show (1 : ℝ) + t ^ 2 ≠ 0 by positivity]

theorem abs_iteratedDeriv_scaleAverage_le {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (q : ℕ) {B : ℝ} (hB : ∀ x, |iteratedDeriv q f x| ≤ B) (x : ℝ) :
    |iteratedDeriv q (scaleAverage f) x| ≤ 2 * B := by
  rw [iteratedDeriv_scaleAverage hf, ← Real.norm_eq_abs]
  have hb : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖2 * t / (1 + t ^ 2) ^ (q + 1) * iteratedDeriv q f (x / (1 + t ^ 2))‖ ≤ 2 * B := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hd : 1 ≤ (1 + t ^ 2) ^ (q + 1) := one_le_pow₀ (by nlinarith only [sq_nonneg t])
    have hc0 : 0 ≤ 2 * t / (1 + t ^ 2) ^ (q + 1) := by positivity
    have hc : 2 * t / (1 + t ^ 2) ^ (q + 1) ≤ 2 := by
      rw [div_le_iff₀ (zero_lt_one.trans_le hd)]
      nlinarith only [ht.2, hd]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hc0]
    exact mul_le_mul hc (hB _) (abs_nonneg _) (by norm_num)
  simpa only [sub_zero, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const hb

theorem scaleAverage_nonneg {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (x : ℝ) :
    0 ≤ scaleAverage f x := by
  apply intervalIntegral.integral_nonneg zero_le_one
  intro t ht
  exact mul_nonneg (div_nonneg (mul_nonneg zero_le_two ht.1) (by positivity)) (hf _)

theorem scaleAverage_vanishesOff {f : ℝ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hf : ∀ x, R < |x| → f x = 0) :
    ∀ x, 2 * R < |x| → scaleAverage f x = 0 := by
  intro x hx
  apply intervalIntegral.integral_eq_zero_of_forall_mem_uIcc_eq_zero
  intro t ht
  rw [Set.uIcc_of_le zero_le_one] at ht
  have ht2 : t ^ 2 ≤ 1 := by nlinarith only [ht.1, ht.2]
  have hd : 0 < (1 : ℝ) + t ^ 2 := by positivity
  have hb : R < |x / (1 + t ^ 2)| := by
    rw [abs_div, abs_of_pos hd, lt_div_iff₀ hd]
    exact (mul_le_mul_of_nonneg_left (by linarith only [ht2] : 1 + t ^ 2 ≤ 2) hR).trans_lt
      (by linarith only [hx])
  rw [hf _ hb, mul_zero]

/-- Averaging a spectral density over dilations. -/
def scaleBandAverage (F : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, 2 * t * F ((1 + t ^ 2) * ξ)

/-- The quadratic substitution converts the scale average into a frequency band. -/
theorem mul_scaleBandAverage (F : ℝ → ℝ) (hF : Continuous F) (ξ : ℝ) :
    ξ * scaleBandAverage F ξ = ∫ u in ξ..2 * ξ, F u := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => (1 + s ^ 2) * ξ) (2 * t * ξ) t := by
    convert (((hasDerivAt_id t).pow 2).const_add 1).mul_const ξ using 1 <;> ring
  have hsub := intervalIntegral.integral_comp_mul_deriv
    (a := (0 : ℝ)) (b := 1) (fun t _ => hd t)
    (by fun_prop : ContinuousOn (fun t : ℝ => 2 * t * ξ) (Set.uIcc 0 1)) hF
  calc ξ * scaleBandAverage F ξ
      = ∫ t in (0 : ℝ)..1, F ((1 + t ^ 2) * ξ) * (2 * t * ξ) := by
        rw [scaleBandAverage, ← intervalIntegral.integral_const_mul]
        congr 1
        funext t
        ring
    _ = ∫ u in ξ..2 * ξ, F u := by
      simpa only [Function.comp_def, zero_pow (by decide : 2 ≠ 0), add_zero,
        one_mul, one_pow, one_add_one_eq_two] using hsub

/-- The sinc profile's integrated lower bound becomes a pointwise bound after scale averaging. -/
theorem eventually_scaleBandAverage_sinc_ge :
    ∀ᶠ ξ : ℝ in atTop,
      Real.exp (-(sincTailConst * (ξ / Real.log ξ ^ 2))) ≤
        scaleBandAverage (fun u => ‖𝓕 (fun x => (sincProfile x : ℂ)) u‖ ^ 2) ξ := by
  filter_upwards [exp_mul_le_integral_norm_fourier_sincProfile_sq,
    eventually_gt_atTop (0 : ℝ)] with ξ hξ hpos
  apply (mul_le_mul_iff_right₀ hpos).mp
  rw [mul_scaleBandAverage _ (continuous_norm_fourier_sincProfile.pow 2)]
  exact hξ

end GaloisForLFunctions.TransMetzlerWeilPositivity
