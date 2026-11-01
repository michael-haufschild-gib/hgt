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
  have hI : IntervalIntegrable (HTGeometry.Interfinity.partialFderiv F x) volume 0 1 :=
    ((HTGeometry.Interfinity.continuous_partialFderiv hF1).comp
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
  | zero => simp only [iteratedDeriv_zero, zero_add, pow_one]; rfl
  | succ q ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    apply HasDerivAt.deriv
    apply hasDerivAt_paramAvg_of_smooth
      (F := fun y t => 2 * t / (1 + t ^ 2) ^ (q + 1) *
        iteratedDeriv q f (y / (1 + t ^ 2)))
      (D := fun y t => 2 * t / (1 + t ^ 2) ^ (q + 1 + 1) *
        iteratedDeriv (q + 1) f (y / (1 + t ^ 2)))
      (contDiff_scaleAverage_derivative_integrand hf q) x
    intro t
    have hfq : Differentiable ℝ (iteratedDeriv q f) :=
      hf.differentiable_iteratedDeriv q (by exact_mod_cast ENat.coe_lt_top q)
    have hd := ((hfq (x / (1 + t ^ 2))).hasDerivAt.comp x
      ((hasDerivAt_id x).div_const (1 + t ^ 2))).const_mul
        (2 * t / (1 + t ^ 2) ^ (q + 1))
    have he : 2 * t / (1 + t ^ 2) ^ (q + 1) *
        (deriv (iteratedDeriv q f) (x / (1 + t ^ 2)) * (1 / (1 + t ^ 2))) =
        2 * t / (1 + t ^ 2) ^ (q + 1 + 1) *
          iteratedDeriv (q + 1) f (x / (1 + t ^ 2)) := by
      rw [iteratedDeriv_succ, pow_succ]
      field_simp [show (1 : ℝ) + t ^ 2 ≠ 0 by positivity]
    simpa only [Function.comp_def, id_eq, he] using hd

theorem abs_iteratedDeriv_scaleAverage_le {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (q : ℕ) {B : ℝ} (hB : ∀ x, |iteratedDeriv q f x| ≤ B) (x : ℝ) :
    |iteratedDeriv q (scaleAverage f) x| ≤ 2 * B := by
  rw [iteratedDeriv_scaleAverage hf, ← Real.norm_eq_abs]
  have hb : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖2 * t / (1 + t ^ 2) ^ (q + 1) * iteratedDeriv q f (x / (1 + t ^ 2))‖ ≤ 2 * B := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hd : 1 ≤ (1 + t ^ 2) ^ (q + 1) := one_le_pow₀ (by nlinarith only [sq_nonneg t])
    have hc0 : 0 ≤ 2 * t / (1 + t ^ 2) ^ (q + 1) :=
      div_nonneg (mul_nonneg zero_le_two ht.1.le) (zero_lt_one.trans_le hd).le
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
  have heq : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      2 * t / (1 + t ^ 2) * f (x / (1 + t ^ 2)) = 0 := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have ht2 : t ^ 2 ≤ 1 := by nlinarith only [ht.1, ht.2]
    have hd : 0 < (1 : ℝ) + t ^ 2 := by positivity
    have hb : R < |x / (1 + t ^ 2)| := by
      rw [abs_div, abs_of_pos hd, lt_div_iff₀ hd]
      exact (mul_le_mul_of_nonneg_left (by linarith only [ht2] : 1 + t ^ 2 ≤ 2) hR).trans_lt
        (by linarith only [hx])
    rw [hf _ hb, mul_zero]
  rw [scaleAverage, intervalIntegral.integral_congr heq, intervalIntegral.integral_zero]

/-- Averaging a spectral density over dilations. -/
def scaleBandAverage (F : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, 2 * t * F ((1 + t ^ 2) * ξ)

/-- The quadratic substitution converts the scale average into a frequency band. -/
theorem mul_scaleBandAverage (F : ℝ → ℝ) (hF : Continuous F) (ξ : ℝ) :
    ξ * scaleBandAverage F ξ = ∫ u in ξ..2 * ξ, F u := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => (1 + s ^ 2) * ξ) (2 * t * ξ) t := by
    simpa only [Nat.cast_ofNat, pow_one, mul_one] using
      (((hasDerivAt_id t).pow 2).const_add 1).mul_const ξ
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
  have hc : Continuous (fun u => ‖𝓕 (fun x => (sincProfile x : ℂ)) u‖ ^ 2) :=
    continuous_norm_fourier_sincProfile.pow 2
  apply (mul_le_mul_iff_right₀ hpos).mp
  rw [mul_scaleBandAverage _ hc]
  exact hξ

/-- Fourier transformation commutes with the normalized dilation average. -/
theorem fourier_scaleAverage {f : ℝ → ℝ} (hf : Continuous f) (hfi : Integrable f) (ξ : ℝ) :
    𝓕 (fun x => (scaleAverage f x : ℂ)) ξ =
      ∫ t in (0 : ℝ)..1, (2 * t : ℝ) * 𝓕 (fun x => (f x : ℂ)) ((1 + t ^ 2) * ξ) := by
  let F : ℝ → ℝ → ℂ := fun t x =>
    (Real.fourierChar (-(x * ξ)) : ℂ) *
      ((2 * t / (1 + t ^ 2) : ℝ) * (f (x / (1 + t ^ 2)) : ℂ))
  have hd (t : ℝ) : 0 < (1 : ℝ) + t ^ 2 := by positivity
  have hscale (t : ℝ) : Integrable (fun x => f (x / (1 + t ^ 2))) := by
    simpa only [div_eq_mul_inv] using hfi.comp_mul_right' (inv_ne_zero (hd t).ne')
  have hFc : Continuous (Function.uncurry F) := by
    dsimp only [F, Function.uncurry]
    fun_prop (disch := positivity)
  have hnorm (t x : ℝ) : ‖F t x‖ =
      |2 * t / (1 + t ^ 2)| * |f (x / (1 + t ^ 2))| := by
    simp only [F, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hslice (t : ℝ) : Integrable (F t) := by
    refine Integrable.mono' ((hscale t).abs.const_mul |2 * t / (1 + t ^ 2)|)
      ((hFc.comp (Continuous.prodMk_right t)).aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun x => (hnorm t x).le
  have hmass (t : ℝ) :
      (∫ x, ‖F t x‖) = |2 * t / (1 + t ^ 2)| * ((1 + t ^ 2) * ∫ x, |f x|) := by
    simp_rw [hnorm]
    rw [integral_const_mul]
    congr 1
    have hh := Measure.integral_comp_mul_left (fun x => |f x|) (1 + t ^ 2)⁻¹
    simpa only [inv_inv, abs_of_pos (hd t), smul_eq_mul, div_eq_mul_inv, mul_comm]
      using hh
  have hprod : Integrable (Function.uncurry F)
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod volume) := by
    rw [integrable_prod_iff hFc.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall hslice, ?_⟩
    simp_rw [hmass]
    rw [Set.uIoc_of_le zero_le_one]
    have hc : Continuous (fun t : ℝ =>
        |2 * t / (1 + t ^ 2)| * ((1 + t ^ 2) * ∫ x, |f x|)) := by
      fun_prop (disch := positivity)
    exact (hc.intervalIntegrable (0 : ℝ) 1).1
  have hinner (t : ℝ) : (∫ x, F t x) =
      (2 * t : ℝ) * 𝓕 (fun x => (f x : ℂ)) ((1 + t ^ 2) * ξ) := by
    have hFT := HTGeometry.fourier_comp_mul_pos (inv_pos.mpr (hd t))
      (fun x => (f x : ℂ)) ξ
    have heq : (fun x : ℝ => (f (x / (1 + t ^ 2)) : ℂ)) =
        fun x => (f ((1 + t ^ 2)⁻¹ * x) : ℂ) := by
      funext x
      rw [div_eq_mul_inv, mul_comm]
    calc (∫ x, F t x)
        = ((2 * t / (1 + t ^ 2) : ℝ) : ℂ) *
          𝓕 (fun x => (f (x / (1 + t ^ 2)) : ℂ)) ξ := by
            rw [Real.fourier_real_eq, ← integral_const_mul]
            apply integral_congr_ae
            apply Filter.Eventually.of_forall
            intro x
            simp only [F, Circle.smul_def, smul_eq_mul]
            ring
      _ = (2 * t : ℝ) * 𝓕 (fun x => (f x : ℂ)) ((1 + t ^ 2) * ξ) := by
        rw [heq, hFT, div_inv_eq_mul, mul_comm ξ]
        push_cast
        field_simp [Complex.ofReal_ne_zero.mpr (hd t).ne']
  calc 𝓕 (fun x => (scaleAverage f x : ℂ)) ξ = ∫ x, ∫ t in (0 : ℝ)..1, F t x := by
      rw [Real.fourier_real_eq]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      simp only [scaleAverage, Circle.smul_def, smul_eq_mul]
      rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      simp only [F, Complex.ofReal_mul]
    _ = ∫ t in (0 : ℝ)..1, ∫ x, F t x := (intervalIntegral_integral_swap hprod).symm
    _ = ∫ t in (0 : ℝ)..1,
        (2 * t : ℝ) * 𝓕 (fun x => (f x : ℂ)) ((1 + t ^ 2) * ξ) := by
      simp_rw [hinner]

end GaloisForLFunctions.TransMetzlerWeilPositivity
