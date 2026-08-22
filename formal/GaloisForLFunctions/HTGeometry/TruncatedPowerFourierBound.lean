import GaloisForLFunctions.HTGeometry.OscillatoryPowerIntegral
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# The Fourier transform of a truncated power, and its uniform decay

For `0 < T ≤ T'` and `Re s > 0` let

`w_{T,T'}^s := 1_{(T,T')}(t) · t^{-s}`.

This is a bounded, compactly supported function, hence lies in `L¹ ∩ L²`, and its Fourier integral
is exactly the oscillatory power integral of `OscillatoryPowerIntegral`:

`𝓕 w(u) = ∫_T^{T'} e^{-2πiut} t^{-s} dt`.

One integration by parts therefore gives the decay

`‖𝓕 w(u)‖ ≤ (2 T^{-Re s} + ‖s‖ T^{-Re s}/Re s) / (2π|u|)`,

**uniform in the outer truncation `T'`** and with a constant that tends to `0` as `T → ∞`.  This is
the estimate that makes the truncated Mellin transforms of a Sonine function a locally uniform
Cauchy family across the critical line (Burnol, arXiv:math/0203120, Thm. 2.1 route).

## Main results

* `integrable_truncPower`, `memLp_two_truncPower`
* `fourierIntegral_truncPower`
* `norm_fourierIntegral_truncPower_le`
-/

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory Set Real FourierTransform

noncomputable section

/-- The truncated power `1_{(T,T')}(t) · t^{-s}` on the real line. -/
def truncPower (T T' : ℝ) (s : ℂ) : ℝ → ℂ :=
  (Set.Ioo T T').indicator fun t => ((t : ℝ) : ℂ) ^ (-s)

theorem continuousOn_ofReal_cpow_neg_Ici {T : ℝ} (hT : 0 < T) (s : ℂ) :
    ContinuousOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s)) (Set.Ici T) := by
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le hT ht
  exact (Complex.continuousAt_ofReal_cpow_const t (-s)
    (Or.inr (ne_of_gt htpos))).continuousWithinAt

theorem norm_ofReal_cpow_neg_le {T t : ℝ} (hT : 0 < T) (hTt : T ≤ t) {s : ℂ} (hs : 0 < s.re) :
    ‖((t : ℝ) : ℂ) ^ (-s)‖ ≤ T ^ (-s.re) := by
  have htpos : 0 < t := lt_of_lt_of_le hT hTt
  rw [Complex.norm_cpow_eq_rpow_re_of_pos htpos, Complex.neg_re]
  rw [Real.rpow_def_of_pos htpos, Real.rpow_def_of_pos hT]
  refine Real.exp_le_exp.2 ?_
  have hlog : Real.log T ≤ Real.log t := Real.log_le_log hT hTt
  nlinarith [mul_nonneg (sub_nonneg.2 hlog) hs.le]

theorem memLp_restrict_ofReal_cpow {T T' : ℝ} (hT : 0 < T) {s : ℂ} (hs : 0 < s.re) :
    MemLp (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s)) 2
      ((volume : Measure ℝ).restrict (Set.Ioo T T')) := by
  haveI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Ioo T T')) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_Ioo_lt_top
  refine MemLp.of_bound ?_ (T ^ (-s.re)) ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    exact (continuousOn_ofReal_cpow_neg_Ici hT s).mono (fun t ht => le_of_lt ht.1)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact norm_ofReal_cpow_neg_le hT (le_of_lt ht.1) hs

theorem memLp_two_truncPower {T T' : ℝ} (hT : 0 < T) {s : ℂ} (hs : 0 < s.re) :
    MemLp (truncPower T T' s) 2 volume := by
  rw [truncPower, memLp_indicator_iff_restrict measurableSet_Ioo]
  exact memLp_restrict_ofReal_cpow hT hs

theorem integrable_truncPower {T T' : ℝ} (hT : 0 < T) {s : ℂ} (hs : 0 < s.re) :
    Integrable (truncPower T T' s) volume := by
  rw [truncPower, integrable_indicator_iff measurableSet_Ioo]
  exact (memLp_restrict_ofReal_cpow hT hs).integrable (by norm_num)

theorem fourierIntegral_truncPower {T T' : ℝ} (hTT' : T ≤ T') (s : ℂ) (u : ℝ) :
    𝓕 (truncPower T T' s) u = oscPowerIntegral T T' s (-(2 * π * u)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hstep : (∫ v : ℝ, Complex.exp ((↑(-2 * π * v * u)) * Complex.I) • truncPower T T' s v)
      = ∫ v in Set.Ioo T T', Complex.exp ((↑(-2 * π * v * u)) * Complex.I) *
          ((v : ℝ) : ℂ) ^ (-s) := by
    rw [truncPower]
    rw [← MeasureTheory.integral_indicator measurableSet_Ioo]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    by_cases hv : v ∈ Set.Ioo T T'
    · simp only [Set.indicator_of_mem hv, smul_eq_mul]
    · simp only [Set.indicator_of_notMem hv, smul_zero]
  rw [hstep, oscPowerIntegral, intervalIntegral.integral_of_le hTT',
    integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun v _ => ?_
  congr 2
  push_cast
  ring

theorem norm_fourierIntegral_truncPower_le {T T' : ℝ} (hT : 0 < T) (hTT' : T ≤ T') {s : ℂ}
    (hs : 0 < s.re) {u : ℝ} (hu : u ≠ 0) :
    ‖𝓕 (truncPower T T' s) u‖ ≤
      (2 * T ^ (-s.re) + ‖s‖ * T ^ (-s.re) / s.re) / (2 * π * |u|) := by
  have hlne : (-(2 * π * u)) ≠ 0 := by
    have hpi : (0 : ℝ) < π := Real.pi_pos
    intro h
    apply hu
    have : 2 * π * u = 0 := by linarith [neg_eq_zero.1 h]
    have h2 : (2 : ℝ) * π ≠ 0 := by positivity
    exact (mul_eq_zero.1 this).resolve_left h2
  have habs : |(-(2 * π * u))| = 2 * π * |u| := by
    rw [abs_neg, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
  rw [fourierIntegral_truncPower hTT' s u]
  have := norm_oscPowerIntegral_le hT hTT' hs hlne
  rwa [habs] at this

end

end GaloisForLFunctions.HTGeometry
