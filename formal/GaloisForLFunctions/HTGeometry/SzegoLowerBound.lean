import Mathlib

/-!
# Szegő's inequality: the lower bound of the first Szegő limit theorem

For a weight `w > 0` on the unit circle and a function `p` analytic on the closed unit disk and
nonvanishing on the circle, the weighted circle mean of `‖p‖²` is bounded below by `‖p(0)‖²` times
the geometric mean `exp((2π)⁻¹∫ log w)` of the weight:

`‖p 0‖² · exp (circleAverage (log w)) ≤ circleAverage (‖p‖² · w)`.

This is the classical Szegő inequality `∫|p|² w ≥ |p(0)|² · GM(w)`, the lower-bound half of the
first Szegő limit theorem.  The proof combines the integral form of Jensen's inequality for the
convex exponential with the sub-mean-value property of `log ‖p‖` (a corollary of Jensen's formula),
both against the normalized angular probability measure `angleProb`.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Real Metric Complex intervalIntegral
open scoped Real ENNReal

noncomputable section

/-- The normalized angular probability measure `(2π)⁻¹ · dθ` on `(0, 2π]`. -/
noncomputable def angleProb : Measure ℝ :=
  (ENNReal.ofReal (2 * π))⁻¹ • volume.restrict (Set.Ioc 0 (2 * π))

instance : IsProbabilityMeasure angleProb := by
  constructor
  rw [angleProb, Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
    smul_eq_mul, ENNReal.inv_mul_cancel]
  · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  · exact ENNReal.ofReal_ne_top

/-- The circle average of `g` equals the integral of `θ ↦ g(e^{iθ})` against `angleProb`. -/
theorem circleAverage_eq_integral_angleProb (g : ℂ → ℝ) :
    circleAverage g 0 1 = ∫ θ, g (circleMap 0 1 θ) ∂angleProb := by
  rw [Real.circleAverage_def, intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2 * π),
    angleProb, MeasureTheory.integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by positivity)]

/-- A continuous function is integrable against the compactly supported measure `angleProb`. -/
theorem integrable_angleProb_of_continuous {F : ℝ → ℝ} (hF : Continuous F) :
    Integrable F angleProb := by
  have hIoc : Integrable F (volume.restrict (Set.Ioc 0 (2 * π))) :=
    (hF.continuousOn.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  rw [angleProb]
  refine hIoc.smul_measure ?_
  rw [ENNReal.inv_ne_top]
  exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'

/-- **Sub-mean-value inequality.**  For `f` analytic on the closed unit disk with `f 0 ≠ 0`, the
value `log‖f 0‖` at the centre is at most the circle average of `log‖f‖`.  This is the inequality
form of Jensen's formula: the counting term of the zeros inside the disk is non-negative. -/
theorem log_norm_center_le_circleAverage_log_norm
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (closedBall 0 |(1:ℝ)|)) (hf0 : f 0 ≠ 0) :
    Real.log ‖f 0‖ ≤ circleAverage (fun z => Real.log ‖f z‖) 0 1 := by
  have hkey := hf.circleAverage_log_norm (one_ne_zero) (by simpa using hf0)
  rw [hkey]
  have hdivpos := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf
  have hsum_nonneg : (0 : ℝ) ≤
      ∑ᶠ u, ((MeromorphicOn.divisor f (closedBall (0:ℂ) |(1:ℝ)|)) u : ℝ)
        * Real.log (1 * ‖(0:ℂ) - u‖⁻¹) := by
    apply finsum_nonneg
    intro u
    by_cases hu : u ∈ closedBall (0:ℂ) |(1:ℝ)|
    · have hdiv : (0:ℤ) ≤ (MeromorphicOn.divisor f (closedBall (0:ℂ) |(1:ℝ)|)) u := hdivpos u
      have hlog : 0 ≤ Real.log (1 * ‖(0:ℂ) - u‖⁻¹) := by
        rw [one_mul, zero_sub, norm_neg]
        rcases eq_or_ne (‖u‖) 0 with h0 | h0
        · simp [h0]
        · apply Real.log_nonneg
          rw [le_inv_comm₀ (by positivity) (by positivity)]
          have : ‖u‖ ≤ 1 := by simpa using (mem_closedBall_zero_iff.mp (by simpa using hu))
          simpa using this
      exact mul_nonneg (by exact_mod_cast hdiv) hlog
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]; simp
  linarith

/-- **Szegő's inequality** (the lower-bound half of the first Szegő limit theorem).  For `p`
analytic on the closed unit disk, nonvanishing on the unit circle, and a positive continuous
weight `w`, the weighted circle mean of `‖p‖²` dominates `‖p(0)‖²` times the geometric mean
`exp (circleAverage (log w))` of the weight.  Equivalently `∫|p|² w ≥ |p(0)|² · GM(w)`. -/
theorem szego_inequality
    (p : ℂ → ℂ) (hp : AnalyticOnNhd ℂ p (closedBall 0 |(1:ℝ)|)) (hp0 : p 0 ≠ 0)
    (hpc : ∀ θ : ℝ, p (circleMap 0 1 θ) ≠ 0)
    (w : ℂ → ℝ) (hwcont : Continuous (fun θ : ℝ => w (circleMap 0 1 θ)))
    (hwpos : ∀ θ : ℝ, 0 < w (circleMap 0 1 θ)) :
    ‖p 0‖ ^ 2 * Real.exp (circleAverage (fun z => Real.log (w z)) 0 1)
      ≤ circleAverage (fun z => ‖p z‖ ^ 2 * w z) 0 1 := by
  have hcm_mem : ∀ θ : ℝ, circleMap 0 1 θ ∈ closedBall (0:ℂ) |(1:ℝ)| := by
    intro θ; rw [mem_closedBall_zero_iff, norm_circleMap_zero]
  have hpc_cont : Continuous (fun θ : ℝ => p (circleMap 0 1 θ)) :=
    hp.continuousOn.comp_continuous (continuous_circleMap 0 1) hcm_mem
  set gpos : ℝ → ℝ := fun θ => ‖p (circleMap 0 1 θ)‖ ^ 2 * w (circleMap 0 1 θ) with hgdef
  have hgpos : ∀ θ, 0 < gpos θ := by
    intro θ; exact mul_pos (pow_pos (norm_pos_iff.mpr (hpc θ)) 2) (hwpos θ)
  have hg_cont : Continuous gpos := by
    rw [hgdef]; exact (hpc_cont.norm.pow 2).mul hwcont
  set h : ℝ → ℝ := fun θ => Real.log (gpos θ) with hhdef
  have hh_cont : Continuous h := hg_cont.log (fun θ => (hgpos θ).ne')
  have hexp_h : ∀ θ, Real.exp (h θ) = gpos θ := fun θ => Real.exp_log (hgpos θ)
  have hint_h : Integrable h angleProb := integrable_angleProb_of_continuous hh_cont
  have hint_exph : Integrable (fun θ => Real.exp (h θ)) angleProb :=
    integrable_angleProb_of_continuous (Real.continuous_exp.comp hh_cont)
  have hjensen : Real.exp (∫ θ, h θ ∂angleProb) ≤ ∫ θ, Real.exp (h θ) ∂angleProb :=
    convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hint_h hint_exph
  have hrhs : ∫ θ, Real.exp (h θ) ∂angleProb = circleAverage (fun z => ‖p z‖ ^ 2 * w z) 0 1 := by
    rw [circleAverage_eq_integral_angleProb]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with θ using hexp_h θ
  have hlogp_cont : Continuous (fun θ : ℝ => Real.log ‖p (circleMap 0 1 θ)‖) := by
    apply Continuous.log hpc_cont.norm
    intro θ; simpa using hpc θ
  have hlogw_cont : Continuous (fun θ : ℝ => Real.log (w (circleMap 0 1 θ))) :=
    hwcont.log (fun θ => (hwpos θ).ne')
  have hsplit : ∀ θ, h θ = 2 * Real.log ‖p (circleMap 0 1 θ)‖ + Real.log (w (circleMap 0 1 θ)) := by
    intro θ
    show Real.log (‖p (circleMap 0 1 θ)‖ ^ 2 * w (circleMap 0 1 θ))
      = 2 * Real.log ‖p (circleMap 0 1 θ)‖ + Real.log (w (circleMap 0 1 θ))
    rw [Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hpc θ))) (hwpos θ).ne', Real.log_pow]
    push_cast; ring
  have hlhs : ∫ θ, h θ ∂angleProb
      = 2 * circleAverage (fun z => Real.log ‖p z‖) 0 1
        + circleAverage (fun z => Real.log (w z)) 0 1 := by
    rw [circleAverage_eq_integral_angleProb (fun z => Real.log ‖p z‖),
      circleAverage_eq_integral_angleProb (fun z => Real.log (w z))]
    rw [show (fun θ => h θ) = (fun θ => 2 * Real.log ‖p (circleMap 0 1 θ)‖
        + Real.log (w (circleMap 0 1 θ))) from funext hsplit]
    rw [integral_add ((integrable_angleProb_of_continuous hlogp_cont).const_mul 2)
      (integrable_angleProb_of_continuous hlogw_cont), MeasureTheory.integral_const_mul]
  have hsub := log_norm_center_le_circleAverage_log_norm p hp hp0
  have hp0norm : (0:ℝ) < ‖p 0‖ := by simpa using hp0
  have hLHS_exp : ‖p 0‖ ^ 2 * Real.exp (circleAverage (fun z => Real.log (w z)) 0 1)
      = Real.exp (2 * Real.log ‖p 0‖ + circleAverage (fun z => Real.log (w z)) 0 1) := by
    rw [Real.exp_add]
    congr 1
    rw [show (2:ℝ) * Real.log ‖p 0‖ = Real.log (‖p 0‖ ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
  rw [hLHS_exp]
  calc Real.exp (2 * Real.log ‖p 0‖ + circleAverage (fun z => Real.log (w z)) 0 1)
      ≤ Real.exp (∫ θ, h θ ∂angleProb) := by
        apply Real.exp_le_exp.mpr
        rw [hlhs]; linarith [hsub]
    _ ≤ ∫ θ, Real.exp (h θ) ∂angleProb := hjensen
    _ = circleAverage (fun z => ‖p z‖ ^ 2 * w z) 0 1 := hrhs

/-- **Szegő's inequality, normalized form.**  For `p` analytic on the closed unit disk with
`p 0 = 1` and nonvanishing on the circle, the geometric mean `exp (circleAverage (log w))` of a
positive continuous weight `w` is at most the weighted circle mean of `‖p‖²`.  This is the sharp
lower bound `GM(w) ≤ ∫|p|² w` over normalized polynomials, and its infimum is the classical Szegő
constant. -/
theorem szego_inequality_normalized
    (p : ℂ → ℂ) (hp : AnalyticOnNhd ℂ p (closedBall 0 |(1:ℝ)|)) (hp0 : p 0 = 1)
    (hpc : ∀ θ : ℝ, p (circleMap 0 1 θ) ≠ 0)
    (w : ℂ → ℝ) (hwcont : Continuous (fun θ : ℝ => w (circleMap 0 1 θ)))
    (hwpos : ∀ θ : ℝ, 0 < w (circleMap 0 1 θ)) :
    Real.exp (circleAverage (fun z => Real.log (w z)) 0 1)
      ≤ circleAverage (fun z => ‖p z‖ ^ 2 * w z) 0 1 := by
  have h := szego_inequality p hp (by rw [hp0]; exact one_ne_zero) hpc w hwcont hwpos
  rwa [hp0, norm_one, one_pow, one_mul] at h

/-- **Szegő geometric mean of a Bernstein–Szegő weight.**  For `h` analytic and nonvanishing on
the closed unit disk, the geometric mean of the weight `w = |h|⁻²` is exactly `‖h(0)‖⁻²`.  This is
Jensen's formula for the nonvanishing analytic function `h`: `(2π)⁻¹∫ log|h| = log|h(0)|`. -/
theorem szego_geometricMean_bs (h : ℂ → ℂ) (hana : AnalyticOnNhd ℂ h (closedBall 0 1))
    (hnz : ∀ z ∈ closedBall (0 : ℂ) 1, h z ≠ 0) :
    Real.exp (circleAverage (fun z => Real.log ((‖h z‖ ^ 2)⁻¹)) 0 1) = (‖h 0‖ ^ 2)⁻¹ := by
  have h00 : h 0 ≠ 0 := hnz 0 (by simp)
  have hpos : (0 : ℝ) < ‖h 0‖ := norm_pos_iff.mpr h00
  rw [show (fun z => Real.log ((‖h z‖ ^ 2)⁻¹)) = (fun z => (-2 : ℝ) • Real.log ‖h z‖) from by
    funext z; rw [smul_eq_mul, Real.log_inv, Real.log_pow]; push_cast; ring]
  rw [circleAverage_fun_smul,
    AnalyticOnNhd.circleAverage_log_norm_of_ne_zero (by simpa using hana) (by simpa using hnz),
    smul_eq_mul,
    show (-2 : ℝ) * Real.log ‖h 0‖ = Real.log ((‖h 0‖ ^ 2)⁻¹) from by
      rw [Real.log_inv, Real.log_pow]; push_cast; ring,
    Real.exp_log (by positivity)]

/-- **Sharp Szegő lower bound for a Bernstein–Szegő weight.**  For `h` analytic and nonvanishing
on the closed unit disk and `p` analytic with `p(0) = 1` and nonvanishing on the circle, the
weighted circle mean of `‖p‖²` against `w = |h|⁻²` is at least the geometric mean `‖h(0)‖⁻²`.
Combining `szego_inequality_normalized` with `szego_geometricMean_bs`, the Szegő infimum for a
Bernstein–Szegő weight is bounded below by its geometric mean. -/
theorem szego_bs_lower (h : ℂ → ℂ) (hana : AnalyticOnNhd ℂ h (closedBall 0 1))
    (hnz : ∀ z ∈ closedBall (0 : ℂ) 1, h z ≠ 0)
    (p : ℂ → ℂ) (hp : AnalyticOnNhd ℂ p (closedBall 0 |(1:ℝ)|)) (hp0 : p 0 = 1)
    (hpc : ∀ θ : ℝ, p (circleMap 0 1 θ) ≠ 0) :
    (‖h 0‖ ^ 2)⁻¹ ≤ circleAverage (fun z => ‖p z‖ ^ 2 * (‖h z‖ ^ 2)⁻¹) 0 1 := by
  have hcm_mem : ∀ θ : ℝ, circleMap 0 1 θ ∈ closedBall (0 : ℂ) 1 := fun θ => by
    simp [Metric.mem_closedBall, dist_eq_norm]
  have hh_cont : Continuous (fun θ : ℝ => h (circleMap 0 1 θ)) :=
    hana.continuousOn.comp_continuous (continuous_circleMap 0 1) hcm_mem
  have hne : ∀ θ : ℝ, h (circleMap 0 1 θ) ≠ 0 := fun θ => hnz _ (hcm_mem θ)
  have hwcont : Continuous (fun θ : ℝ => ((‖h (circleMap 0 1 θ)‖ ^ 2)⁻¹ : ℝ)) :=
    (hh_cont.norm.pow 2).inv₀ (fun θ => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne θ)))
  have hwpos : ∀ θ : ℝ, (0 : ℝ) < (‖h (circleMap 0 1 θ)‖ ^ 2)⁻¹ := fun θ =>
    inv_pos.mpr (pow_pos (norm_pos_iff.mpr (hne θ)) 2)
  have hineq := szego_inequality_normalized p hp hp0 hpc
    (fun z => (‖h z‖ ^ 2)⁻¹) hwcont hwpos
  rwa [szego_geometricMean_bs h hana hnz] at hineq

end

end GaloisForLFunctions.HTGeometry
