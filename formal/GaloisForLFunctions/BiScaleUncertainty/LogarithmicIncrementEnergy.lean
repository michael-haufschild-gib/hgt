import GaloisForLFunctions.BiScaleUncertainty.InfiniteGridTailRigidity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Logarithmic control of translation increments by Levy energy

Integrating the translation chord inequality against a decreasing singular kernel
controls each translation increment by its logarithmic cost. The resulting estimate
does not use a derivative moment. A separated copy preserving its distant logarithmic
sample must pay energy proportional to its separation.
-/

open MeasureTheory Set Filter Topology
open scoped CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

theorem antitoneOn_archLevySinhWeight : AntitoneOn archLevySinhWeight (Ioi 0) := by
  intro a ha b hb hab
  simp only [archLevySinhWeight]
  rw [exp_half_div_sinh_eq ha, exp_half_div_sinh_eq hb]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  unfold RHTower.archLevyDensity
  have hd : 0 < 1 - Real.exp (-2 * a) := by
    have := Real.exp_lt_one_iff.mpr (show -2 * a < 0 by linarith [mem_Ioi.mp ha])
    linarith
  have hdd : 1 - Real.exp (-2 * a) ≤ 1 - Real.exp (-2 * b) := by
    have := Real.exp_le_exp.mpr (show -2 * b ≤ -2 * a by linarith)
    linarith
  exact div_le_div₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr (by linarith)) hd hdd

theorem continuousOn_archLevySinhWeight_Ioi : ContinuousOn archLevySinhWeight (Ioi 0) := by
  exact (Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn.div
    Real.continuous_sinh.continuousOn fun x hx => (Real.sinh_pos_iff.mpr hx).ne'

theorem intervalIntegrable_biScaleLevyIntegrand {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun x => (autocorr f 0 - autocorr f x) * archLevySinhWeight x)
      volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
  exact (integrableOn_biScaleLevyIntegrand hf hfc).mono_set fun x hx => lt_of_le_of_lt ha hx.1

theorem interval_biScaleLevyIntegrand_le {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ x in a..b, (autocorr f 0 - autocorr f x) * archLevySinhWeight x) ≤
      biScaleLevyEnergy f := by
  rw [intervalIntegral.integral_of_le hab]
  apply setIntegral_mono_set (integrableOn_biScaleLevyIntegrand hf hfc)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (autocorr_sub_nonneg hfc hf.continuous x) (archLevySinhWeight_pos hx).le
  · exact Eventually.of_forall fun x hx => lt_of_le_of_lt ha hx.1

theorem interval_biScaleLevyIntegrand_le_initial {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {a b c : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    (∫ x in a..b, (autocorr f 0 - autocorr f x) * archLevySinhWeight x) ≤
      ∫ x in (0 : ℝ)..c, (autocorr f 0 - autocorr f x) * archLevySinhWeight x := by
  rw [intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le (ha.trans (hab.trans hbc))]
  apply setIntegral_mono_set
    ((integrableOn_biScaleLevyIntegrand hf hfc).mono_set (fun x hx => hx.1 : Ioc 0 c ⊆ Ioi 0))
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact mul_nonneg (autocorr_sub_nonneg hfc hf.continuous x) (archLevySinhWeight_pos hx.1).le
  · exact Eventually.of_forall fun x hx => ⟨lt_of_le_of_lt ha hx.1, hx.2.trans hbc⟩

/-- A pointwise translation defect is controlled by the Levy energy below the cutoff itself. -/
theorem autocorr_increment_mul_weight_integral_le_local {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {δ b : ℝ}
    (hδ : 0 < δ) (hδb : δ ≤ b) :
    (autocorr f 0 - autocorr f δ) * (∫ x in δ..b, archLevySinhWeight x) ≤
      4 * ∫ x in (0 : ℝ)..b, (autocorr f 0 - autocorr f x) * archLevySinhWeight x := by
  let F : ℝ → ℝ := fun x => (autocorr f 0 - autocorr f x) * archLevySinhWeight x
  have hi : IntervalIntegrable F volume δ b :=
    intervalIntegrable_biScaleLevyIntegrand hf hfc hδ.le hδb
  have hi0 : IntervalIntegrable F volume 0 (b - δ) :=
    intervalIntegrable_biScaleLevyIntegrand hf hfc le_rfl (sub_nonneg.mpr hδb)
  have his : IntervalIntegrable (fun x => F (x - δ)) volume δ b := by
    simpa only [zero_add, sub_add_cancel] using hi0.comp_sub_right δ
  have hw : IntervalIntegrable archLevySinhWeight volume δ b := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_archLevySinhWeight_Ioi.mono
    rw [uIcc_of_le hδb]
    exact fun x hx => lt_of_lt_of_le hδ hx.1
  have hbound :
      (∫ x in δ..b, (autocorr f 0 - autocorr f δ) * archLevySinhWeight x) ≤
        ∫ x in δ..b, 2 * F x + 2 * F (x - δ) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hδb (hw.const_mul _)
      ((hi.const_mul 2).add (his.const_mul 2))
    intro x hx
    have hx0 : 0 < x := lt_trans hδ hx.1
    have hxd : 0 < x - δ := sub_pos.mpr hx.1
    have hchord := autocorr_sub_add_le hfc hf.continuous x (δ - x)
    rw [show x + (δ - x) = δ by ring,
      show δ - x = -(x - δ) by ring, autocorr_neg] at hchord
    have hwle : archLevySinhWeight x ≤ archLevySinhWeight (x - δ) :=
      antitoneOn_archLevySinhWeight hxd hx0 (by linarith)
    have hp := mul_le_mul_of_nonneg_right hchord (archLevySinhWeight_pos hx0).le
    have hq := mul_le_mul_of_nonneg_left hwle (autocorr_sub_nonneg hfc hf.continuous (x - δ))
    dsimp only [F]
    nlinarith
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hi.const_mul 2) (his.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right, sub_self] at hbound
  have h1 := interval_biScaleLevyIntegrand_le_initial hf hfc hδ.le hδb (le_refl b)
  have h2 := interval_biScaleLevyIntegrand_le_initial hf hfc le_rfl (sub_nonneg.mpr hδb)
    (show b - δ ≤ b by linarith)
  dsimp only [F] at hbound
  linarith

/-- A pointwise translation defect consumes four times the total Levy energy at most,
when weighted by the kernel mass between its displacement and any larger cutoff. -/
theorem autocorr_increment_mul_weight_integral_le {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {δ b : ℝ}
    (hδ : 0 < δ) (hδb : δ ≤ b) :
    (autocorr f 0 - autocorr f δ) * (∫ x in δ..b, archLevySinhWeight x) ≤
      4 * biScaleLevyEnergy f := by
  have h := autocorr_increment_mul_weight_integral_le_local hf hfc hδ hδb
  have he := interval_biScaleLevyIntegrand_le hf hfc le_rfl (hδ.le.trans hδb)
  linarith

theorem exp_neg_half_div_le_archLevySinhWeight {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    Real.exp (-(1 / 2 : ℝ)) / x ≤ archLevySinhWeight x := by
  have hd : 0 < 1 - Real.exp (-2 * x) := by
    have := Real.exp_lt_one_iff.mpr (show -2 * x < 0 by linarith)
    linarith
  have hdx : 1 - Real.exp (-2 * x) ≤ 2 * x := by
    linarith [Real.add_one_le_exp (-2 * x)]
  have hb := div_le_div_of_nonneg_left (Real.exp_pos (-x / 2)).le hd hdx
  have hc := Real.exp_le_exp.mpr (show -(1 / 2 : ℝ) ≤ -x / 2 by linarith)
  calc
    _ ≤ Real.exp (-x / 2) / x := div_le_div_of_nonneg_right hc hx.le
    _ = 2 * (Real.exp (-x / 2) / (2 * x)) := by ring
    _ ≤ 2 * (Real.exp (-x / 2) / (1 - Real.exp (-2 * x))) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = archLevySinhWeight x := by
      rw [archLevySinhWeight, exp_half_div_sinh_eq hx]
      rfl

/-- Uniform logarithmic control of the translation increment by the full Levy energy. -/
theorem autocorr_increment_mul_log_le {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.exp (-(1 / 2 : ℝ)) * (autocorr f 0 - autocorr f δ) * (-Real.log δ) ≤
      4 * biScaleLevyEnergy f := by
  have hw : IntervalIntegrable archLevySinhWeight volume δ 1 := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_archLevySinhWeight_Ioi.mono
    rw [uIcc_of_le hδ1]
    exact fun x hx => lt_of_lt_of_le hδ hx.1
  have hinv : IntervalIntegrable (fun x : ℝ => 1 / x) volume δ 1 := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div continuousOn_id
    intro x hx
    rw [uIcc_of_le hδ1] at hx
    exact (lt_of_lt_of_le hδ hx.1).ne'
  have hb := intervalIntegral.integral_mono_on hδ1 (hinv.const_mul (Real.exp (-(1 / 2 : ℝ)))) hw
    (fun x hx => by simpa only [mul_one_div] using
      exp_neg_half_div_le_archLevySinhWeight (lt_of_lt_of_le hδ hx.1) hx.2)
  rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos hδ zero_lt_one] at hb
  simp only [one_div, Real.log_inv] at hb
  have hmul := mul_le_mul_of_nonneg_left hb (autocorr_sub_nonneg hfc hf.continuous δ)
  have he := autocorr_increment_mul_weight_integral_le hf hfc hδ hδ1
  nlinarith

/-- The exponentially small grid displacement has energy cost at least linear in its center.
This also covers centers that are exactly logarithmic nodes, where the increment is zero. -/
theorem autocorr_logarithmicCeilLag_energy_bound {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {T : ℝ} (hT : 0 ≤ T) :
    Real.exp (-(1 / 2 : ℝ)) * T * (autocorr f 0 - autocorr f (logarithmicCeilLag T)) ≤
      4 * biScaleLevyEnergy f := by
  have hb := logarithmicCeilLag_bounds T
  rcases eq_or_lt_of_le hb.1 with hz | hp
  · rw [← hz, sub_self, mul_zero]
    exact mul_nonneg (by norm_num) (biScaleLevyEnergy_nonneg hfc hf.continuous)
  · have hδ1 : logarithmicCeilLag T ≤ 1 :=
      hb.2.trans (Real.exp_le_one_iff.mpr (by linarith))
    have hlog := Real.log_le_log hp hb.2
    rw [Real.log_exp] at hlog
    have hc := autocorr_increment_mul_log_le hf hfc hp hδ1
    have hm := mul_le_mul_of_nonneg_left (show T ≤ -Real.log (logarithmicCeilLag T) by linarith)
      (mul_nonneg (Real.exp_pos (-(1 / 2 : ℝ))).le
        (autocorr_sub_nonneg hfc hf.continuous (logarithmicCeilLag T)))
    nlinarith

/-- A quantitative tail-sample law for positive copy coefficients, uniform over the source.
Absolute sampling errors must be compared with the copy amplitude to detect the energy cost. -/
theorem subtractCopy_tail_sample_energy_bound (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) {D T a : ℝ}
    (hD : 0 ≤ D) (hsupp : ∀ x, D < |x| → autocorr f x = 0)
    (hT : D < T) (ha : 0 ≤ a) :
    Real.exp (-(1 / 2 : ℝ)) * T *
      (a * autocorr f 0 + autocorr (subtractCopy f a T)
        (Real.log (logarithmicCeilNode T : ℝ))) ≤ 4 * a * biScaleLevyEnergy f := by
  rw [autocorr_subtractCopy_logarithmicCeilNode f hD hsupp hT]
  have h := mul_le_mul_of_nonneg_left
    (autocorr_logarithmicCeilLag_energy_bound hf f.hasCompactSupport (by linarith : 0 ≤ T)) ha
  nlinarith

/-- A separated copy that preserves its first distant grid sample pays a linear separation
cost, in both the base source and the actual copy. The coefficient may have either sign. -/
theorem subtractCopy_zero_linear_energy_cost (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) {D T a : ℝ}
    (hD : 0 ≤ D) (hsupp : ∀ x, D < |x| → autocorr f x = 0)
    (hT : D + 1 < T) (ha : a ≠ 0)
    (hz : autocorr (subtractCopy f a T) (Real.log (logarithmicCeilNode T : ℝ)) = 0) :
    Real.exp (-(1 / 2 : ℝ)) * T * autocorr f 0 ≤ 4 * biScaleLevyEnergy f ∧
      Real.exp (-(1 / 2 : ℝ)) * T * autocorr (subtractCopy f a T) 0 ≤
        4 * biScaleLevyEnergy (subtractCopy f a T) := by
  have hT0 : 0 ≤ T := by linarith
  have hbasezero := (subtractCopy_zero_forces_translation_defect f hD hsupp
    (by linarith : D < T) ha hz).2.2.1
  have hb := logarithmicCeilLag_bounds T
  have hδ1 : |logarithmicCeilLag T| ≤ 1 := by
    rw [abs_of_nonneg hb.1]
    exact hb.2.trans (Real.exp_le_one_iff.mpr (by linarith))
  have hcopyzero : autocorr (subtractCopy f a T) (logarithmicCeilLag T) = 0 := by
    rw [autocorr_subtractCopy_local (f := (f : ℝ → ℝ)) f.continuous
      f.hasCompactSupport hsupp hT hδ1, hbasezero, mul_zero]
  constructor
  · have h := autocorr_logarithmicCeilLag_energy_bound hf f.hasCompactSupport hT0
    simpa only [hbasezero, sub_zero] using h
  · have h := autocorr_logarithmicCeilLag_energy_bound
      (contDiff_subtractCopy hf a T) (hasCompactSupport_subtractCopy f.hasCompactSupport a T) hT0
    simpa only [hcopyzero, sub_zero] using h

/-- Every compact `C²` source supplies its own separation threshold; no support-radius or
analytic estimate is left as an assumption of this endpoint. -/
theorem exists_subtractCopy_infinite_grid_energy_barrier
    (f : {f : C_c(ℝ, ℝ) // ContDiff ℝ 2 (f : ℝ → ℝ)}) :
    ∃ D : ℝ, 0 < D ∧ ∀ T : ℝ, D + 1 < T → ∀ a : ℝ, a ≠ 0 →
      autocorr (subtractCopy f.1 a T) (Real.log (logarithmicCeilNode T : ℝ)) = 0 →
      Real.exp (-(1 / 2 : ℝ)) * T * autocorr f.1 0 ≤ 4 * biScaleLevyEnergy f.1 ∧
      Real.exp (-(1 / 2 : ℝ)) * T * autocorr (subtractCopy f.1 a T) 0 ≤
        4 * biScaleLevyEnergy (subtractCopy f.1 a T) := by
  obtain ⟨D, hD, hsupp⟩ := exists_pos_autocorr_support_radius f.1.hasCompactSupport
  exact ⟨D, hD, fun T hT a ha hz => subtractCopy_zero_linear_energy_cost f.1 f.2 hD.le hsupp hT ha hz⟩

end

end GaloisForLFunctions.BiScaleUncertainty
