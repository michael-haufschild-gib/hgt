import GaloisForLFunctions.RHTower.LogSineQuantileClock
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Singular endpoint control for the logarithmic sine quantile inverse

The reciprocal profile q is unbounded, but t*q(t) tends to zero at the left
endpoint. The proof uses the literal profile's logarithmic lower bound. Reflection
handles the other endpoint. The exact clock derivative, clock difference formula
and phase comparison retain the original singular coefficient.

These statements supply the endpoint control needed to construct a pinned-inverse
eigenmode from a transform zero. No spectral-placement assumption is introduced.
-/

open MeasureTheory Set Filter Topology
namespace RHTower
noncomputable section

/-- Reciprocal metric for the literal logarithmic sine profile. -/
def logSineQuantileSpeed (δ t : ℝ) : ℝ := 1 / logSineProfile δ t

theorem logSineQuantileSpeed_pos {δ t : ℝ} (hδ : 0 ≤ δ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < logSineQuantileSpeed δ t := one_div_pos.mpr (logSineProfile_pos hδ ht)

theorem logSineQuantileSpeed_one_sub (δ t : ℝ) :
    logSineQuantileSpeed δ (1 - t) = logSineQuantileSpeed δ t := by
  rw [logSineQuantileSpeed, logSineProfile_one_sub, logSineQuantileSpeed]

theorem continuousAt_logSineQuantileSpeed {δ t : ℝ} (hδ : 0 ≤ δ)
    (ht : t ∈ Ioo (0 : ℝ) 1) : ContinuousAt (logSineQuantileSpeed δ) t :=
  continuousAt_const.div (hasDerivAt_logSineProfile ht).continuousAt
    (logSineProfile_pos hδ ht).ne'

theorem intervalIntegrable_logSineQuantileSpeed {δ a b : ℝ} (hδ : 0 ≤ δ)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (logSineQuantileSpeed δ) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  exact (continuousAt_logSineQuantileSpeed hδ
    ⟨(lt_min ha.1 hb.1).trans_le ht.1, ht.2.trans_lt (max_lt ha.2 hb.2)⟩).continuousWithinAt

theorem logSineQuantileClock_sub {δ a b : ℝ} (hδ : 0 ≤ δ)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    logSineQuantileClock δ b - logSineQuantileClock δ a =
      ∫ t in a..b, logSineQuantileSpeed δ t :=
  intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_logSineQuantileSpeed hδ (by constructor <;> norm_num) hb)
    (intervalIntegrable_logSineQuantileSpeed hδ (by constructor <;> norm_num) ha)

/-- Arbitrarily small endpoint coefficient, derived from the actual profile. -/
theorem exists_logSineQuantileSpeed_endpoint_small {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ a < 1 / 2 ∧ ∀ t : ℝ, 0 < t → t ≤ a →
      t * logSineQuantileSpeed δ t ≤ ε := by
  let K : ℝ := 1 / (2 * δ * ε)
  have hK : 0 < K := by dsimp [K]; positivity
  have hE : 1 < Real.exp K := Real.one_lt_exp_iff.mpr hK
  let a : ℝ := min (1 / 4) (1 / (Real.pi * Real.exp K))
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have ha1 : a < 1 / 2 := (min_le_left _ _).trans_lt (by norm_num)
  refine ⟨a, ha, ha1, fun t ht hta => ?_⟩
  have ht1 : t < 1 / 2 := hta.trans_lt ha1
  have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨ht, by linarith⟩
  have hte : t * (Real.pi * Real.exp K) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < Real.pi * Real.exp K)).mp
      (hta.trans (min_le_right _ _))
  have hpt : Real.pi * t < 1 := by nlinarith [mul_pos Real.pi_pos ht]
  have hlog : K ≤ Real.log (1 / (Real.pi * t)) := by
    apply (Real.le_log_iff_exp_le (by positivity)).mpr
    apply (le_div_iff₀ (mul_pos Real.pi_pos ht)).mpr
    nlinarith [hte]
  have hlow := logSineProfile_endpoint_lower hδ.le ht ht1.le hpt
  have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2 * δ * t)
  have hid : ε * (2 * δ * t * K) = t := by dsimp [K]; field_simp
  unfold logSineQuantileSpeed
  rw [mul_one_div]
  apply (div_le_iff₀ (logSineProfile_pos hδ.le htI)).mpr
  calc
    t = ε * (2 * δ * t * K) := hid.symm
    _ ≤ ε * logSineProfile δ t := mul_le_mul_of_nonneg_left (hmul.trans hlow) hε.le

theorem tendsto_logSineQuantileSpeed_endpoint {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun t => t * logSineQuantileSpeed δ t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨a, ha, ha1, hb⟩ := exists_logSineQuantileSpeed_endpoint_small hδ (half_pos hε)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with t ht hta
  rw [dist_zero_right, Real.norm_of_nonneg (mul_nonneg ht.le
    (logSineQuantileSpeed_pos hδ.le ⟨ht, by linarith⟩).le)]
  exact (hb t ht hta.le).trans_lt (half_lt_self hε)

private theorem measurable_logSineQuantileSpeed (δ : ℝ) :
    Measurable (logSineQuantileSpeed δ) := by
  unfold logSineQuantileSpeed logSineProfile logSineLift
  fun_prop

theorem hasDerivAt_logSineQuantileClock {δ t : ℝ} (hδ : 0 ≤ δ)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (logSineQuantileClock δ) (logSineQuantileSpeed δ t) t := by
  exact intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_logSineQuantileSpeed hδ (by constructor <;> norm_num) ht)
    (measurable_logSineQuantileSpeed δ).stronglyMeasurable.stronglyMeasurableAtFilter
    (continuousAt_logSineQuantileSpeed hδ ht)

theorem logSineQuantileClock_one_sub (δ t : ℝ) :
    logSineQuantileClock δ (1 - t) = -logSineQuantileClock δ t := by
  have h := intervalIntegral.integral_comp_sub_left (logSineQuantileSpeed δ)
    (a := 1 / 2) (b := t) 1
  simp_rw [logSineQuantileSpeed_one_sub] at h
  norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by ring] at h
  change (∫ x in (1 / 2 : ℝ)..1 - t, logSineQuantileSpeed δ x) =
    -(∫ x in (1 / 2 : ℝ)..t, logSineQuantileSpeed δ x)
  rw [h, intervalIntegral.integral_symm (a := 1 - t) (b := 1 / 2)]

/-- An endpoint speed bound controls clock differences on the same interval. -/
theorem logSineQuantileClock_sub_le_log {δ ε a b : ℝ} (hδ : 0 ≤ δ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hq : ∀ v ∈ Icc a b, v * logSineQuantileSpeed δ v ≤ ε) :
    logSineQuantileClock δ b - logSineQuantileClock δ a ≤ ε * Real.log (b / a) := by
  have hb0 : 0 < b := ha.trans_le hab
  have hI : IntervalIntegrable (fun v : ℝ => ε / v) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact continuousOn_const.div continuousOn_id (fun v hv => (ha.trans_le hv.1).ne')
  rw [logSineQuantileClock_sub hδ ⟨ha, hab.trans_lt hb⟩ ⟨hb0, hb⟩]
  calc
    _ ≤ ∫ v in a..b, ε / v := by
      apply intervalIntegral.integral_mono_on hab
        (intervalIntegrable_logSineQuantileSpeed hδ ⟨ha, hab.trans_lt hb⟩ ⟨hb0, hb⟩) hI
      intro v hv
      apply (le_div_iff₀ (ha.trans_le hv.1)).mpr
      simpa only [mul_comm] using hq v hv
    _ = ε * ∫ v in a..b, 1 / v := by rw [← intervalIntegral.integral_const_mul]; congr 1; funext v; ring
    _ = _ := by rw [integral_one_div_of_pos ha hb0]

theorem logSineQuantileClock_sub_nonneg {δ a b : ℝ} (hδ : 0 ≤ δ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    0 ≤ logSineQuantileClock δ b - logSineQuantileClock δ a := by
  rw [logSineQuantileClock_sub hδ ⟨ha, hab.trans_lt hb⟩ ⟨ha.trans_le hab, hb⟩]
  apply intervalIntegral.integral_nonneg hab
  intro v hv
  exact (logSineQuantileSpeed_pos hδ ⟨ha.trans_le hv.1, hv.2.trans_lt hb⟩).le

/-- An actual phase comparison, retaining both clock arguments. -/
theorem logSineQuantile_phase_difference_bound {δ ε a b : ℝ} (hδ : 0 ≤ δ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (z : ℂ)
    (hε : |z.im| * ε ≤ 1 / 2)
    (hq : ∀ v ∈ Icc a b, v * logSineQuantileSpeed δ v ≤ ε) :
    ‖Complex.exp (Complex.I * z * ((logSineQuantileClock δ a - logSineQuantileClock δ b : ℝ) : ℂ))‖ ≤
      (b / a) ^ (1 / 2 : ℝ) := by
  have hd := logSineQuantileClock_sub_nonneg hδ ha hab hb
  have hbnd := logSineQuantileClock_sub_le_log hδ ha hab hb hq
  have hlog : 0 ≤ Real.log (b / a) := Real.log_nonneg ((one_le_div ha).mpr hab)
  rw [Complex.norm_exp, Real.rpow_def_of_pos (div_pos (ha.trans_le hab) ha)]
  apply Real.exp_le_exp.mpr
  have he : (Complex.I * z * ((logSineQuantileClock δ a - logSineQuantileClock δ b : ℝ) : ℂ)).re =
      z.im * (logSineQuantileClock δ b - logSineQuantileClock δ a) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [he]
  calc
    _ ≤ |z.im| * (logSineQuantileClock δ b - logSineQuantileClock δ a) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hd
    _ ≤ |z.im| * (ε * Real.log (b / a)) := mul_le_mul_of_nonneg_left hbnd (abs_nonneg _)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hε hlog]

end
end RHTower
