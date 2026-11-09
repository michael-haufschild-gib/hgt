import GaloisForLFunctions.ArithmeticElectrostatics.TheLogarithmicDepthProfilesDissipate
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Logarithmic thresholds as smooth profile limits

For positive `a`, the threshold `log(max 1 (u/a))` vanishes below `a`.
The normalized profile `(log(a^r+u^r)−log(a^r))/r` approximates it from
above with error at most `log 2/r`, uniformly over `u≥0`.
-/

open Filter Topology

namespace GaloisForLFunctions.ArithmeticElectrostatics
noncomputable section

/-- Logarithmic depth above threshold `a`. -/
def logarithmicDepthThreshold (a u : ℝ) : ℝ := Real.log (max 1 (u / a))

theorem logarithmicDepthThreshold_nonneg (a u : ℝ) :
    0 ≤ logarithmicDepthThreshold a u := Real.log_nonneg (le_max_left _ _)

theorem logarithmicDepthThreshold_zero (a : ℝ) : logarithmicDepthThreshold a 0 = 0 := by
  simp only [logarithmicDepthThreshold, zero_div, max_eq_left zero_le_one, Real.log_one]

theorem continuous_logarithmicDepthThreshold (a : ℝ) :
    Continuous (logarithmicDepthThreshold a) :=
  (continuous_const.max (continuous_id.div_const a)).log
    (fun u => (zero_lt_one.trans_le (le_max_left (1 : ℝ) (u / a))).ne')

theorem logarithmicDepthThreshold_eq_zero {a u : ℝ} (ha : 0 < a) (hu : u ≤ a) :
    logarithmicDepthThreshold a u = 0 := by
  have h : u / a ≤ 1 := (div_le_iff₀ ha).mpr (by simpa only [one_mul] using hu)
  simp only [logarithmicDepthThreshold, max_eq_left h, Real.log_one]

theorem logarithmicDepthThreshold_eq_log_sub {a u : ℝ} (ha : 0 < a) (hu : a ≤ u) :
    logarithmicDepthThreshold a u = Real.log u - Real.log a := by
  have h : 1 ≤ u / a := (le_div_iff₀ ha).mpr (by simpa only [one_mul] using hu)
  rw [logarithmicDepthThreshold, max_eq_right h, Real.log_div (ha.trans_le hu).ne' ha.ne']

theorem monotone_logarithmicDepthThreshold {a : ℝ} (ha : 0 < a) :
    Monotone (logarithmicDepthThreshold a) := by
  intro u v huv
  exact Real.log_le_log (zero_lt_one.trans_le (le_max_left _ _))
    (max_le_max le_rfl (div_le_div_of_nonneg_right huv ha.le))

theorem logarithmicDepthThreshold_eq_max_log_sub {a u : ℝ} (ha : 0 < a) (hu : 0 < u) :
    logarithmicDepthThreshold a u = max (Real.log u - Real.log a) 0 := by
  by_cases hua : u ≤ a
  · rw [logarithmicDepthThreshold_eq_zero ha hua,
      max_eq_right (sub_nonpos.mpr (Real.log_le_log hu hua))]
  · have hau : a ≤ u := (lt_of_not_ge hua).le
    rw [logarithmicDepthThreshold_eq_log_sub ha hau,
      max_eq_left (sub_nonneg.mpr (Real.log_le_log ha hau))]

/-- Uniform error bound for the smooth logarithmic approximation. -/
theorem elapsedLogDepthProfile_threshold_error {r a u : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hu : 0 ≤ u) :
    0 ≤ elapsedLogDepthProfile r (a ^ r) u / r - logarithmicDepthThreshold a u ∧
      elapsedLogDepthProfile r (a ^ r) u / r - logarithmicDepthThreshold a u ≤ Real.log 2 / r := by
  have hA : 0 < a ^ r := Real.rpow_pos_of_pos ha r
  have hU : 0 ≤ u ^ r := Real.rpow_nonneg hu r
  have hsum : 0 < a ^ r + u ^ r := add_pos_of_pos_of_nonneg hA hU
  by_cases hua : u ≤ a
  · rw [logarithmicDepthThreshold_eq_zero ha hua, sub_zero]
    have hp := Real.rpow_le_rpow hu hua hr.le
    have hlog := Real.log_le_log hsum (show a ^ r + u ^ r ≤ 2 * a ^ r by linarith only [hp])
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hA.ne'] at hlog
    constructor
    · exact div_nonneg (elapsedLogDepthProfile_nonneg hA hu r) hr.le
    · apply div_le_div_of_nonneg_right _ hr.le
      unfold elapsedLogDepthProfile
      linarith only [hlog]
  · have hau : a ≤ u := (lt_of_not_ge hua).le
    have hu0 : 0 < u := ha.trans_le hau
    have hp := Real.rpow_le_rpow ha.le hau hr.le
    have hup := Real.rpow_pos_of_pos hu0 r
    have hlo := Real.log_le_log hup (le_add_of_nonneg_left hA.le)
    have hhi := Real.log_le_log hsum (show a ^ r + u ^ r ≤ 2 * u ^ r by linarith only [hp])
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hup.ne', Real.log_rpow hu0] at hhi
    rw [Real.log_rpow hu0] at hlo
    have hlower : r * (Real.log u - Real.log a) ≤ elapsedLogDepthProfile r (a ^ r) u := by
      unfold elapsedLogDepthProfile
      rw [Real.log_rpow ha]
      linarith only [hlo]
    have hupper : elapsedLogDepthProfile r (a ^ r) u ≤
        r * (Real.log u - Real.log a) + Real.log 2 := by
      unfold elapsedLogDepthProfile
      rw [Real.log_rpow ha]
      linarith only [hhi]
    have hlowdiv : Real.log u - Real.log a ≤ elapsedLogDepthProfile r (a ^ r) u / r :=
      (le_div_iff₀ hr).mpr (by nlinarith only [hlower])
    have hhighdiv : elapsedLogDepthProfile r (a ^ r) u / r ≤
        Real.log u - Real.log a + Real.log 2 / r := by
      apply (div_le_iff₀ hr).mpr
      calc
        _ ≤ r * (Real.log u - Real.log a) + Real.log 2 := hupper
        _ = _ := by field_simp [hr.ne']
    rw [logarithmicDepthThreshold_eq_log_sub ha hau]
    constructor <;> linarith only [hlowdiv, hhighdiv]

/-- Increasing integer exponents recover the exact threshold profile. -/
theorem tendsto_elapsedLogDepthProfile_threshold {a u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) :
    Tendsto (fun n : ℕ => elapsedLogDepthProfile ((n : ℝ) + 1) (a ^ ((n : ℝ) + 1)) u /
      ((n : ℝ) + 1)) atTop (𝓝 (logarithmicDepthThreshold a u)) := by
  have hupper : Tendsto (fun n : ℕ => Real.log 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (Real.log 2)
  have h := squeeze_zero
    (fun n : ℕ => (elapsedLogDepthProfile_threshold_error (r := (n : ℝ) + 1)
      (by positivity) ha hu).1)
    (fun n : ℕ => (elapsedLogDepthProfile_threshold_error (r := (n : ℝ) + 1)
      (by positivity) ha hu).2) hupper
  simpa only [sub_add_cancel, zero_add] using h.add_const (logarithmicDepthThreshold a u)

#print axioms elapsedLogDepthProfile_threshold_error
#print axioms tendsto_elapsedLogDepthProfile_threshold

end
end GaloisForLFunctions.ArithmeticElectrostatics
