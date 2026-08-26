import GaloisForLFunctions.RHTower.Sieve.MoebiusHarmonicRealCutoffArbitraryLogRate
import GaloisForLFunctions.RHTower.Sieve.MoebiusShiftedLogPowerRealCutoff

/-!
# Shifted logarithmic Möbius kernels on interior rays

On the logarithmic layer `t = v * log X`, the remaining cutoff is
`X * exp (-v * log X) = X^(1-v)`.  For every fixed `v < 1`, it tends to infinity and the affine
shift exactly restores the original logarithmic scale: the linear kernel tends to `1`, while the
quadratic kernel divided by `log X` tends to `2`.
-/

open Filter Topology

namespace RHTower.Sieve

noncomputable section

/-- Remaining cutoff on the logarithmic ray of relative depth `v`. -/
def moebiusShiftedLogRay (v X : ℝ) : ℝ :=
  X * Real.exp (-v * Real.log X)

theorem moebiusShiftedLogRay_eq_rpow {v X : ℝ} (hX : 0 < X) :
    moebiusShiftedLogRay v X = X ^ (1 - v) := by
  rw [moebiusShiftedLogRay, Real.rpow_def_of_pos hX]
  calc
    X * Real.exp (-v * Real.log X) =
        Real.exp (Real.log X) * Real.exp (-v * Real.log X) := by
          rw [Real.exp_log hX]
    _ = Real.exp (Real.log X + (-v * Real.log X)) := by
      rw [Real.exp_add]
    _ = Real.exp (Real.log X * (1 - v)) := by congr 1; ring

theorem log_moebiusShiftedLogRay {v X : ℝ} (hX : 0 < X) :
    Real.log (moebiusShiftedLogRay v X) =
      (1 - v) * Real.log X := by
  rw [moebiusShiftedLogRay_eq_rpow hX, Real.log_rpow hX]

/-- Every interior logarithmic ray retains a cofinal cutoff. -/
theorem tendsto_moebiusShiftedLogRay_atTop {v : ℝ} (hv : v < 1) :
    Tendsto (moebiusShiftedLogRay v) atTop atTop := by
  have h := tendsto_rpow_atTop (sub_pos.mpr hv)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  exact (moebiusShiftedLogRay_eq_rpow hX).symm

/-- The shifted linear kernel has limit one on every fixed interior logarithmic ray. -/
theorem tendsto_moebiusShiftedLogKernelReal_logRay_one
    {v : ℝ} (hv : v < 1) :
    Tendsto (fun X : ℝ =>
      moebiusShiftedLogKernelReal (v * Real.log X)
        (moebiusShiftedLogRay v X)) atTop (nhds 1) := by
  have hY := tendsto_moebiusShiftedLogRay_atTop hv
  have hmain := tendsto_coprimeLogMoebius_one.comp hY
  have hrate :=
    (tendsto_log_pow_mul_deningerHarmonicPartial_natFloor_zero 1).comp hY
  have hlograte : Tendsto (fun X : ℝ => Real.log X *
      RHTower.deningerHarmonicPartial ⌊moebiusShiftedLogRay v X⌋₊)
      atTop (nhds 0) := by
    have hscaled := hrate.const_mul (1 / (1 - v))
    simp only [one_div, mul_zero] at hscaled
    refine hscaled.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have hvne : 1 - v ≠ 0 := by linarith
    simp only [Function.comp_apply, pow_one]
    rw [log_moebiusShiftedLogRay hX]
    field_simp [hvne]
  have herror := hlograte.const_mul v
  simp only [mul_zero] at herror
  have hsum := hmain.add herror
  simp only [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards with X
  rw [moebiusShiftedLogKernelReal_eq]
  simp only [Function.comp_apply]
  ring

/-- The shifted quadratic kernel has leading coefficient two on every fixed interior
logarithmic ray. -/
theorem tendsto_moebiusShiftedLogSqKernelReal_div_log_logRay_two
    {v : ℝ} (hv : v < 1) :
    Tendsto (fun X : ℝ =>
      moebiusShiftedLogSqKernelReal (v * Real.log X)
          (moebiusShiftedLogRay v X) / Real.log X)
      atTop (nhds 2) := by
  have hY := tendsto_moebiusShiftedLogRay_atTop hv
  have hlogratio : Tendsto
      (fun X : ℝ => Real.log (moebiusShiftedLogRay v X) / Real.log X)
      atTop (nhds (1 - v)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hXpos : 0 < X := by linarith
    have hlogX : Real.log X ≠ 0 := (Real.log_pos hX).ne'
    rw [log_moebiusShiftedLogRay hXpos]
    field_simp [hlogX]
  have hmainRatio := tendsto_moebiusDoubleLogKernelReal_div_log_two.comp hY
  have hmain : Tendsto (fun X : ℝ =>
      moebiusDoubleLogKernelReal (moebiusShiftedLogRay v X) / Real.log X)
      atTop (nhds (2 * (1 - v))) := by
    have hmul := hmainRatio.mul hlogratio
    refine hmul.congr' ?_
    filter_upwards [hY.eventually (eventually_gt_atTop (1 : ℝ)),
      eventually_gt_atTop (1 : ℝ)] with X hRay hX
    have hlogRay : Real.log (moebiusShiftedLogRay v X) ≠ 0 :=
      (Real.log_pos hRay).ne'
    have hlogX : Real.log X ≠ 0 := (Real.log_pos hX).ne'
    simp only [Function.comp_apply]
    field_simp [hlogRay, hlogX]
  have hlinear := tendsto_coprimeLogMoebius_one.comp hY
  have hmiddle : Tendsto (fun X : ℝ =>
      2 * (v * Real.log X) *
          coprimeLogMoebius 1 (moebiusShiftedLogRay v X) / Real.log X)
      atTop (nhds (2 * v)) := by
    have hscaled := hlinear.const_mul (2 * v)
    simp only [mul_one] at hscaled
    refine hscaled.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hlogX : Real.log X ≠ 0 := (Real.log_pos hX).ne'
    simp only [Function.comp_apply]
    field_simp [hlogX]
  have hrate :=
    (tendsto_log_pow_mul_deningerHarmonicPartial_natFloor_zero 1).comp hY
  have hlograte : Tendsto (fun X : ℝ => Real.log X *
      RHTower.deningerHarmonicPartial ⌊moebiusShiftedLogRay v X⌋₊)
      atTop (nhds 0) := by
    have hscaled := hrate.const_mul (1 / (1 - v))
    simp only [one_div, mul_zero] at hscaled
    refine hscaled.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have hvne : 1 - v ≠ 0 := by linarith
    simp only [Function.comp_apply, pow_one]
    rw [log_moebiusShiftedLogRay hX]
    field_simp [hvne]
  have herror : Tendsto (fun X : ℝ =>
      (v * Real.log X) ^ 2 *
          RHTower.deningerHarmonicPartial ⌊moebiusShiftedLogRay v X⌋₊ /
        Real.log X) atTop (nhds 0) := by
    have hscaled := hlograte.const_mul (v ^ 2)
    simp only [mul_zero] at hscaled
    refine hscaled.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hlogX : Real.log X ≠ 0 := (Real.log_pos hX).ne'
    field_simp [hlogX]
  have hsum := (hmain.add hmiddle).add herror
  have hlim : 2 * (1 - v) + 2 * v + 0 = (2 : ℝ) := by ring
  rw [hlim] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have hlogX : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  rw [moebiusShiftedLogSqKernelReal_eq]
  field_simp [hlogX]

end

end RHTower.Sieve
