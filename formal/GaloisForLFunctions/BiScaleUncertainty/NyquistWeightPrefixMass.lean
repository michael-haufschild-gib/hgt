import GaloisForLFunctions.BiScaleUncertainty.NyquistPrefixScales
import GaloisForLFunctions.BiScaleUncertainty.NyquistPositivePrefixComparison

/-! # Sharp critical and supercritical residual mass prefixes -/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

def nyquistWeightPrefixMass (β : ℝ) (m N M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range M, nyquistWeightCellMass β m (N + k)

theorem tendsto_nyquistWeightCellMass_critical_ratio (m : ℕ) :
    Tendsto (fun k => nyquistWeightCellMass ((m : ℝ) + 1) m k /
      nyquistWeightCellWidth k) atTop (𝓝 (nyquistWeightCellConstant ((m : ℝ) + 1) m)) := by
  have ha := tendsto_nyquistWeightCellMass_normalized
    (by positivity : 0 < (m : ℝ) + 1) m
  have he : (m : ℝ) + 1 - ((m + 2 : ℕ) : ℝ) = -1 := by push_cast; ring
  rw [he] at ha
  have ht := ha.div tendsto_nyquistWeightCellWidth_scaled one_ne_zero
  simp only [div_one] at ht
  apply ht.congr'
  filter_upwards with k
  change (nyquistWeightCellMass ((m : ℝ) + 1) m k /
    ((k + 1 : ℕ) : ℝ) ^ (-1 : ℝ)) /
      (((k + 1 : ℕ) : ℝ) * nyquistWeightCellWidth k) = _
  rw [Real.rpow_neg_one]
  field_simp [(nyquistWeightCellWidth_pos k).ne']

theorem tendsto_nyquistWeightPrefixMass_critical_ratio (m N : ℕ) :
    Tendsto (fun M => nyquistWeightPrefixMass ((m : ℝ) + 1) m N M /
      (nyquistResidualNode (N + M) - nyquistResidualNode N))
      atTop (𝓝 (nyquistWeightCellConstant ((m : ℝ) + 1) m)) := by
  have hr := (tendsto_nyquistWeightCellMass_critical_ratio m).comp
    (tendsto_add_atTop_nat N)
  have ht := tendsto_nyquist_positive_prefix_ratio
    (a := fun k => nyquistWeightCellMass ((m : ℝ) + 1) m (N + k))
    (fun k => nyquistWeightCellWidth_pos (N + k))
    (tendsto_sum_nyquistWeightCellWidth N)
    (by simpa only [Function.comp_def, Nat.add_comm] using hr)
  simpa only [nyquistWeightPrefixMass, sum_nyquistWeightCellWidth] using ht

theorem tendsto_nyquistWeightPrefixMass_critical (m N : ℕ) :
    Tendsto (fun M => nyquistWeightPrefixMass ((m : ℝ) + 1) m N M /
      nyquistResidualNode M) atTop
      (𝓝 (nyquistWeightCellConstant ((m : ℝ) + 1) m)) := by
  have hB := tendsto_sum_nyquistWeightCellWidth N
  have ht := (tendsto_nyquistWeightPrefixMass_critical_ratio m N).mul
    (tendsto_sum_nyquistWeightCellWidth_normalized N)
  simp only [mul_one, sum_nyquistWeightCellWidth] at ht
  apply ht.congr'
  filter_upwards [hB.eventually (eventually_gt_atTop 0)] with M hM
  rw [sum_nyquistWeightCellWidth] at hM
  field_simp [hM.ne']

theorem tendsto_nyquistWeightCellMass_supercritical_ratio {β : ℝ} (m : ℕ)
    (hβ : (m : ℝ) + 1 < β) :
    Tendsto (fun k => nyquistWeightCellMass β m k /
      nyquistPowerIncrement (β - ((m : ℝ) + 1)) k) atTop
      (𝓝 (nyquistWeightCellConstant β m / (β - ((m : ℝ) + 1)))) := by
  let r : ℝ := β - ((m : ℝ) + 1)
  have hr : 0 < r := by dsimp [r]; linarith
  have ha := tendsto_nyquistWeightCellMass_normalized
    (by have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith : 0 < β) m
  have he : β - ((m + 2 : ℕ) : ℝ) = r - 1 := by dsimp [r]; push_cast; ring
  rw [he] at ha
  have ht := ha.div (tendsto_nyquistPowerIncrement_normalized r) hr.ne'
  apply ht.congr'
  filter_upwards with k
  change (nyquistWeightCellMass β m k / ((k + 1 : ℕ) : ℝ) ^ (r - 1)) /
    (nyquistPowerIncrement r k / ((k + 1 : ℕ) : ℝ) ^ (r - 1)) =
      nyquistWeightCellMass β m k / nyquistPowerIncrement r k
  have hn := (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < (k + 1 : ℕ)) (r - 1)).ne'
  field_simp [(nyquistPowerIncrement_pos hr k).ne']

theorem tendsto_nyquistWeightPrefixMass_supercritical {β : ℝ} (m N : ℕ)
    (hβ : (m : ℝ) + 1 < β) :
    Tendsto (fun M => nyquistWeightPrefixMass β m N M /
      ((M + 1 : ℕ) : ℝ) ^ (β - ((m : ℝ) + 1))) atTop
      (𝓝 (nyquistWeightCellConstant β m / (β - ((m : ℝ) + 1)))) := by
  let r : ℝ := β - ((m : ℝ) + 1)
  have hr : 0 < r := by dsimp [r]; linarith
  have hshift := (tendsto_nyquistWeightCellMass_supercritical_ratio m hβ).comp
    (tendsto_add_atTop_nat N)
  have hB := tendsto_sum_nyquistPowerIncrement hr N
  have hratio := tendsto_nyquist_positive_prefix_ratio
    (a := fun k => nyquistWeightCellMass β m (N + k))
    (fun k => nyquistPowerIncrement_pos hr (N + k)) hB
    (by simpa only [Function.comp_def, Nat.add_comm] using hshift)
  have ht := hratio.mul (tendsto_sum_nyquistPowerIncrement_normalized hr N)
  simp only [mul_one] at ht
  apply ht.congr'
  filter_upwards [hB.eventually (eventually_gt_atTop 0)] with M hM
  change ((nyquistWeightPrefixMass β m N M /
    (∑ k ∈ Finset.range M, nyquistPowerIncrement r (N + k))) *
    ((∑ k ∈ Finset.range M, nyquistPowerIncrement r (N + k)) /
      ((M + 1 : ℕ) : ℝ) ^ r)) = _
  field_simp [hM.ne']

end
end GaloisForLFunctions.BiScaleUncertainty
