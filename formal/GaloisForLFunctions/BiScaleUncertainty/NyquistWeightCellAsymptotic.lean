import GaloisForLFunctions.BiScaleUncertainty.NyquistWeightCells
import Mathlib.Analysis.PSeries

/-! # Exact Nyquist cell asymptotics and the sharp summability threshold -/

open Set Filter Topology Asymptotics

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

def nyquistWeightCellConstant (β : ℝ) (m : ℕ) : ℝ :=
  β ^ (m + 1) / (2 * ((m + 2).factorial : ℝ))

theorem nyquistWeightCellConstant_pos {β : ℝ} (hβ : 0 < β) (m : ℕ) :
    0 < nyquistWeightCellConstant β m := by
  unfold nyquistWeightCellConstant
  positivity

theorem tendsto_nyquistWeightJet_normalized {β : ℝ} (hβ : 0 < β) (j : ℕ) :
    Tendsto (fun k => nyquistWeightJet β j (nyquistResidualNode k) /
      ((k + 1 : ℕ) : ℝ) ^ β) atTop (𝓝 (β ^ j / 2)) := by
  have hn : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hp : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-2 * β)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using
      (tendsto_rpow_neg_atTop (by positivity : 0 < 2 * β)).comp hn
  have ht : Tendsto (fun k : ℕ => β ^ j / 2 *
      (1 + (-1 : ℝ) ^ j * ((k + 1 : ℕ) : ℝ) ^ (-2 * β))) atTop (𝓝 (β ^ j / 2)) := by
    simpa only [mul_zero, add_zero, mul_one] using
      ((tendsto_const_nhds (x := (1 : ℝ))).add
        (hp.const_mul ((-1 : ℝ) ^ j))).const_mul (β ^ j / 2)
  exact ht.congr' (Eventually.of_forall fun k =>
    (nyquistWeightJet_log_normalized β j (by positivity : (0 : ℝ) < (k + 1 : ℕ))).symm)

theorem tendsto_nyquistWeight_successor_ratio :
    Tendsto (fun k : ℕ => ((k + 2 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
  have ht : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))
      atTop (𝓝 1) := by
    convert (tendsto_natCast_div_add_atTop (1 : ℝ)).comp (tendsto_add_atTop_nat 1) using 1
    norm_num [Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc]
  have hi := (tendsto_const_nhds (x := (1 : ℝ))).div ht one_ne_zero
  change Tendsto (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)))
    atTop (𝓝 ((1 : ℝ) / 1)) at hi
  simpa only [one_div_div, div_one] using hi

theorem tendsto_nyquistWeightJet_successor_normalized {β : ℝ} (hβ : 0 < β) (j : ℕ) :
    Tendsto (fun k => nyquistWeightJet β j (nyquistResidualNode (k + 1)) /
      ((k + 1 : ℕ) : ℝ) ^ β) atTop (𝓝 (β ^ j / 2)) := by
  have hj := (tendsto_nyquistWeightJet_normalized hβ j).comp (tendsto_add_atTop_nat 1)
  have hr := tendsto_nyquistWeight_successor_ratio.rpow_const (Or.inl one_ne_zero :
    (1 : ℝ) ≠ 0 ∨ 0 ≤ β)
  have ht : Tendsto (fun k =>
      (nyquistWeightJet β j (nyquistResidualNode (k + 1)) / ((k + 2 : ℕ) : ℝ) ^ β) *
      (((k + 2 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)) ^ β) atTop (𝓝 (β ^ j / 2)) := by
    simpa only [Function.comp_def, Nat.add_assoc, Real.one_rpow, mul_one] using hj.mul hr
  apply ht.congr'
  filter_upwards with k
  rw [Real.div_rpow (by positivity : (0 : ℝ) ≤ (k + 2 : ℕ))
    (by positivity : (0 : ℝ) ≤ (k + 1 : ℕ))]
  have hn : ((k + 2 : ℕ) : ℝ) ^ β ≠ 0 := (Real.rpow_pos_of_pos (by positivity) β).ne'
  field_simp

theorem tendsto_nyquistWeightCellMass_normalized {β : ℝ} (hβ : 0 < β) (m : ℕ) :
    Tendsto (fun k => nyquistWeightCellMass β m k /
      ((k + 1 : ℕ) : ℝ) ^ (β - ((m + 2 : ℕ) : ℝ))) atTop
      (𝓝 (nyquistWeightCellConstant β m)) := by
  have hw := tendsto_nyquistWeightCellWidth_scaled.pow (m + 2)
  have hl : Tendsto (fun k =>
      (nyquistWeightJet β (m + 1) (nyquistResidualNode k) / ((k + 1 : ℕ) : ℝ) ^ β) *
      (((k + 1 : ℕ) : ℝ) * nyquistWeightCellWidth k) ^ (m + 2) /
      ((m + 2).factorial : ℝ)) atTop (𝓝 (nyquistWeightCellConstant β m)) := by
    convert ((tendsto_nyquistWeightJet_normalized hβ (m + 1)).mul hw).div
      tendsto_const_nhds (by positivity : ((m + 2).factorial : ℝ) ≠ 0) using 1
    congr 1
    simp only [one_pow, mul_one, nyquistWeightCellConstant]
    ring
  have hu : Tendsto (fun k =>
      (nyquistWeightJet β (m + 1) (nyquistResidualNode (k + 1)) /
        ((k + 1 : ℕ) : ℝ) ^ β) *
      (((k + 1 : ℕ) : ℝ) * nyquistWeightCellWidth k) ^ (m + 2) /
      ((m + 2).factorial : ℝ)) atTop (𝓝 (nyquistWeightCellConstant β m)) := by
    convert ((tendsto_nyquistWeightJet_successor_normalized hβ (m + 1)).mul hw).div
      tendsto_const_nhds (by positivity : ((m + 2).factorial : ℝ) ≠ 0) using 1
    congr 1
    simp only [one_pow, mul_one, nyquistWeightCellConstant]
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu
  · intro k
    have h := div_le_div_of_nonneg_right (nyquistWeightCellMass_bounds hβ.le m k).1
      (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < (k + 1 : ℕ))
        (β - ((m + 2 : ℕ) : ℝ))).le
    rwa [nyquistWeight_endpoint_normalization β _ _ (by positivity)] at h
  · intro k
    have h := div_le_div_of_nonneg_right (nyquistWeightCellMass_bounds hβ.le m k).2
      (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < (k + 1 : ℕ))
        (β - ((m + 2 : ℕ) : ℝ))).le
    rwa [nyquistWeight_endpoint_normalization β _ _ (by positivity)] at h

theorem isEquivalent_nyquistWeightCellMass {β : ℝ} (hβ : 0 < β) (m : ℕ) :
    IsEquivalent atTop (nyquistWeightCellMass β m)
      (fun k => nyquistWeightCellConstant β m *
        ((k + 1 : ℕ) : ℝ) ^ (β - ((m + 2 : ℕ) : ℝ))) := by
  have hc := (nyquistWeightCellConstant_pos hβ m).ne'
  apply (isEquivalent_iff_tendsto_one (Eventually.of_forall fun k =>
    mul_ne_zero hc (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < (k + 1 : ℕ)) _).ne')).mpr
  change Tendsto (fun k => nyquistWeightCellMass β m k /
    (nyquistWeightCellConstant β m * ((k + 1 : ℕ) : ℝ) ^ (β - ((m + 2 : ℕ) : ℝ))))
    atTop (𝓝 1)
  have ht := (tendsto_nyquistWeightCellMass_normalized hβ m).div tendsto_const_nhds hc
  change Tendsto (fun k => (nyquistWeightCellMass β m k /
    ((k + 1 : ℕ) : ℝ) ^ (β - ((m + 2 : ℕ) : ℝ))) / nyquistWeightCellConstant β m)
    atTop (𝓝 (nyquistWeightCellConstant β m / nyquistWeightCellConstant β m)) at ht
  simpa only [div_self hc, div_div, mul_comm] using ht

theorem summable_nyquistWeightCellMass_iff {β : ℝ} (hβ : 0 < β) (m : ℕ) :
    Summable (nyquistWeightCellMass β m) ↔ β < (m : ℝ) + 1 := by
  rw [(isEquivalent_nyquistWeightCellMass hβ m).summable_iff_nat,
    summable_mul_left_iff (nyquistWeightCellConstant_pos hβ m).ne',
    summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (β - ((m + 2 : ℕ) : ℝ))) 1,
    Real.summable_nat_rpow]
  push_cast
  constructor <;> intro h <;> linarith

theorem summable_nyquistWeightCellMass_tail_iff {β : ℝ} (hβ : 0 < β) (m N : ℕ) :
    Summable (fun k => nyquistWeightCellMass β m (N + k)) ↔ β < (m : ℝ) + 1 := by
  simpa only [Nat.add_comm] using
    (summable_nat_add_iff N).trans (summable_nyquistWeightCellMass_iff hβ m)

end
end GaloisForLFunctions.BiScaleUncertainty
