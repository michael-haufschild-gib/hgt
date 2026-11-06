import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The sharp horizontal gain between two zero-detection radii

The gain `t log((t+a)/(t+b))` is strictly below `a-b` and approaches
that bound as `t` tends to infinity. For a spectral gap above `1/2`,
the corresponding gain is therefore strictly below `1/2`.
This is a parameter bound, not a lower bound for actual recurrence times.
-/

open Filter Topology

namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-- Two rational bounds for the logarithmic gain between two horizontal radii. -/
theorem mul_log_shift_ratio_bounds {a b t : ℝ} (hb : 0 < b) (hba : b < a)
    (ht : 0 ≤ t) :
    t / (t + a) * (a - b) ≤ t * Real.log ((t + a) / (t + b)) ∧
      t * Real.log ((t + a) / (t + b)) ≤ t / (t + b) * (a - b) := by
  have hTa : 0 < t + a := by linarith only [hb, hba, ht]
  have hTb : 0 < t + b := add_pos_of_nonneg_of_pos ht hb
  have hq : 0 < (t + a) / (t + b) := div_pos hTa hTb
  have hlo := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hq) ht
  have hhi := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hq) ht
  constructor
  · calc
      t / (t + a) * (a - b) = t * (1 - ((t + a) / (t + b))⁻¹) := by
        field_simp [hTa.ne', hTb.ne']; ring
      _ ≤ _ := hlo
  · calc
      _ ≤ t * ((t + a) / (t + b) - 1) := hhi
      _ = _ := by field_simp [hTa.ne', hTb.ne']; ring

/-- The gain is strictly smaller than the difference of the two offsets. -/
theorem mul_log_shift_ratio_lt_gap {a b t : ℝ} (hb : 0 < b) (hba : b < a)
    (ht : 0 ≤ t) : t * Real.log ((t + a) / (t + b)) < a - b := by
  apply (mul_log_shift_ratio_bounds hb hba ht).2.trans_lt
  have hfrac : t / (t + b) < 1 := (div_lt_one (by linarith only [hb, ht])).mpr (by linarith only [hb])
  exact mul_lt_of_lt_one_left (sub_pos.mpr hba) hfrac

/-- The gap bound is sharp: the gain approaches it as the common offset tends to infinity. -/
theorem tendsto_nat_mul_log_shift_ratio {a b : ℝ} (hb : 0 < b) (hba : b < a) :
    Tendsto (fun n : ℕ => (n : ℝ) * Real.log (((n : ℝ) + a) / (n + b)))
      atTop (𝓝 (a - b)) := by
  have hlo := (tendsto_natCast_div_add_atTop a).mul_const (a - b)
  simp only [one_mul] at hlo
  have herror : Tendsto
      (fun n : ℕ => (a - b) - (n : ℝ) * Real.log (((n : ℝ) + a) / (n + b)))
      atTop (𝓝 0) := by
    apply squeeze_zero
      (fun n => sub_nonneg.mpr (mul_log_shift_ratio_lt_gap hb hba (Nat.cast_nonneg n)).le)
      (fun n => sub_le_sub_left
        (mul_log_shift_ratio_bounds hb hba (Nat.cast_nonneg n)).1 (a - b))
    simpa only [sub_self] using (tendsto_const_nhds (x := a - b)).sub hlo
  simpa only [sub_zero, sub_sub_cancel] using
    (tendsto_const_nhds (x := a - b)).sub herror

/-- In a spectral gap above the critical line, the normalized horizontal gain is below `1/2`. -/
theorem horizontal_jet_gain_lt_half {β₁ β η : ℝ}
    (hβ₁ : 1 / 2 ≤ β₁) (hgap : β₁ < β) (hβ : β < 1) (hη : 0 ≤ η) :
    η * Real.log ((η + 1 - β₁) / (η + 1 - β)) < β - β₁ ∧ β - β₁ < 1 / 2 := by
  have h := mul_log_shift_ratio_lt_gap
    (a := 1 - β₁) (b := 1 - β) (t := η)
    (by linarith only [hβ]) (by linarith only [hgap]) hη
  constructor
  · have hnum : η + (1 - β₁) = η + 1 - β₁ := by ring
    have hden : η + (1 - β) = η + 1 - β := by ring
    have hdiff : (1 - β₁) - (1 - β) = β - β₁ := by ring
    rwa [hnum, hden, hdiff] at h
  · linarith only [hβ, hβ₁]

#print axioms tendsto_nat_mul_log_shift_ratio
#print axioms horizontal_jet_gain_lt_half

end GaloisForLFunctions.ZeroConfigurationGeometry
