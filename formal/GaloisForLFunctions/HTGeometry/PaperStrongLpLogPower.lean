import GaloisForLFunctions.HTGeometry.PaperLogPowerAdmission

/-! # Every Lᵖ input with p > 1 pays all finite logarithmic powers -/

noncomputable section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace GaloisForLFunctions.HTGeometry

abbrev StrongLpExponent := {p : ℝ≥0∞ // 1 < p}

private theorem logPower_rpow_bound (a : ℝ≥0) {b : ℝ} (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      Real.log (2 + t) ^ (a : ℝ) ≤ C * (2 + t) ^ b := by
  by_cases ha : (a : ℝ) = 0
  · refine ⟨1, one_pos, fun t ht => ?_⟩
    rw [ha, Real.rpow_zero, one_mul]
    exact Real.one_le_rpow (by linarith) hb.le
  · have ha0 : 0 < (a : ℝ) := lt_of_le_of_ne a.coe_nonneg (Ne.symm ha)
    have he : 0 < b / (a : ℝ) := div_pos hb ha0
    refine ⟨(b / (a : ℝ))⁻¹ ^ (a : ℝ), Real.rpow_pos_of_pos (inv_pos.mpr he) _, fun t ht => ?_⟩
    have ht0 : 0 < 2 + t := by linarith
    have hl : 0 ≤ Real.log (2 + t) := Real.log_nonneg (by linarith)
    have h := Real.rpow_le_rpow hl (Real.log_le_rpow_div ht0.le he) a.coe_nonneg
    calc
      _ ≤ ((2 + t) ^ (b / (a : ℝ)) / (b / (a : ℝ))) ^ (a : ℝ) := h
      _ = _ := by
        rw [div_eq_mul_inv, Real.mul_rpow (Real.rpow_nonneg ht0.le _) (inv_nonneg.mpr he.le),
          ← Real.rpow_mul ht0.le, div_mul_cancel₀ _ ha]
        ring

private theorem linear_mul_shift_rpow {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) :
    t * (2 + t) ^ b ≤ (3 : ℝ) ^ b * (1 + t ^ (b + 1)) := by
  by_cases ht1 : t ≤ 1
  · calc
      t * (2 + t) ^ b ≤ 1 * (3 : ℝ) ^ b :=
        mul_le_mul ht1 (Real.rpow_le_rpow (by linarith) (by linarith) hb.le)
          (Real.rpow_nonneg (by linarith) _) zero_le_one
      _ ≤ (3 : ℝ) ^ b * (1 + t ^ (b + 1)) := by
        have h := Real.rpow_nonneg ht (b + 1)
        have h3 := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) b
        nlinarith
  · have ht0 : 0 < t := lt_trans zero_lt_one (lt_of_not_ge ht1)
    calc
      t * (2 + t) ^ b ≤ t * (3 * t) ^ b :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by linarith) (by linarith) hb.le) ht
      _ = (3 : ℝ) ^ b * t ^ (b + 1) := by
        rw [Real.mul_rpow (by norm_num) ht, Real.rpow_add ht0, Real.rpow_one]
        ring
      _ ≤ (3 : ℝ) ^ b * (1 + t ^ (b + 1)) := by
        gcongr
        linarith

/-- Actual Lᵖ data, for every p > 1 including infinity, pay every finite log power. -/
theorem integrable_logPower_strongLp {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (p : StrongLpExponent)
    (f : Lp ℂ p.val μ) (a : ℝ≥0) :
    Integrable (fun x => ‖f x‖ * Real.log (2 + ‖f x‖) ^ (a : ℝ)) μ := by
  by_cases hp2 : 2 ≤ p.val
  · have hf := (Lp.memLp f).mono_exponent hp2
    refine (integrable_logPower_Lp μ (hf.toLp f) a).congr ?_
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
  · have htop : p.val ≠ ∞ := by
      intro h
      apply hp2
      rw [h]
      exact le_top
    have hp : 1 < p.val.toReal := by
      simpa using (ENNReal.toReal_lt_toReal (by simp) htop).mpr p.property
    let b := p.val.toReal - 1
    have hb : 0 < b := sub_pos.mpr hp
    obtain ⟨C, hC, hbound⟩ := logPower_rpow_bound a hb
    have hmoment := (Lp.memLp f).integrable_norm_rpow'
    have hm := (Lp.aestronglyMeasurable f).norm.aemeasurable
    refine ((integrable_const (1 : ℝ)).add hmoment |>.const_mul (C * (3 : ℝ) ^ b)).mono'
      (hm.mul ((aemeasurable_const.add hm).log.pow_const (a : ℝ))).aestronglyMeasurable ?_
    filter_upwards [] with x
    have ht := norm_nonneg (f x)
    have hl : 0 ≤ Real.log (2 + ‖f x‖) := Real.log_nonneg (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht (Real.rpow_nonneg hl _))]
    calc
      _ ≤ ‖f x‖ * (C * (2 + ‖f x‖) ^ b) :=
        mul_le_mul_of_nonneg_left (hbound _ ht) ht
      _ = C * (‖f x‖ * (2 + ‖f x‖) ^ b) := by ring
      _ ≤ C * ((3 : ℝ) ^ b * (1 + ‖f x‖ ^ (b + 1))) :=
        mul_le_mul_of_nonneg_left (linear_mul_shift_rpow ht hb) hC.le
      _ = C * (3 : ℝ) ^ b * (1 + ‖f x‖ ^ p.val.toReal) := by
        rw [show b + 1 = p.val.toReal by dsimp [b]; ring]
        ring

end GaloisForLFunctions.HTGeometry
