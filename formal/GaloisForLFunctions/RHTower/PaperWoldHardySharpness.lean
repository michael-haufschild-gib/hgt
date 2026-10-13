import GaloisForLFunctions.RHTower.PaperWoldHardyEscape

/-! # Sharp lower bounds surviving every compact Hardy correction -/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry

def paperWoldHardyPowerScale (a : {a : ℝ // 1 / 2 < a}) (K : ℕ) : ℝ :=
  (1 / (2 * (a : ℝ))) * (((K : ℝ) + 1) / ((K : ℝ) + 2)) ^ (a : ℝ)

theorem paperWoldHardyPowerScale_nonneg (a : {a : ℝ // 1 / 2 < a}) (K : ℕ) :
    0 ≤ paperWoldHardyPowerScale a K := by
  have ha : 0 < (a : ℝ) := by linarith [a.property]
  unfold paperWoldHardyPowerScale
  positivity

private theorem power_shift_lower (a : {a : ℝ // 1 / 2 < a}) (K n : ℕ) (hKn : K ≤ n) :
    paperWoldHardyPowerScale a K * ((n : ℝ) + 1) ^ (-(a : ℝ)) ≤
      ((n : ℝ) + 2) ^ (-(a : ℝ)) / (2 * (a : ℝ)) := by
  have ha : 0 < (a : ℝ) := by linarith [a.property]
  have hratio : ((K : ℝ) + 1) / ((K : ℝ) + 2) ≤ ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have h : (K : ℝ) ≤ n := Nat.cast_le.mpr hKn
    nlinarith
  have h := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) hratio ha.le)
    (show 0 ≤ ((n : ℝ) + 1) ^ (-(a : ℝ)) by positivity)
  have he : (((n : ℝ) + 1) / ((n : ℝ) + 2)) ^ (a : ℝ) * ((n : ℝ) + 1) ^ (-(a : ℝ)) =
      ((n : ℝ) + 2) ^ (-(a : ℝ)) := by
    rw [Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity),
      Real.rpow_neg (by positivity)]
    have hp : ((n : ℝ) + 1) ^ (a : ℝ) ≠ 0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
    field_simp
  rw [he] at h
  have hc := mul_le_mul_of_nonneg_left h (show 0 ≤ 1 / (2 * (a : ℝ)) by positivity)
  simpa only [paperWoldHardyPowerScale, mul_assoc, one_div, div_eq_mul_inv, mul_comm, one_mul] using hc

theorem paperWoldHardyPowerHistory_norm_lower (a : {a : ℝ // 1 / 2 < a}) (K : ℕ) :
    paperWoldHardyPowerScale a K * ‖paperWoldHardyPowerHistory a K‖ ≤
      ‖paperWoldHardyOperator (paperWoldHardyPowerHistory a K)‖ := by
  let f := paperWoldHardyPowerHistory a K
  let c := paperWoldHardyPowerScale a K
  have hc : 0 ≤ c := paperWoldHardyPowerScale_nonneg a K
  have hpoint (n : ℕ) : c * ‖f n‖ ≤ ‖paperWoldHardyOperator f n‖ := by
    by_cases hn : K ≤ n
    · have he : ‖f n‖ = ((n : ℝ) + 1) ^ (-(a : ℝ)) := by
        change ‖(paperWoldHardyPowerTail a K n : ℂ)‖ = _
        rw [paperWoldHardyPowerTail, if_pos hn, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.rpow_pos_of_pos (by positivity) _)]
      rw [he]
      exact (power_shift_lower a K n hn).trans
        ((paperWoldHardyPowerHistory_row_lower a K n hn).trans (Complex.re_le_norm _))
    · have he : f n = 0 := by simp [f, paperWoldHardyPowerHistory, paperWoldHardyPowerTail, hn]
      rw [he, norm_zero, mul_zero]
      exact norm_nonneg _
  have hsq : c ^ 2 * ‖f‖ ^ 2 ≤ ‖paperWoldHardyOperator f‖ ^ 2 := by
    rw [HilbertSchmidt.lp_norm_sq_eq, HilbertSchmidt.lp_norm_sq_eq, ← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun n => by
      simpa only [mul_pow] using pow_le_pow_left₀ (mul_nonneg hc (norm_nonneg _)) (hpoint n) 2)
      ((HilbertSchmidt.summable_coe_sq f).mul_left (c ^ 2))
      (HilbertSchmidt.summable_coe_sq _)
  change c * ‖f‖ ≤ ‖paperWoldHardyOperator f‖
  nlinarith [norm_nonneg f, norm_nonneg (paperWoldHardyOperator f)]

theorem paperWoldHardyPowerUnit_image_lower (a : {a : ℝ // 1 / 2 < a}) (K : ℕ) :
    paperWoldHardyPowerScale a K ≤ ‖paperWoldHardyOperator (paperWoldHardyPowerUnit a K)‖ := by
  have hp := norm_pos_iff.mpr (paperWoldHardyPowerHistory_ne_zero a K)
  have h := mul_le_mul_of_nonneg_left (paperWoldHardyPowerHistory_norm_lower a K) (inv_nonneg.mpr hp.le)
  rw [paperWoldHardyPowerUnit, map_smul, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  calc
    _ = ‖paperWoldHardyPowerHistory a K‖⁻¹ *
        (paperWoldHardyPowerScale a K * ‖paperWoldHardyPowerHistory a K‖) := by field_simp
    _ ≤ _ := h

theorem paperWoldHardyPowerScale_tendsto (a : {a : ℝ // 1 / 2 < a}) :
    Tendsto (paperWoldHardyPowerScale a) atTop (𝓝 (1 / (2 * (a : ℝ)))) := by
  have hi : Tendsto (fun K : ℕ => (((K : ℝ) + 2)⁻¹)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  have hr : Tendsto (fun K : ℕ => ((K : ℝ) + 1) / ((K : ℝ) + 2)) atTop (𝓝 (1 : ℝ)) := by
    have h : Tendsto (fun K : ℕ => 1 - ((K : ℝ) + 2)⁻¹) atTop (𝓝 ((1 : ℝ) - 0)) :=
      tendsto_const_nhds.sub hi
    simp only [sub_zero] at h
    convert h using 1
    funext K
    field_simp
    ring
  have h := (hr.rpow_const (p := (a : ℝ)) (Or.inl one_ne_zero)).const_mul (1 / (2 * (a : ℝ)))
  change Tendsto (fun K : ℕ => (1 / (2 * (a : ℝ))) *
    (((K : ℝ) + 1) / ((K : ℝ) + 2)) ^ (a : ℝ)) atTop (𝓝 (1 / (2 * (a : ℝ))))
  simpa only [Real.one_rpow, mul_one] using h

theorem paperWoldHardyOperator_sub_compact_norm_ge_one
    (C : compactOperatorStarAlgebra PaperWoldHistory) : 1 ≤ ‖paperWoldHardyOperator - C.val‖ := by
  have hbound (a : {a : ℝ // 1 / 2 < a}) : 1 / (2 * (a : ℝ)) ≤ ‖paperWoldHardyOperator - C.val‖ := by
    have hc := tendsto_norm_compact_of_weaklyNull C.val C.property (paperWoldHardyPowerUnit a)
      (fun K => (paperWoldHardyPowerUnit_norm a K).le) (paperWoldHardyPowerUnit_weaklyNull a)
    have hcn : Tendsto (fun K => ‖C.val (paperWoldHardyPowerUnit a K)‖) atTop (𝓝 0) := by
      simpa only [norm_zero] using hc.norm
    have hle (K : ℕ) : paperWoldHardyPowerScale a K ≤
        ‖paperWoldHardyOperator - C.val‖ + ‖C.val (paperWoldHardyPowerUnit a K)‖ := by
      have h := (paperWoldHardyOperator - C.val).le_opNorm (paperWoldHardyPowerUnit a K)
      rw [paperWoldHardyPowerUnit_norm, mul_one] at h
      have ht := norm_add_le ((paperWoldHardyOperator - C.val) (paperWoldHardyPowerUnit a K))
        (C.val (paperWoldHardyPowerUnit a K))
      simp only [sub_apply, sub_add_cancel] at ht
      exact (paperWoldHardyPowerUnit_image_lower a K).trans (ht.trans (add_le_add h le_rfl))
    have h := le_of_tendsto_of_tendsto (paperWoldHardyPowerScale_tendsto a)
      (tendsto_const_nhds.add hcn) (Filter.Eventually.of_forall hle)
    simpa only [add_zero] using h
  by_contra h
  have hd : ‖paperWoldHardyOperator - C.val‖ < 1 := lt_of_not_ge h
  let d := ‖paperWoldHardyOperator - C.val‖
  have hp : 0 < d + 1 := by dsimp [d]; positivity
  have ha : (1 / 2 : ℝ) < 1 / (d + 1) := by
    apply (lt_div_iff₀ hp).mpr
    dsimp [d]
    linarith
  have hh := hbound ⟨1 / (d + 1), ha⟩
  have he : 1 / (2 * (1 / (d + 1))) = (d + 1) / 2 := by field_simp
  change 1 / (2 * (1 / (d + 1))) ≤ d at hh
  rw [he] at hh
  dsimp [d] at hh
  linarith

end
end RHTower
