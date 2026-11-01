import GaloisForLFunctions.TransMetzlerWeilPositivity.ReceiverRate.TheLogarithmicFourierFloorHasAPowerLogBudget

/-!
# Exponential control of the logarithmic spectral reserves

Both the Gamma coefficient and every completed conductor energy have
reciprocal bounded by `exp(Bc/log²c)`, with the same fixed constant `B`.
The change of frequency scale costs at most a factor four in the exponent.
-/

noncomputable section
set_option autoImplicit false

open Filter Topology MeasureTheory

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

/-- Rescaling the logarithm by a fixed factor costs at most four once `d² ≤ c`. -/
theorem scaled_logarithmic_ratio_le {d c : ℝ} (hd : 1 ≤ d) (hc : 1 < c)
    (hdc : d ^ 2 ≤ c) :
    (c / d) / Real.log (c / d) ^ 2 ≤ 4 * c / Real.log c ^ 2 := by
  have hd0 := zero_lt_one.trans_le hd
  have hc0 := zero_lt_one.trans hc
  have hlc : 0 < Real.log c := Real.log_pos hc
  have hld : 0 ≤ Real.log d := Real.log_nonneg hd
  have hlog : 2 * Real.log d ≤ Real.log c := by
    have h := Real.log_le_log (sq_pos_of_pos hd0) hdc
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hdivlog : Real.log (c / d) = Real.log c - Real.log d :=
    Real.log_div hc0.ne' hd0.ne'
  have hhalf : Real.log c ≤ 2 * Real.log (c / d) := by
    rw [hdivlog]
    linarith only [hlog]
  have hldiv : 0 < Real.log (c / d) := by linarith only [hlc, hhalf]
  have hsquare : Real.log c ^ 2 ≤ 4 * Real.log (c / d) ^ 2 := by
    calc
      Real.log c ^ 2 ≤ (2 * Real.log (c / d)) ^ 2 := pow_le_pow_left₀ hlc.le hhalf 2
      _ = 4 * Real.log (c / d) ^ 2 := by ring
  have hcd : c / d ≤ c := div_le_self hc0.le hd
  apply (div_le_div_iff₀ (sq_pos_of_pos hldiv) (sq_pos_of_pos hlc)).mpr
  calc
    (c / d) * Real.log c ^ 2 ≤ c * Real.log c ^ 2 :=
      mul_le_mul_of_nonneg_right hcd (sq_nonneg _)
    _ ≤ c * (4 * Real.log (c / d) ^ 2) :=
      mul_le_mul_of_nonneg_left hsquare hc0.le
    _ = 4 * c * Real.log (c / d) ^ 2 := by ring

/-- A common exponential rate for both reciprocal spectral floors. -/
def logarithmicReserveRate : ℝ := 808 * sincTailConst

theorem logarithmicReserveRate_pos : 0 < logarithmicReserveRate := by
  unfold logarithmicReserveRate sincTailConst
  positivity

/-- The exponential control also dominates the overlap itself. -/
theorem le_logarithmicSpectralControl {c : ℝ} (hc : 1 < c) :
    c ≤ logarithmicSpectralControl logarithmicReserveRate c := by
  have hc0 := zero_lt_one.trans hc
  have hlc := Real.log_pos hc
  have hB : 6 ≤ logarithmicReserveRate := by
    unfold logarithmicReserveRate sincTailConst
    nlinarith only [Real.pi_pos]
  have h := Real.pow_div_factorial_le_exp (Real.log c) hlc.le 3
  norm_num [Real.exp_log hc0] at h
  have hcube : Real.log c ^ 3 ≤ logarithmicReserveRate * c := by
    nlinarith only [h, mul_le_mul_of_nonneg_right hB hc0.le]
  have hlog : Real.log c ≤ logarithmicReserveRate * c / Real.log c ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hlc)).mpr
    nlinarith only [hcube]
  exact (Real.exp_log hc0).symm.trans_le (Real.exp_le_exp.mpr hlog)

private theorem reciprocal_control_le_scaled_floor {d c : ℝ}
    (hd : 1 ≤ d) (hc : 1 < c) (hdc : d ^ 2 ≤ c) :
    (logarithmicSpectralControl logarithmicReserveRate c)⁻¹ ≤
      Real.exp (-(202 * sincTailConst * ((c / d) / Real.log (c / d) ^ 2))) := by
  have hC : 0 < sincTailConst := by unfold sincTailConst; positivity
  have h := mul_le_mul_of_nonneg_left (scaled_logarithmic_ratio_le hd hc hdc)
    (show 0 ≤ 202 * sincTailConst by positivity)
  rw [logarithmicSpectralControl, ← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  unfold logarithmicReserveRate
  have heq : 202 * sincTailConst * (4 * c / Real.log c ^ 2) =
      808 * sincTailConst * c / Real.log c ^ 2 := by ring
  rw [heq] at h
  exact neg_le_neg h

/-- Both positive spectral floors dominate the reciprocal of one exponential control. -/
theorem eventually_logarithmic_reserves_ge_reciprocal :
    ∀ᶠ c : ℝ in atTop,
      (logarithmicSpectralControl logarithmicReserveRate c)⁻¹ ≤ zeroFreeLogGammaReserve c ∧
      (logarithmicSpectralControl logarithmicReserveRate c)⁻¹ ≤ zeroFreeLogConductorFloor c := by
  have hd : 1 ≤ 16 * Real.pi := by linarith only [Real.pi_gt_three]
  have hM := integral_zeroFreeLogProfile_sq_pos
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_ge_atTop ((16 * Real.pi) ^ 2), eventually_ge_atTop (64 : ℝ),
    eventually_ge_atTop (Real.pi * (∫ u, zeroFreeLogProfile u ^ 2) / 24),
    eventually_ge_atTop ((∫ u, zeroFreeLogProfile u ^ 2) / 2)]
    with c hc hcd hc8 hcg hce
  have hc0 := zero_lt_one.trans hc
  have hg : (logarithmicSpectralControl logarithmicReserveRate c)⁻¹ ≤
      zeroFreeLogBandFloor c := reciprocal_control_le_scaled_floor hd hc hcd
  have he : (logarithmicSpectralControl logarithmicReserveRate c)⁻¹ ≤
      zeroFreeLogBandFloor (2 * Real.pi * c) := by
    have h := reciprocal_control_le_scaled_floor (by norm_num : (1 : ℝ) ≤ 8) hc
      (by norm_num at hc8 ⊢; exact hc8)
    have heq : 2 * Real.pi * c / (16 * Real.pi) = c / 8 := by
      field_simp [Real.pi_ne_zero]
      norm_num
    simpa only [zeroFreeLogBandFloor, heq] using h
  constructor
  · apply hg.trans
    unfold zeroFreeLogGammaReserve
    apply (le_div_iff₀ (mul_pos Real.pi_pos hM)).mpr
    have hcoef : Real.pi * (∫ u, zeroFreeLogProfile u ^ 2) ≤ 24 * c := by
      have h := (div_le_iff₀ (by norm_num : (0 : ℝ) < 24)).mp hcg
      linarith only [h]
    nlinarith only [mul_le_mul_of_nonneg_right hcoef (zeroFreeLogBandFloor_pos c).le]
  · apply he.trans
    unfold zeroFreeLogConductorFloor
    apply (le_div_iff₀ hM).mpr
    have hcoef : (∫ u, zeroFreeLogProfile u ^ 2) ≤ 2 * c := by
      have h := (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hce
      linarith only [h]
    nlinarith only [mul_le_mul_of_nonneg_right hcoef
      (zeroFreeLogBandFloor_pos (2 * Real.pi * c)).le]

end GaloisForLFunctions.TransMetzlerWeilPositivity

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.scaled_logarithmic_ratio_le
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.le_logarithmicSpectralControl
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_logarithmic_reserves_ge_reciprocal
