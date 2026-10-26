import GaloisForLFunctions.BiScaleUncertainty.EnergyControlledClosedCycleRecovery

/-!
# The exact first-order singular-energy collar

The deficit estimate gives the collar exponent eight directly. The squared
increment modulus is retained for moving between nearby sample locations.
-/

noncomputable section
open MeasureTheory Set
open scoped CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
namespace GaloisForLFunctions.BiScaleUncertainty.EnergyCycle
set_option autoImplicit false

/-- The actual normalized energy ceiling is nonnegative whenever its source class is inhabited. -/
theorem energyCeiling_nonneg {E : ℝ} (f : LevyEnergySource E) : 0 ≤ E := by
  have he : 0 ≤ normalizedArchEnergy f.source := by
    unfold normalizedArchEnergy
    exact div_nonneg (biScaleLevyEnergy_nonneg f.source.hasCompactSupport f.source.continuous)
      f.mass_pos.le
  exact he.trans f.energy_le

/-- The first-order normalized deficit has the exact logarithmic energy coefficient four. -/
theorem normalized_deficit_mul_log_le {E : ℝ} (f : LevyEnergySource E)
    {t : ℝ} (ht : 0 < |t|) (ht1 : |t| ≤ 1) :
    Real.exp (-(1 / 2 : ℝ)) * (1 - f.correlation t) * (-Real.log |t|) ≤ 4 * E := by
  have hb := div_le_div_of_nonneg_right
    (autocorr_increment_mul_log_le f.smooth f.source.hasCompactSupport ht ht1) f.mass_pos.le
  calc
    _ = (Real.exp (-(1 / 2 : ℝ)) *
        (autocorr f.source 0 - autocorr f.source |t|) * (-Real.log |t|)) /
        autocorr f.source 0 := by
      rw [← f.correlation_abs t, LevyEnergySource.correlation]
      field_simp [f.mass_pos.ne']
    _ ≤ (4 * biScaleLevyEnergy f.source) / autocorr f.source 0 := hb
    _ = 4 * normalizedArchEnergy f.source := by unfold normalizedArchEnergy; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left f.energy_le (by norm_num)

/-- The exact collar radius obtained from the first-order deficit estimate. -/
def firstOrderCollarRadius (E : ℝ) : ℝ :=
  Real.exp (-1 - 8 * E / Real.exp (-(1 / 2 : ℝ)))

theorem firstOrderCollarRadius_pos (E : ℝ) : 0 < firstOrderCollarRadius E := Real.exp_pos _

/-- The closed collar of the stated radius has normalized correlation strictly above one half. -/
theorem correlation_firstOrderCollar {E : ℝ} (f : LevyEnergySource E) {t : ℝ}
    (ht : |t| ≤ firstOrderCollarRadius E) : 1 / 2 < f.correlation t := by
  by_cases ht0 : t = 0
  · rw [ht0, f.correlation_zero]
    norm_num
  let c := Real.exp (-(1 / 2 : ℝ))
  let q := 1 + 8 * E / c
  have hc : 0 < c := Real.exp_pos _
  have hE := energyCeiling_nonneg f
  have hq : 0 < q := by
    have hnonneg := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hE) hc.le
    dsimp only [q]
    linarith only [hnonneg]
  have hexp : |t| ≤ Real.exp (-q) := by
    convert ht using 1
    unfold firstOrderCollarRadius
    dsimp only [q, c]
    congr 1
    ring
  have htpos : 0 < |t| := abs_pos.mpr ht0
  have ht1 : |t| ≤ 1 := hexp.trans (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hq.le))
  have hl := Real.log_le_log htpos hexp
  rw [Real.log_exp] at hl
  have hlog : q ≤ -Real.log |t| := by linarith only [hl]
  have hqe : c * q = c + 8 * E := by dsimp only [q]; field_simp [hc.ne']
  have hb := normalized_deficit_mul_log_le f htpos ht1
  change c * (1 - f.correlation t) * (-Real.log |t|) ≤ 4 * E at hb
  by_contra h
  have hf : f.correlation t ≤ 1 / 2 := le_of_not_gt h
  have hm := mul_le_mul_of_nonneg_right
    (show (1 : ℝ) / 2 ≤ 1 - f.correlation t by linarith only [hf])
    (mul_nonneg hc.le (hq.le.trans hlog))
  have hqmul := mul_le_mul_of_nonneg_left hlog hc.le
  nlinarith only [hb, hm, hqmul, hqe, hc]

/-- The logarithmic squared-increment estimate gives a closed-radius global modulus. -/
theorem correlation_logarithmic_modulus {E η : ℝ} (f : LevyEnergySource E)
    (hη : 0 < η) (hη1 : η < 1) {x y : ℝ} (hxy : |x - y| ≤ η) :
    |f.correlation x - f.correlation y| ≤
      Real.sqrt (8 * E / (Real.exp (-(1 / 2 : ℝ)) * (-Real.log η))) := by
  by_cases heq : x = y
  · rw [heq, sub_self, abs_zero]
    exact Real.sqrt_nonneg _
  have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr heq)
  have hc : 0 < Real.exp (-(1 / 2 : ℝ)) := Real.exp_pos _
  have hlogη : 0 < -Real.log η := neg_pos.mpr (Real.log_neg hη hη1)
  have hw := mul_pos hc hlogη
  have hl : -Real.log η ≤ -Real.log |x - y| := neg_le_neg (Real.log_le_log hd hxy)
  have hb := normalized_autocorr_difference_sq_mul_log_le
    f.smooth f.source.hasCompactSupport f.mass_pos hd (hxy.trans hη1.le)
  change Real.exp (-(1 / 2 : ℝ)) * (-Real.log |x - y|) *
    (f.correlation x - f.correlation y) ^ 2 ≤ 8 * normalizedArchEnergy f.source at hb
  have hbE := hb.trans (mul_le_mul_of_nonneg_left f.energy_le (by norm_num))
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl hc.le)
    (sq_nonneg (f.correlation x - f.correlation y))
  have hs : (f.correlation x - f.correlation y) ^ 2 ≤
      8 * E / (Real.exp (-(1 / 2 : ℝ)) * (-Real.log η)) :=
    (le_div_iff₀ hw).mpr (by simpa only [mul_comm] using hm.trans hbE)
  have hn : 0 ≤ 8 * E / (Real.exp (-(1 / 2 : ℝ)) * (-Real.log η)) :=
    div_nonneg (mul_nonneg (by norm_num) (energyCeiling_nonneg f)) hw.le
  nlinarith only [hs, Real.sq_sqrt hn,
    Real.sqrt_nonneg (8 * E / (Real.exp (-(1 / 2 : ℝ)) * (-Real.log η))),
    sq_abs (f.correlation x - f.correlation y),
    abs_nonneg (f.correlation x - f.correlation y)]

/-- The existing exponential continuity radius controls its closed ball as well. -/
theorem correlation_close_closed {E ε : ℝ} (f : LevyEnergySource E)
    (hε : 0 < ε) {x y : ℝ} (hxy : |x - y| ≤ continuityRadius E ε) :
    |f.correlation x - f.correlation y| ≤ ε := by
  have hE := energyCeiling_nonneg f
  let c := Real.exp (-(1 / 2 : ℝ))
  have hc : 0 < c := Real.exp_pos _
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hq : 0 < 1 + 8 * E / (c * ε ^ 2) := by positivity
  have hη1 : continuityRadius E ε < 1 := by
    rw [continuityRadius, max_eq_left hE, Real.exp_lt_one_iff]
    exact neg_neg_of_pos hq
  apply (correlation_logarithmic_modulus f (continuityRadius_pos E ε) hη1 hxy).trans
  apply (Real.sqrt_le_iff).mpr
  refine ⟨hε.le, ?_⟩
  have hlog : -Real.log (continuityRadius E ε) = 1 + 8 * E / (c * ε ^ 2) := by
    rw [continuityRadius, Real.log_exp, neg_neg, max_eq_left hE]
  rw [hlog]
  change 8 * E / (c * (1 + 8 * E / (c * ε ^ 2))) ≤ ε ^ 2
  apply (div_le_iff₀ (mul_pos hc hq)).mpr
  have he : ε ^ 2 * (c * (1 + 8 * E / (c * ε ^ 2))) = c * ε ^ 2 + 8 * E := by
    field_simp [hc.ne', hε.ne']
  rw [he]
  exact le_add_of_nonneg_left (mul_nonneg hc.le hε2.le)

/-- The stated mesh radius is the existing continuity radius at one quarter of the target accuracy. -/
theorem continuityRadius_quarter_eq {E ε : ℝ} (hE : 0 ≤ E) :
    continuityRadius E (ε / 4) =
      Real.exp (-1 - 128 * E / (Real.exp (-(1 / 2 : ℝ)) * ε ^ 2)) := by
  unfold continuityRadius
  rw [max_eq_left hE]
  congr 1
  by_cases hε : ε = 0
  · simp only [hε, zero_div, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero,
      div_zero, add_zero, sub_zero]
  · field_simp [hε, (Real.exp_pos (-(1 / 2 : ℝ))).ne']
    ring

end GaloisForLFunctions.BiScaleUncertainty.EnergyCycle
