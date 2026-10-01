import GaloisForLFunctions.RHTower.PMAnalyticPowerBoundary
import GaloisForLFunctions.RHTower.PMPowerIncrementSeries

/-!
# Rescaling the power model without losing its canonical variance

A positive amplitude at most one preserves the comparison model's analytic
bounds and PNT normalization. Its centered variance controls the original power
variance up to one finite initial-cell error. The positive amplitude cancelling
the affine prime-weighted response is uniquely `1 / (2 * Sσ - 1)`.
-/

open MeasureTheory Filter Topology Set
noncomputable section
namespace RHTower

def pmPowerUnitStep (x : ℝ) : ℝ := (Ioi (1 : ℝ)).indicator (fun _ => 1) x

def pmScaledPowerProfile (σ c x : ℝ) : ℝ :=
  c * pmPowerProfile σ x + (1 - c) * pmPowerUnitStep x

def pmScaledPowerModel (σ c x : ℝ) : ℝ := x * pmScaledPowerProfile σ c x

theorem pmScaledPowerModel_eq (σ c x : ℝ) :
    pmScaledPowerModel σ c x = if x ≤ 1 then 0 else x + c * x ^ σ := by
  by_cases hx : x ≤ 1
  · simp [pmScaledPowerModel, pmScaledPowerProfile, pmPowerProfile, pmPowerModel,
      pmPowerUnitStep, hx, not_lt.mpr hx]
  · have hx0 : 0 < x := lt_trans zero_lt_one (lt_of_not_ge hx)
    simp only [pmScaledPowerModel, pmScaledPowerProfile, pmPowerProfile, pmPowerModel,
      if_neg hx]
    simp [pmPowerUnitStep, lt_of_not_ge hx]
    field_simp [hx0.ne']
    ring

theorem pmScaledPowerProfile_one (σ x : ℝ) :
    pmScaledPowerProfile σ 1 x = pmPowerProfile σ x := by
  simp [pmScaledPowerProfile]

theorem pmScaledPowerProfile_bounds {σ c : ℝ} (hσ : σ ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (x : ℝ) :
    0 ≤ pmScaledPowerProfile σ c x ∧ pmScaledPowerProfile σ c x ≤ 2 := by
  have hf := pmPowerProfile_bounds hσ x
  have hi : 0 ≤ pmPowerUnitStep x ∧ pmPowerUnitStep x ≤ 1 := by
    by_cases hx : 1 < x <;> simp [pmPowerUnitStep, hx]
  constructor
  · exact add_nonneg (mul_nonneg hc0 hf.1) (mul_nonneg (sub_nonneg.mpr hc1) hi.1)
  · have h1 := mul_le_mul_of_nonneg_left hf.2 hc0
    have h2 := mul_le_mul_of_nonneg_left hi.2 (sub_nonneg.mpr hc1)
    dsimp [pmScaledPowerProfile]
    nlinarith

theorem measurable_pmScaledPowerProfile {σ : ℝ} (hσ : 0 ≤ σ) (c : ℝ) :
    Measurable (pmScaledPowerProfile σ c) :=
  ((measurable_pmPowerProfile hσ).const_mul c).add
    ((measurable_const.indicator measurableSet_Ioi).const_mul (1 - c))

theorem measurable_pmScaledPowerModel {σ : ℝ} (hσ : 0 ≤ σ) (c : ℝ) :
    Measurable (pmScaledPowerModel σ c) :=
  measurable_id.mul (measurable_pmScaledPowerProfile hσ c)

theorem pmScaledPowerModel_div {σ c x : ℝ} (hx : x ≠ 0) :
    pmScaledPowerModel σ c x / x = pmScaledPowerProfile σ c x := by
  rw [pmScaledPowerModel]
  field_simp [hx]

theorem pmScaledPowerModel_le_two_mul {σ c x : ℝ} (hσ : σ ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hx : 0 ≤ x) :
    pmScaledPowerModel σ c x ≤ 2 * x := by
  simpa only [pmScaledPowerModel, mul_comm x 2] using
    mul_le_mul_of_nonneg_left (pmScaledPowerProfile_bounds hσ hc0 hc1 x).2 hx

theorem abs_pmScaledPowerModel_error_le {σ c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (x : ℝ) :
    |pmScaledPowerModel σ c x - x| ≤ |pmPowerModel σ x - x| := by
  rw [pmScaledPowerModel_eq, pmPowerModel]
  split_ifs with hx
  · exact le_refl _
  · have hp := Real.rpow_nonneg (show 0 ≤ x by linarith) σ
    rw [add_sub_cancel_left, add_sub_cancel_left, abs_of_nonneg (mul_nonneg hc0 hp),
      abs_of_nonneg hp]
    exact mul_le_of_le_one_left hp hc1

theorem pmScaledPowerModel_nonneg {σ c : ℝ} (hc : 0 ≤ c) (x : ℝ) :
    0 ≤ pmScaledPowerModel σ c x := by
  rw [pmScaledPowerModel_eq]
  split_ifs with hx
  · exact le_refl _
  · have hx0 : 0 ≤ x := (lt_trans zero_lt_one (lt_of_not_ge hx)).le
    exact add_nonneg hx0 (mul_nonneg hc (Real.rpow_nonneg hx0 σ))

theorem pmScaledPowerModel_monotone {σ c : ℝ} (hσ : 0 ≤ σ) (hc : 0 ≤ c) :
    Monotone (pmScaledPowerModel σ c) := by
  intro x y hxy
  rw [pmScaledPowerModel_eq, pmScaledPowerModel_eq]
  by_cases hx : x ≤ 1
  · rw [if_pos hx]
    rw [← pmScaledPowerModel_eq]
    exact pmScaledPowerModel_nonneg hc y
  · have hy : ¬y ≤ 1 := by linarith
    rw [if_neg hx, if_neg hy]
    exact add_le_add hxy (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by linarith : 0 ≤ x) hxy hσ) hc)

theorem tendsto_pmScaledPowerProfile_one {σ : ℝ} (hσ : σ < 1) (c : ℝ) :
    Tendsto (pmScaledPowerProfile σ c) atTop (𝓝 1) := by
  have ht := ((tendsto_pmPowerProfile_one hσ).const_mul c).add_const (1 - c)
  have he : c * 1 + (1 - c) = 1 := by ring
  rw [he] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 1] with x hx
  simp [pmScaledPowerProfile, pmPowerUnitStep, hx]

theorem integrableOn_pmScaledPower_error_sq {σ c : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (B R : ℝ) :
    IntegrableOn (fun x => (B - pmScaledPowerProfile σ c x) ^ 2) (Ioo 0 R) := by
  refine Measure.integrableOn_of_bounded (M := (|B| + 2) ^ 2) measure_Ioo_lt_top.ne
    ((measurable_const.sub (measurable_pmScaledPowerProfile hσ0 c)).pow_const 2).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    apply pow_le_pow_left₀ (abs_nonneg _) _ 2
    calc
      _ ≤ |B| + |pmScaledPowerProfile σ c x| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le B (-pmScaledPowerProfile σ c x)
      _ ≤ _ := by rw [abs_of_nonneg (pmScaledPowerProfile_bounds hσ1 hc0 hc1 x).1]
                  exact add_le_add (le_refl _) (pmScaledPowerProfile_bounds hσ1 hc0 hc1 x).2

theorem integral_pmPower_initialCell {R : ℝ} (hR : 1 < R) :
    (∫ x in Ioo (0 : ℝ) R, (Iic (1 : ℝ)).indicator (fun _ => (1 : ℝ)) x) = 1 := by
  rw [setIntegral_indicator measurableSet_Iic]
  have hs : Ioo (0 : ℝ) R ∩ Iic 1 = Ioc 0 1 := by
    ext x
    simp only [mem_inter_iff, mem_Ioo, mem_Iic, mem_Ioc]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, lt_of_le_of_lt h.2 hR⟩, h.2⟩
  rw [hs]
  simp

theorem pmScaledPower_error_lower {σ c R : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hR : 1 < R) (B : ℝ) :
    c ^ 2 * (∫ x in Ioo (0 : ℝ) R,
      ((B - 1 + c) / c - pmPowerProfile σ x) ^ 2) ≤
        2 * (∫ x in Ioo (0 : ℝ) R, (B - pmScaledPowerProfile σ c x) ^ 2) +
          2 * (1 - c) ^ 2 := by
  let g := fun x : ℝ => (Iic (1 : ℝ)).indicator (fun _ => (1 : ℝ)) x
  have hg : IntegrableOn g (Ioo (0 : ℝ) R) :=
    (integrableOn_const (C := (1 : ℝ)) (s := Ioo (0 : ℝ) R)
      measure_Ioo_lt_top.ne).indicator measurableSet_Iic
  have hf := integrableOn_pmScaledPower_error_sq hσ0 hσ1 hc0.le hc1 B R
  have hb : IntegrableOn (fun x => ((B - 1 + c) / c - pmPowerProfile σ x) ^ 2)
      (Ioo (0 : ℝ) R) := by
    simpa only [pmScaledPowerProfile_one] using
      integrableOn_pmScaledPower_error_sq hσ0 hσ1 (by norm_num : (0 : ℝ) ≤ 1)
        (le_refl (1 : ℝ)) ((B - 1 + c) / c) R
  have hp (x : ℝ) : c ^ 2 * ((B - 1 + c) / c - pmPowerProfile σ x) ^ 2 ≤
      2 * (B - pmScaledPowerProfile σ c x) ^ 2 + 2 * (1 - c) ^ 2 * g x := by
    have he : c * ((B - 1 + c) / c - pmPowerProfile σ x) =
        B - pmScaledPowerProfile σ c x - (1 - c) * g x := by
      by_cases hx : x ≤ 1
      · simp [pmScaledPowerProfile, pmPowerUnitStep, g, hx, not_lt.mpr hx]
        field_simp [hc0.ne']
        ring
      · simp [pmScaledPowerProfile, pmPowerUnitStep, g, hx, lt_of_not_ge hx]
        field_simp [hc0.ne']
        ring
    have hi : g x = 0 ∨ g x = 1 := by
      by_cases hx : x ≤ 1 <;> simp [g, hx]
    rw [← mul_pow, he]
    rcases hi with hi | hi <;> rw [hi]
    · nlinarith [sq_nonneg (B - pmScaledPowerProfile σ c x)]
    · nlinarith [sq_nonneg (B - pmScaledPowerProfile σ c x + (1 - c))]
  have ht := integral_mono_ae (hb.const_mul (c ^ 2))
    ((hf.const_mul 2).add (hg.const_mul (2 * (1 - c) ^ 2)))
    (Filter.Eventually.of_forall hp)
  simp only [Pi.add_apply] at ht
  rw [integral_const_mul, integral_add (hf.const_mul 2) (hg.const_mul _),
    integral_const_mul, integral_const_mul] at ht
  change c ^ 2 * _ ≤ 2 * _ + 2 * (1 - c) ^ 2 *
    (∫ x in Ioo (0 : ℝ) R, (Iic (1 : ℝ)).indicator (fun _ => (1 : ℝ)) x) at ht
  rw [integral_pmPower_initialCell hR, mul_one] at ht
  exact ht

theorem tendsto_pmScaledPowerProfile_error_div_log_sq {σ c : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (hc0 : 0 < c) (hc1 : c ≤ 1) (B : ℝ → ℝ) :
    Tendsto (fun R : ℝ => (∫ x in Ioo (0 : ℝ) R,
      (B R - pmScaledPowerProfile σ c x) ^ 2) / Real.log R ^ 2) atTop atTop := by
  have hE := tendsto_pmPowerProfile_scalar_error_div_log_sq hσ hσ1
    (fun R => (B R - 1 + c) / c)
  apply tendsto_atTop.2
  intro b
  filter_upwards [hE.eventually (eventually_ge_atTop
    ((2 * b + 2 * (1 - c) ^ 2) / c ^ 2)),
    eventually_gt_atTop (Real.exp 1)] with R hbudget hR
  have hR1 : 1 < R := (Real.one_lt_exp_iff.mpr zero_lt_one).trans hR
  have hlog : 1 ≤ Real.log R := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hR.le
  have hlog2 : 1 ≤ Real.log R ^ 2 := by nlinarith
  have hL := div_le_div_of_nonneg_right
    (pmScaledPower_error_lower (by linarith) hσ1.le hc0 hc1 hR1 (B R))
    (sq_nonneg (Real.log R))
  let A := ∫ x in Ioo (0 : ℝ) R, ((B R - 1 + c) / c - pmPowerProfile σ x) ^ 2
  let D := ∫ x in Ioo (0 : ℝ) R, (B R - pmScaledPowerProfile σ c x) ^ 2
  change c ^ 2 * A / Real.log R ^ 2 ≤ (2 * D + 2 * (1 - c) ^ 2) / Real.log R ^ 2 at hL
  change (2 * b + 2 * (1 - c) ^ 2) / c ^ 2 ≤ A / Real.log R ^ 2 at hbudget
  change b ≤ D / Real.log R ^ 2
  have hL' : c ^ 2 * (A / Real.log R ^ 2) ≤
      2 * (D / Real.log R ^ 2) + 2 * (1 - c) ^ 2 / Real.log R ^ 2 := by
    calc
      _ = c ^ 2 * A / Real.log R ^ 2 := by ring
      _ ≤ (2 * D + 2 * (1 - c) ^ 2) / Real.log R ^ 2 := hL
      _ = _ := by ring
  have hK := div_le_self (by positivity : 0 ≤ 2 * (1 - c) ^ 2) hlog2
  have hB := (div_le_iff₀ (sq_pos_of_pos hc0)).mp hbudget
  nlinarith only [hL', hK, hB]

def pmCancellingPowerAmplitude (σ : ℝ) : ℝ := 1 / (2 * pmPowerResponse σ - 1)

theorem pmCancellingPowerAmplitude_bounds {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    0 < pmCancellingPowerAmplitude σ ∧ pmCancellingPowerAmplitude σ < 1 := by
  have hs := one_lt_pmPowerResponse hσ0 hσ1
  have hd : 0 < 2 * pmPowerResponse σ - 1 := by linarith
  exact ⟨one_div_pos.mpr hd, (div_lt_one hd).mpr (by linarith)⟩

theorem pmPower_affine_response_zero_iff {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (c : ℝ) :
    c * pmPowerResponse σ - (1 + c) / 2 = 0 ↔ c = pmCancellingPowerAmplitude σ := by
  have hd : 2 * pmPowerResponse σ - 1 ≠ 0 := by
    have hs := one_lt_pmPowerResponse hσ0 hσ1
    linarith
  rw [pmCancellingPowerAmplitude, eq_div_iff hd]
  constructor <;> intro h <;> nlinarith

end RHTower
