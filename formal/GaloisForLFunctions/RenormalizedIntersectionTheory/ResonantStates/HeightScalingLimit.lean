import GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.HeightProbabilityLaw

/-!
# Rescaled height law and escape from fixed heights

The rescaled height marginal differs from the power-law probability by a
cutoff-one component and a missing lower tail of equal mass. This gives an
error bound for every bounded measurable test, uniformly in spectral ordinate.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry RHTower
open scoped ENNReal

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates

noncomputable section

/-- Dilation of a positive-height power band. -/
theorem heightPowerBand_rescale (g : ℝ → ℝ) (κ : ℝ) {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ y in Ioc 1 Y, g (y / Y) * y ^ (κ - 1)) =
      Y ^ κ * ∫ t in Ioc (1 / Y) 1, g t * t ^ (κ - 1) := by
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hi : 1 / Y ≤ 1 := (div_le_iff₀ hY0).mpr (by simpa using hY)
  rw [← intervalIntegral.integral_of_le hY, ← intervalIntegral.integral_of_le hi]
  calc
    _ = Y ^ (κ - 1) * ∫ y in (1 : ℝ)..Y, g (y / Y) * (y / Y) ^ (κ - 1) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro y hy
      rw [uIcc_of_le hY] at hy
      dsimp only
      rw [Real.div_rpow (zero_lt_one.trans_le hy.1).le hY0.le]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hY0 (κ - 1))]
    _ = _ := by
      rw [intervalIntegral.integral_comp_div (fun t => g t * t ^ (κ - 1)) hY0.ne',
        div_self hY0.ne', smul_eq_mul, ← mul_assoc]
      have hp : Y ^ (κ - 1) * Y = Y ^ κ := by
        conv_lhs => rhs; rw [← Real.rpow_one Y]
        rw [← Real.rpow_add hY0]
        congr 1
        ring
      rw [hp]

/-- The lower power-law tail has exactly the mass controlling every bounded test. -/
theorem heightPowerBand_tail_bound (g : ℝ → ℝ) {M κ b : ℝ} (hM : ∀ y, ‖g y‖ ≤ M)
    (hk : 0 < κ) (hb : 0 ≤ b) :
    |κ * ∫ y in Ioc 0 b, g y * y ^ (κ - 1)| ≤ M * b ^ κ := by
  letI := heightPowerBand_finite_of_pos (a := 0) (b := b) hk
  have h := norm_integral_le_of_norm_le_const
    (μ := heightPowerBand κ 0 b) (Eventually.of_forall hM)
  rw [integral_heightPowerBand _ le_rfl, Real.norm_eq_abs, Measure.real_def,
    heightPowerBand_mass hk le_rfl hb, Real.zero_rpow hk.ne', sub_zero,
    ENNReal.toReal_ofReal (div_nonneg (Real.rpow_nonneg hb _) hk.le)] at h
  rw [abs_mul, abs_of_pos hk]
  calc
    _ ≤ κ * (M * (b ^ κ / κ)) := mul_le_mul_of_nonneg_left h hk.le
    _ = M * b ^ κ := by field_simp

private theorem heightPowerBand_test_split (g : ℝ → ℝ) (hg : Measurable g) {M κ c : ℝ}
    (hM : ∀ y, ‖g y‖ ≤ M) (hk : 0 < κ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    (∫ y in Ioc 0 c, g y * y ^ (κ - 1)) +
        (∫ y in Ioc c 1, g y * y ^ (κ - 1)) =
      ∫ y in Ioc 0 1, g y * y ^ (κ - 1) := by
  have hi (a b : ℝ) : IntegrableOn (fun y => g y * y ^ (κ - 1)) (Ioc a b) := by
    have hp : IntegrableOn (fun y : ℝ => y ^ (κ - 1)) (Ioc a b) :=
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < κ - 1)).1
    exact hp.bdd_mul hg.aestronglyMeasurable (Eventually.of_forall hM)
  have h₁ := (intervalIntegrable_iff_integrableOn_Ioc_of_le hc).mpr (hi 0 c)
  have h₂ := (intervalIntegrable_iff_integrableOn_Ioc_of_le hc1).mpr (hi c 1)
  have h := intervalIntegral.integral_add_adjacent_intervals h₁ h₂
  rwa [intervalIntegral.integral_of_le hc, intervalIntegral.integral_of_le hc1,
    intervalIntegral.integral_of_le zero_le_one] at h

/-- The power-law probability with density `κ t^(κ-1)` on `(0,1]`. -/
def powerHeightProbabilityMeasure (κ : ℝ) : Measure ℝ :=
  ENNReal.ofReal κ • heightPowerBand κ 0 1

theorem powerHeightProbabilityMeasure_probability {κ : ℝ} (hk : 0 < κ) :
    IsProbabilityMeasure (powerHeightProbabilityMeasure κ) := by
  rw [isProbabilityMeasure_iff, powerHeightProbabilityMeasure, Measure.smul_apply, smul_eq_mul,
    heightPowerBand_mass hk le_rfl zero_le_one, Real.one_rpow, Real.zero_rpow hk.ne', sub_zero,
    ← ENNReal.ofReal_mul hk.le]
  have he : κ * (1 / κ) = 1 := by field_simp
  rw [he, ENNReal.ofReal_one]

theorem integral_powerHeightProbabilityMeasure {κ : ℝ} (hk : 0 < κ) (g : ℝ → ℝ) :
    (∫ t, g t ∂powerHeightProbabilityMeasure κ) =
      κ * ∫ t in Ioc 0 1, g t * t ^ (κ - 1) := by
  rw [powerHeightProbabilityMeasure, integral_smul_measure, ENNReal.toReal_ofReal hk.le,
    smul_eq_mul, integral_heightPowerBand _ le_rfl]

/-- The exact probability mixture acts on every bounded measurable height test. -/
theorem integral_resonant_heightProbabilityMeasure {u : ℂ} (hu : u ∈ eisensteinLineDomain)
    (hur : u.re < 0) (hAu : msA u = 0) {Y : ℝ} (hY : 1 ≤ Y)
    (g : ℝ → ℝ) (hg : Measurable g) {M : ℝ} (hM : ∀ y, ‖g y‖ ≤ M) :
    (∫ y, g y ∂heightProbabilityMeasure u Y) =
      Y ^ (2 * u.re) * (∫ y, g y ∂heightProbabilityMeasure u 1) +
        ((-2 * u.re) * Y ^ (2 * u.re)) * ∫ y in Ioc 1 Y, g y * y ^ (-2 * u.re - 1) := by
  letI := heightProbabilityMeasure_probability hu hur hAu (Y := 1) le_rfl
  letI := heightPowerBand_finite (-2 * u.re) (b := Y) zero_lt_one
  letI := (heightProbabilityMeasure u 1).smul_finite
    (c := ENNReal.ofReal (Y ^ (2 * u.re))) ENNReal.ofReal_ne_top
  letI := (heightPowerBand (-2 * u.re) 1 Y).smul_finite
    (c := ENNReal.ofReal ((-2 * u.re) * Y ^ (2 * u.re))) ENNReal.ofReal_ne_top
  have hi₁ : Integrable g (ENNReal.ofReal (Y ^ (2 * u.re)) • heightProbabilityMeasure u 1) :=
    (integrable_const M).mono' hg.aestronglyMeasurable (Eventually.of_forall hM)
  have hi₂ : Integrable g (ENNReal.ofReal ((-2 * u.re) * Y ^ (2 * u.re)) •
      heightPowerBand (-2 * u.re) 1 Y) :=
    (integrable_const M).mono' hg.aestronglyMeasurable (Eventually.of_forall hM)
  have hd : 0 ≤ Y ^ (2 * u.re) := Real.rpow_nonneg (zero_lt_one.trans_le hY).le _
  rw [resonant_heightProbabilityMeasure hu hur hAu hY,
    integral_add_measure hi₁ hi₂,
    integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal hd, ENNReal.toReal_ofReal (mul_nonneg (by linarith) hd),
    smul_eq_mul, smul_eq_mul, integral_heightPowerBand _ zero_le_one]

/-- Uniform bounded-measurable error for the rescaled actual height marginal. -/
theorem resonant_rescaled_height_error {u : ℂ} (hu : u ∈ eisensteinLineDomain)
    (hur : u.re < 0) (hAu : msA u = 0) {Y : ℝ} (hY : 1 ≤ Y)
    (g : ℝ → ℝ) (hg : Measurable g) {M : ℝ} (hM : ∀ y, ‖g y‖ ≤ M) :
    |(∫ y, g (y / Y) ∂heightProbabilityMeasure u Y) -
        (∫ t, g t ∂powerHeightProbabilityMeasure (-2 * u.re))| ≤
      2 * M * Y ^ (2 * u.re) := by
  have hk : 0 < -2 * u.re := by linarith
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hc0 : 0 ≤ 1 / Y := by positivity
  have hc1 : 1 / Y ≤ 1 := (div_le_iff₀ hY0).mpr (by simpa using hY)
  have hd : 0 ≤ Y ^ (2 * u.re) := Real.rpow_nonneg hY0.le _
  have hn : Y ^ (2 * u.re) = (Y ^ (-2 * u.re))⁻¹ := by
    rw [show 2 * u.re = -(-2 * u.re) by ring, Real.rpow_neg hY0.le]
  have hc : (1 / Y) ^ (-2 * u.re) = Y ^ (2 * u.re) := by
    rw [Real.div_rpow zero_le_one hY0.le, Real.one_rpow, one_div, hn]
  have hcancel : Y ^ (2 * u.re) * Y ^ (-2 * u.re) = 1 := by
    rw [← Real.rpow_add hY0, show 2 * u.re + -2 * u.re = 0 by ring, Real.rpow_zero]
  have hgY : Measurable (fun y => g (y / Y)) := hg.comp (measurable_id.div_const Y)
  have hMY : ∀ y, ‖g (y / Y)‖ ≤ M := fun y => hM (y / Y)
  have he := integral_resonant_heightProbabilityMeasure hu hur hAu hY
    (fun y => g (y / Y)) hgY hMY
  rw [heightPowerBand_rescale g (-2 * u.re) hY] at he
  have hmul (J : ℝ) : ((-2 * u.re) * Y ^ (2 * u.re)) * (Y ^ (-2 * u.re) * J) =
      (-2 * u.re) * J := by
    calc
      _ = (-2 * u.re) * (Y ^ (2 * u.re) * Y ^ (-2 * u.re)) * J := by ring
      _ = _ := by rw [hcancel, mul_one]
  rw [hmul] at he
  have hsplit := heightPowerBand_test_split g hg hM hk hc0 hc1
  letI := heightProbabilityMeasure_probability hu hur hAu (Y := 1) le_rfl
  have hbase : |∫ y, g (y / Y) ∂heightProbabilityMeasure u 1| ≤ M := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := heightProbabilityMeasure u 1)
        (Eventually.of_forall hMY))
  have htail := heightPowerBand_tail_bound g hM hk hc0
  rw [hc] at htail
  rw [integral_powerHeightProbabilityMeasure hk]
  have herr : (∫ y, g (y / Y) ∂heightProbabilityMeasure u Y) -
      (-2 * u.re) * (∫ t in Ioc 0 1, g t * t ^ (-2 * u.re - 1)) =
      Y ^ (2 * u.re) * (∫ y, g (y / Y) ∂heightProbabilityMeasure u 1) -
        (-2 * u.re) * (∫ t in Ioc 0 (1 / Y), g t * t ^ (-2 * u.re - 1)) := by
    linear_combination he + (-2 * u.re) * hsplit
  rw [herr]
  calc
    _ ≤ |Y ^ (2 * u.re) * (∫ y, g (y / Y) ∂heightProbabilityMeasure u 1)| +
        |(-2 * u.re) * (∫ t in Ioc 0 (1 / Y), g t * t ^ (-2 * u.re - 1))| := abs_sub _ _
    _ ≤ Y ^ (2 * u.re) * M + M * Y ^ (2 * u.re) := by
      apply add_le_add _ htail
      rw [abs_mul, abs_of_nonneg hd]
      exact mul_le_mul_of_nonneg_left hbase hd
    _ = _ := by ring

/-- At every fixed height the normalized mass is bounded by the cutoff norm ratio. -/
theorem resonant_height_local_mass {u : ℂ} (hu : u ∈ eisensteinLineDomain)
    (hur : u.re < 0) (hAu : msA u = 0) {C Y : ℝ} (hC : 1 ≤ C) (hCY : C ≤ Y) :
    heightProbabilityMeasure u Y (Ioc 0 C) ≤ ENNReal.ofReal ((C / Y) ^ (-2 * u.re)) := by
  have hk : 0 < -2 * u.re := by linarith
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hY : 1 ≤ Y := hC.trans hCY
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hd : 0 ≤ Y ^ (2 * u.re) := Real.rpow_nonneg hY0.le _
  have hp : 0 < Y ^ (-2 * u.re) := Real.rpow_pos_of_pos hY0 _
  have hCpow : 1 ≤ C ^ (-2 * u.re) := Real.one_le_rpow hC hk.le
  have hn : Y ^ (2 * u.re) = (Y ^ (-2 * u.re))⁻¹ := by
    rw [show 2 * u.re = -(-2 * u.re) by ring, Real.rpow_neg hY0.le]
  letI := heightProbabilityMeasure_probability hu hur hAu (Y := 1) le_rfl
  have hm : heightProbabilityMeasure u 1 (Ioc 0 C) ≤ 1 := by
    simpa only [measure_univ] using
      (measure_mono (μ := heightProbabilityMeasure u 1) (subset_univ (Ioc 0 C)))
  rw [resonant_heightProbabilityMeasure hu hur hAu hY, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    heightPowerBand_below hCY, heightPowerBand_mass hk zero_le_one hC, Real.one_rpow]
  calc
    _ ≤ ENNReal.ofReal (Y ^ (2 * u.re)) +
        ENNReal.ofReal ((-2 * u.re) * Y ^ (2 * u.re)) *
          ENNReal.ofReal ((C ^ (-2 * u.re) - 1) / (-2 * u.re)) := by
      apply add_le_add
      · simpa only [mul_one] using mul_le_mul_right hm (ENNReal.ofReal (Y ^ (2 * u.re)))
      · exact le_rfl
    _ = _ := by
      have hq : 0 ≤ (C ^ (-2 * u.re) - 1) / (-2 * u.re) :=
        div_nonneg (sub_nonneg.mpr hCpow) hk.le
      rw [← ENNReal.ofReal_mul (mul_nonneg hk.le hd),
        ← ENNReal.ofReal_add hd (mul_nonneg (mul_nonneg hk.le hd) hq),
        Real.div_rpow hC0.le hY0.le]
      congr 1
      rw [hn]
      field_simp [hur.ne, hp.ne']
      ring

/-- A uniform rate bound holds for all cutoffs, including those below the test height. -/
theorem resonant_height_escape_bound {u : ℂ} (hu : u ∈ eisensteinLineDomain)
    (hur : u.re < 0) (hAu : msA u = 0) {C Y ε : ℝ} (hC : 1 ≤ C) (hY : 1 ≤ Y)
    (hε : 0 < ε) (hκ : ε ≤ -2 * u.re) :
    (heightProbabilityMeasure u Y).real (Ioc 0 C) ≤ (C / Y) ^ ε := by
  letI := heightProbabilityMeasure_probability hu hur hAu hY
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  by_cases hCY : C ≤ Y
  · have h := (ENNReal.toReal_le_toReal
        (measure_ne_top (heightProbabilityMeasure u Y) (Ioc 0 C)) ENNReal.ofReal_ne_top).mpr
      (resonant_height_local_mass hu hur hAu hC hCY)
    have hb : (heightProbabilityMeasure u Y).real (Ioc 0 C) ≤ (C / Y) ^ (-2 * u.re) := by
      simpa only [Measure.real_def,
        ENNReal.toReal_ofReal (Real.rpow_nonneg (div_nonneg hC0.le hY0.le) _)] using h
    exact hb.trans (Real.rpow_le_rpow_of_exponent_ge (div_pos hC0 hY0)
      ((div_le_iff₀ hY0).mpr (by simpa using hCY)) hκ)
  · have hb : (heightProbabilityMeasure u Y).real (Ioc 0 C) ≤ 1 := by
      simpa only [probReal_univ] using
        (measureReal_mono (μ := heightProbabilityMeasure u Y) (subset_univ (Ioc 0 C)))
    exact hb.trans (Real.one_le_rpow
      ((le_div_iff₀ hY0).mpr (by simpa using (lt_of_not_ge hCY).le)) hε.le)

/-- Cutoffs tending to infinity lose all mass at bounded height, uniformly in ordinate. -/
theorem resonant_height_mass_tendsto_zero (u : ℕ → ℂ) (Y : ℕ → ℝ)
    (hu : ∀ n, u n ∈ eisensteinLineDomain) (hur : ∀ n, (u n).re < 0)
    (hAu : ∀ n, msA (u n) = 0) (hY : ∀ n, 1 ≤ Y n)
    {ε C : ℝ} (hε : 0 < ε) (hκ : ∀ n, ε ≤ -2 * (u n).re) (hC : 1 ≤ C)
    (hYtop : Tendsto Y atTop atTop) :
    Tendsto (fun n => (heightProbabilityMeasure (u n) (Y n)).real (Ioc 0 C)) atTop (𝓝 0) := by
  have hp : Tendsto (fun n => (C / Y n) ^ ε) atTop (𝓝 0) := by
    have h := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).div_atTop hYtop).rpow_const
      (Or.inr hε.le)
    simpa only [Real.zero_rpow hε.ne'] using h
  exact squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => resonant_height_escape_bound (hu n) (hur n) (hAu n) hC (hY n) hε (hκ n)) hp

end

end GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates

#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.powerHeightProbabilityMeasure_probability
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.resonant_rescaled_height_error
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.resonant_height_local_mass
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.resonant_height_escape_bound
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.resonant_height_mass_tendsto_zero
