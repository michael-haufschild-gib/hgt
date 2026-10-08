import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseRegularization
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A logarithmic bound for the phase-window kernel

Integrating the endpoint distance, instead of a single cutoff, retains the
logarithmic Poisson smoothing rate. The final weight adapts to the height.
-/

open Complex Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RHTower.WeilWorkSettledPhase

/-- A continuous endpoint envelope, including the two jump locations. -/
theorem windowError_le_endpoint_envelope {η y r : ℝ} (hη : 0 < η) (hy : 0 ≤ y) :
    windowError η y r ≤ 8 * η / (η + |y - r|) + 8 * η / (η + |y + r|) := by
  let d := min |y - r| |y + r|
  have hd : 0 ≤ d := le_min (abs_nonneg _) (abs_nonneg _)
  have hb : windowError η y r ≤ 8 * η / (η + d) := by
    by_cases h : d ≤ η
    · refine (windowError_le_pi hη hy r).trans ?_
      apply (le_div_iff₀ (by positivity : 0 < η + d)).mpr
      nlinarith [Real.pi_lt_four, Real.pi_pos]
    · have hpos : 0 < d := hη.trans (lt_of_not_ge h)
      refine (windowError_le_endpoint hη hpos hy (min_le_right _ _) (min_le_left _ _)).trans ?_
      apply (div_le_div_iff₀ hpos (by positivity : 0 < η + d)).mpr
      nlinarith
  refine hb.trans ?_
  dsimp [d]
  rcases le_total |y - r| |y + r| with h | h
  · rw [min_eq_left h]
    exact le_add_of_nonneg_right (by positivity)
  · rw [min_eq_right h]
    exact le_add_of_nonneg_left (by positivity)

private theorem integral_inv_add_abs {η R : ℝ} (hη : 0 < η) (hR : 0 ≤ R) :
    (∫ x in -R..R, (η + |x|)⁻¹) = 2 * Real.log (1 + R / η) := by
  have hc : Continuous (fun x : ℝ => (η + |x|)⁻¹) :=
    (continuous_const.add continuous_abs).inv₀ (fun _ => by dsimp; positivity)
  have hp : (∫ x in 0..R, (η + |x|)⁻¹) = Real.log (1 + R / η) := by
    calc
      (∫ x in 0..R, (η + |x|)⁻¹) = ∫ x in 0..R, (η + x)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hR] at hx
        simp only [abs_of_nonneg hx.1]
      _ = ∫ x in η..(η + R), x⁻¹ := by
        simpa only [add_zero] using intervalIntegral.integral_comp_add_left
          (fun x : ℝ => x⁻¹) η (a := 0) (b := R)
      _ = Real.log ((η + R) / η) := integral_inv_of_pos hη (by positivity)
      _ = _ := by congr 1; field_simp
  have hn : (∫ x in -R..0, (η + |x|)⁻¹) = ∫ x in 0..R, (η + |x|)⁻¹ := by
    simpa using (intervalIntegral.integral_comp_neg (fun x : ℝ => (η + |x|)⁻¹)
      (a := 0) (b := R)).symm
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-R) 0) (hc.intervalIntegrable 0 R), hn, hp]
  ring

private theorem integral_endpoint_envelope_le {η Y r : ℝ} (hη : 0 < η)
    (hY : 1 ≤ Y) (hr : |r| ≤ 4 * Y) :
    (∫ y in Ioc Y (2 * Y), (η + |y - r|)⁻¹) ≤
      2 * Real.log (1 + 6 * Y / η) := by
  have hc : Continuous (fun x : ℝ => (η + |x|)⁻¹) :=
    (continuous_const.add continuous_abs).inv₀ (fun _ => by dsimp; positivity)
  rw [← intervalIntegral.integral_of_le (by linarith : Y ≤ 2 * Y),
    intervalIntegral.integral_comp_sub_right (fun x : ℝ => (η + |x|)⁻¹) r]
  refine (intervalIntegral.integral_mono_interval (c := -(6 * Y)) (d := 6 * Y)
    (by linarith [(abs_le.mp hr).2]) (by linarith)
    (by linarith [(abs_le.mp hr).1]) (Eventually.of_forall fun x => by positivity)
    (hc.intervalIntegrable _ _)).trans_eq ?_
  exact integral_inv_add_abs hη (by linarith)

/-- Logarithmic height integral throughout the near spectral region. -/
theorem integral_windowError_le_log {η Y r : ℝ} (hη : 0 < η) (hY : 1 ≤ Y)
    (hr : |r| ≤ 4 * Y) :
    (∫ y in Ioc Y (2 * Y), windowError η y r) ≤
      32 * η * Real.log (1 + 6 * Y / η) := by
  have hi (r : ℝ) : IntegrableOn (fun y : ℝ => (η + |y - r|)⁻¹) (Ioc Y (2 * Y)) := by
    exact ((continuous_const.add (continuous_id.sub continuous_const).abs).inv₀
      (fun _ => by dsimp; positivity)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hp := integral_endpoint_envelope_le hη hY hr
  have hn := integral_endpoint_envelope_le hη hY (r := -r) (by simpa using hr)
  simp only [sub_neg_eq_add] at hn
  have hs : IntegrableOn (fun y : ℝ =>
      8 * η * (η + |y - r|)⁻¹ + 8 * η * (η + |y - -r|)⁻¹) (Ioc Y (2 * Y)) :=
    ((hi r).const_mul (8 * η)).add ((hi (-r)).const_mul (8 * η))
  have hb := setIntegral_mono_on (integrableOn_windowError hη hY r) hs measurableSet_Ioc
    (fun y hy => by
      change windowError η y r ≤ 8 * η * (η + |y - r|)⁻¹ + 8 * η * (η + |y - -r|)⁻¹
      simpa only [div_eq_mul_inv, sub_neg_eq_add] using
        windowError_le_endpoint_envelope hη (by linarith [hy.1]) (r := r))
  rw [integral_add ((hi r).const_mul _) ((hi (-r)).const_mul _),
    integral_const_mul, integral_const_mul] at hb
  simp only [sub_neg_eq_add] at hb
  nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ 8 * η by positivity),
    mul_le_mul_of_nonneg_left hn (show 0 ≤ 8 * η by positivity)]

/-- A scale-adapted Poisson weight controls near and far spectral mass together. -/
theorem integral_windowError_le_scaled_weight {η Y : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1) (hY : 1 ≤ Y) (r : ℝ) :
    (∫ y in Ioc Y (2 * Y), windowError η y r) ≤
      (544 * η * Y * Real.log (1 + 6 * Y / η)) * (Y / (Y ^ 2 + r ^ 2)) := by
  have hY0 : 0 < Y := by linarith
  have hden : 0 < Y ^ 2 + r ^ 2 := by positivity
  have hlog : 1 ≤ Real.log (1 + 6 * Y / η) := by
    apply (Real.le_log_iff_exp_le (by positivity)).mpr
    have hq : 6 ≤ 6 * Y / η := (le_div_iff₀ hη).mpr (by linarith)
    have := Real.exp_one_lt_d9
    linarith
  by_cases hr : |r| ≤ 4 * Y
  · have hs : Y ^ 2 + r ^ 2 ≤ 17 * Y ^ 2 := by
      have := (sq_le_sq₀ (abs_nonneg r) (by positivity : 0 ≤ 4 * Y)).mpr hr
      norm_num [sq_abs, mul_pow] at this
      nlinarith
    refine (integral_windowError_le_log hη hY hr).trans ?_
    rw [← mul_div_assoc, le_div_iff₀ hden]
    nlinarith [mul_le_mul_of_nonneg_left hs
      (show 0 ≤ 32 * η * Real.log (1 + 6 * Y / η) by positivity)]
  · have hr' : 4 * Y < |r| := lt_of_not_ge hr
    have hi : IntegrableOn (fun _ : ℝ => 32 * η * Y * (1 + r ^ 2)⁻¹)
        (Ioc Y (2 * Y)) := integrableOn_const measure_Ioc_lt_top.ne
    have hb := setIntegral_mono_on (integrableOn_windowError hη hY r) hi
      measurableSet_Ioc (fun y hy => windowError_le_far hη hY hy hr')
    rw [setIntegral_const, Real.volume_real_Ioc, smul_eq_mul,
      show 2 * Y - Y = Y by ring, max_eq_left hY0.le] at hb
    have hs : Y ^ 2 + r ^ 2 ≤ 2 * (1 + r ^ 2) := by
      have := (sq_le_sq₀ (by positivity : 0 ≤ 4 * Y) (abs_nonneg r)).mpr hr'.le
      norm_num [sq_abs, mul_pow] at this
      nlinarith
    have hweight : (1 + r ^ 2)⁻¹ ≤ 2 / (Y ^ 2 + r ^ 2) := by
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity : 0 < 1 + r ^ 2) hden]
      linarith
    calc
      (∫ y in Ioc Y (2 * Y), windowError η y r) ≤
          32 * η * Y ^ 2 * (1 + r ^ 2)⁻¹ := by nlinarith [hb]
      _ ≤ 32 * η * Y ^ 2 * (2 / (Y ^ 2 + r ^ 2)) := by gcongr
      _ ≤ (544 * η * Y * Real.log (1 + 6 * Y / η)) * (Y / (Y ^ 2 + r ^ 2)) := by
        rw [← mul_div_assoc, ← mul_div_assoc]
        apply div_le_div_of_nonneg_right _ hden.le
        nlinarith [mul_le_mul_of_nonneg_left hlog (show 0 ≤ η * Y ^ 2 by positivity)]

end RHTower.WeilWorkSettledPhase
