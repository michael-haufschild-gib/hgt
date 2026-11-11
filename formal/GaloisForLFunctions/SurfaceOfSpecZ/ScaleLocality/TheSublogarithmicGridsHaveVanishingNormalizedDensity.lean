import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.TheGrowingImaginaryGridsMeetTheCalibrationBounds
import GaloisForLFunctions.RHTower.HighBlockAsymptotics

/-!
# Sublogarithmic windows and sparse calibrated grids

The scale `Γ=T^(1/4)` leaves enough room for calibration. A window
`R=o(log T)` needs `o(Γ log Γ)` nodes, and its normalized quadratic
mass tends to zero, allowing a tempered sparse sequence of blocks.
-/

open Complex Filter Set Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Frequency scale used for the growing interpolation blocks. -/
def calibratedGridFrequency (T : ℝ) : ℝ := T ^ (1 / 4 : ℝ)

private theorem gridFrequency_pos {T : ℝ} (hT : 0 < T) : 0 < calibratedGridFrequency T :=
  Real.rpow_pos_of_pos hT _

private theorem gridFrequency_fourth {T : ℝ} (hT : 0 < T) :
    calibratedGridFrequency T ^ 4 = T := by
  unfold calibratedGridFrequency
  rw [← Real.rpow_natCast, ← Real.rpow_mul hT.le]
  norm_num

private theorem log_gridFrequency {T : ℝ} (hT : 0 < T) :
    Real.log (calibratedGridFrequency T) = Real.log T / 4 := by
  rw [calibratedGridFrequency, Real.log_rpow hT]
  ring

/-- Sublogarithmic radii meet all scalar calibration bounds eventually. -/
theorem eventually_sublogarithmic_grid_parameters {R : ℝ → ℝ}
    (hR : Tendsto (fun T => R T / Real.log T) atTop (𝓝 0))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop,
      0 < T ∧ 1 ≤ Real.log T ∧ Real.log 6 ≤ Real.log T ∧
      20000 * Real.log T ≤ calibratedGridFrequency T ∧
      Real.log (calibratedGridFrequency T) = Real.log T / 4 ∧
      calibratedGridFrequency T ^ 4 = T ∧ R T ≤ Real.log T ∧
      1 / (8 * calibratedGridFrequency T) ≤ η := by
  have hpower := RHTower.eventually_const_mul_rpow_neg_mul_log_pow_le
    20000 (1 / 4) (by norm_num) 1 (by norm_num : (0 : ℝ) < 1)
  have hdepth := RHTower.eventually_const_mul_rpow_neg_le
    (1 / 8) (1 / 4) (by norm_num) hη
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.log 6),
    hpower, hdepth, hR.eventually_le_const (by norm_num : (0 : ℝ) < 1)]
    with T hT hL hL6 hp hd hratio
  have hΓ := gridFrequency_pos hT
  have hL0 : 0 < Real.log T := zero_lt_one.trans_le hL
  have he : T ^ (-(1 / 4 : ℝ)) = (calibratedGridFrequency T)⁻¹ :=
    Real.rpow_neg hT.le _
  have hp' : 20000 * Real.log T / calibratedGridFrequency T ≤ 1 := by
    simpa only [he, pow_one, div_eq_mul_inv, mul_left_comm, mul_comm, mul_assoc] using hp
  have hd' : 1 / (8 * calibratedGridFrequency T) ≤ η := by
    simpa only [he, one_div, mul_inv_rev, mul_comm] using hd
  exact ⟨hT, hL, hL6, (div_le_one hΓ).mp hp', log_gridFrequency hT,
    gridFrequency_fourth hT, (div_le_one hL0).mp hratio, hd'⟩

/-- Every sufficiently late sublogarithmic window has a calibrated positive block. -/
theorem eventually_exists_sublogarithmic_calibrated_grid {R : ℝ → ℝ}
    (hR0 : ∀ T, 0 ≤ R T)
    (hR : Tendsto (fun T => R T / Real.log T) atTop (𝓝 0))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop,
      let Γ := calibratedGridFrequency T
      let k := calibratedGridDegree Γ (R T)
      ∃ z : Fin (k + 1) → ℂ,
        Function.Injective z ∧
        (∀ i, |(z i).re| ≤ η ∧ Γ / 2 ≤ (z i).im ∧ (z i).im ≤ 4 * Γ ∧ ‖z i‖ ≤ 4 * Γ) ∧
        (∀ i j, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * (Γ / k) ≤ |(z i).im - (z j).im|) ∧
        ∀ v : ℝ, |v| ≤ R T + 8 →
          (3 / 4 : ℝ) ≤ (∑ i, Complex.exp (((T + v : ℝ) : ℂ) * z i)).re := by
  filter_upwards [eventually_sublogarithmic_grid_parameters hR hη] with T hT
  exact exists_positive_growing_calibrated_grid hT.2.1 hT.2.2.1 hT.2.2.2.1
    hT.2.2.2.2.1 hT.2.2.2.2.2.1 (hR0 T) hT.2.2.2.2.2.2.1 hT.2.2.2.2.2.2.2

/-- The quadratic normalized grid mass vanishes, permitting a summable choice of blocks. -/
theorem tendsto_sublogarithmic_grid_quadratic_mass {R : ℝ → ℝ}
    (hR0 : ∀ T, 0 ≤ R T)
    (hR : Tendsto (fun T => R T / Real.log T) atTop (𝓝 0)) :
    Tendsto (fun T => (calibratedGridDegree (calibratedGridFrequency T) (R T) : ℝ) /
      calibratedGridFrequency T ^ 2) atTop (𝓝 0) := by
  have hmajor := RHTower.tendsto_const_mul_rpow_neg_mul_log_pow
    18433 (1 / 4) (by norm_num) 1
  apply squeeze_zero_norm' _ hmajor
  filter_upwards [eventually_sublogarithmic_grid_parameters hR (by norm_num : (0 : ℝ) < 1)]
    with T hT
  have hΓ := gridFrequency_pos hT.1
  have hbound := growing_calibrated_grid_bounds hT.2.1 hT.2.2.1 hT.2.2.2.1
    hT.2.2.2.2.1 hT.2.2.2.2.2.1 (hR0 T) hT.2.2.2.2.2.2.1 hT.2.2.2.2.2.2.2
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (18433 * calibratedGridFrequency T * Real.log T) / calibratedGridFrequency T ^ 2 :=
      div_le_div_of_nonneg_right hbound.2.2.2.1 (by positivity)
    _ = 18433 * (T ^ (-(1 / 4 : ℝ)) * Real.log T ^ 1) := by
      rw [Real.rpow_neg hT.1.le]
      change 18433 * calibratedGridFrequency T * Real.log T / calibratedGridFrequency T ^ 2 =
        18433 * ((calibratedGridFrequency T)⁻¹ * Real.log T ^ 1)
      field_simp [hΓ.ne'] <;> ring

/-- The grid uses a vanishing fraction of the allowed logarithmic local density. -/
theorem tendsto_sublogarithmic_grid_logarithmic_density {R : ℝ → ℝ}
    (hR0 : ∀ T, 0 ≤ R T)
    (hR : Tendsto (fun T => R T / Real.log T) atTop (𝓝 0)) :
    Tendsto (fun T => (calibratedGridDegree (calibratedGridFrequency T) (R T) : ℝ) /
      (calibratedGridFrequency T * Real.log (calibratedGridFrequency T))) atTop (𝓝 0) := by
  have hinv : Tendsto (fun T : ℝ => (Real.log T)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hmajor : Tendsto (fun T => 8192 * (R T / Real.log T) +
      65540 * (Real.log T)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hR.const_mul 8192).add (hinv.const_mul 65540)
  apply squeeze_zero_norm' _ hmajor
  filter_upwards [eventually_sublogarithmic_grid_parameters hR (by norm_num : (0 : ℝ) < 1)]
    with T hT
  let Γ := calibratedGridFrequency T
  have hΓ : 0 < Γ := gridFrequency_pos hT.1
  have hΓ1 : 1 ≤ Γ := by linarith only [hT.2.1, hT.2.2.2.1]
  have hL : 0 < Real.log T := zero_lt_one.trans_le hT.2.1
  have hlog : Real.log Γ = Real.log T / 4 := hT.2.2.2.2.1
  have hlog0 : 0 < Real.log Γ := by rw [hlog]; positivity
  have hc : (calibratedGridDegree Γ (R T) : ℝ) < 2048 * Γ * (R T + 8) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hb : (calibratedGridDegree Γ (R T) : ℝ) ≤ Γ * (2048 * R T + 16385) := by
    nlinarith only [hc, hΓ1]
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (Γ * (2048 * R T + 16385)) / (Γ * Real.log Γ) :=
      div_le_div_of_nonneg_right hb (by positivity)
    _ = 8192 * (R T / Real.log T) + 65540 * (Real.log T)⁻¹ := by
      rw [hlog]
      field_simp [hΓ.ne', hL.ne'] <;> ring

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
