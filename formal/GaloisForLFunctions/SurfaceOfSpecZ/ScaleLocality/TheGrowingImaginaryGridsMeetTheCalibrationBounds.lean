import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.TheCalibratedNodesStayOnASeparatedImaginaryGrid

/-!
# Calibration bounds for growing grids

At height `T=Γ⁴`, a grid with `⌈2048 Γ (R+8)⌉` gaps can be calibrated
inside any depth tolerance larger than `1/(8Γ)`. The elementary bounds
below apply once `R≤L`, `log Γ=L/4`, and `20000 L≤Γ`.
-/

open Complex Finset

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- The number of gaps needed to control a window, including the spline support. -/
def calibratedGridDegree (Γ R : ℝ) : ℕ := ⌈2048 * Γ * (R + 8)⌉₊

/-- Explicit scalar conditions for a growing calibrated grid. -/
theorem growing_calibrated_grid_bounds {Γ L R η T : ℝ}
    (hL : 1 ≤ L) (hlog6 : Real.log 6 ≤ L) (hΓL : 20000 * L ≤ Γ)
    (hlogΓ : Real.log Γ = L / 4) (hT : Γ ^ 4 = T)
    (hR0 : 0 ≤ R) (hRL : R ≤ L) (hη : 1 / (8 * Γ) ≤ η) :
    let k := calibratedGridDegree Γ R
    let r := min ((Γ / k) / 8) η
    0 < k ∧ 0 < r ∧ 8 * r ≤ Γ / k ∧
      (k : ℝ) ≤ 18433 * Γ * L ∧ (k : ℝ) ≤ Γ ^ 2 ∧
      12 * ((k + 1 : ℕ) : ℝ) ≤ (Γ / k) * T ∧
      2 * (2 * ((k + 1 : ℕ) : ℝ) *
        (|Real.log (Γ / k)| + |Real.log (6 * Γ)|) + 2 * Real.pi) ≤ r * T ∧
      2048 * Γ * (R + 8) ≤ k := by
  dsimp only
  let k := calibratedGridDegree Γ R
  let s : ℝ := Γ / k
  let r : ℝ := min (s / 8) η
  have hΓ : 0 < Γ := by linarith only [hL, hΓL]
  have hΓ1 : 1 ≤ Γ := by linarith only [hL, hΓL]
  have hL0 : 0 ≤ L := by linarith only [hL]
  have ha0 : 0 ≤ 2048 * Γ * (R + 8) := by positivity
  have hceil : 2048 * Γ * (R + 8) ≤ (k : ℝ) := Nat.le_ceil _
  have hceil' : (k : ℝ) < 2048 * Γ * (R + 8) + 1 := Nat.ceil_lt_add_one ha0
  have hΓk : Γ ≤ (k : ℝ) := by nlinarith only [hceil, mul_nonneg hΓ.le hR0, hΓ]
  have hk0 : (0 : ℝ) < k := hΓ.trans_le hΓk
  have hk : 0 < k := by exact_mod_cast hk0
  have hΓL1 : 1 ≤ Γ * L := by nlinarith only [hΓ1, hL, mul_nonneg (sub_nonneg.mpr hΓ1) (sub_nonneg.mpr hL)]
  have hkL : (k : ℝ) ≤ 18433 * Γ * L := by
    have hmul := mul_le_mul_of_nonneg_left hRL (show 0 ≤ 2048 * Γ by positivity)
    have hmul' := mul_le_mul_of_nonneg_left hL (show 0 ≤ 16384 * Γ by positivity)
    nlinarith only [hceil', hmul, hmul', hΓL1]
  have hkΓ : (k : ℝ) ≤ Γ ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hΓL hΓ.le
    nlinarith only [hkL, hh, mul_nonneg hΓ.le hL0]
  have hs0 : 0 < s := div_pos hΓ hk0
  have hs1 : s ≤ 1 := (div_le_one hk0).mpr hΓk
  have hsinv : 1 / Γ ≤ s := by
    dsimp only [s]
    apply (div_le_div_iff₀ hΓ hk0).mpr
    nlinarith only [hkΓ]
  have hrlo : 1 / (8 * Γ) ≤ r := by
    apply le_min
    · have hh := div_le_div_of_nonneg_right hsinv (by norm_num : (0 : ℝ) ≤ 8)
      simpa only [div_div, mul_comm Γ] using hh
    · exact hη
  have hr : 0 < r := (by positivity : 0 < 1 / (8 * Γ)).trans_le hrlo
  have hrsmall : 8 * r ≤ s := by
    have hh : r ≤ s / 8 := min_le_left _ _
    linarith only [hh]
  have hM : ((k + 1 : ℕ) : ℝ) ≤ 2 * Γ ^ 2 := by
    push_cast
    nlinarith only [hkΓ, hΓ1]
  have hΓsq0 : 0 ≤ Γ ^ 2 := sq_nonneg _
  have hΓcube : 0 ≤ Γ ^ 3 := by positivity
  have hsT : Γ ^ 3 ≤ s * T := by
    have hh := mul_le_mul_of_nonneg_right hsinv (show 0 ≤ Γ ^ 4 by positivity)
    rw [hT] at hh
    have he : (1 / Γ) * T = Γ ^ 3 := by rw [← hT]; field_simp [hΓ.ne'] <;> ring
    rwa [he] at hh
  have hrT : Γ ^ 3 / 8 ≤ r * T := by
    have hh := mul_le_mul_of_nonneg_right hrlo (show 0 ≤ Γ ^ 4 by positivity)
    rw [hT] at hh
    have he : (1 / (8 * Γ)) * T = Γ ^ 3 / 8 := by
      rw [← hT]
      field_simp [hΓ.ne'] <;> ring
    rwa [he] at hh
  have hcontract : 12 * ((k + 1 : ℕ) : ℝ) ≤ s * T := by
    have hΓ24 : 24 ≤ Γ := by linarith only [hL, hΓL]
    have hh := mul_le_mul_of_nonneg_right hΓ24 hΓsq0
    nlinarith only [hM, hh, hsT]
  have hlogs0 : Real.log s ≤ 0 := Real.log_nonpos hs0.le hs1
  have hlogs1 : -Real.log Γ ≤ Real.log s := by
    have hh := Real.log_le_log (by positivity : 0 < 1 / Γ) hsinv
    simpa only [one_div, Real.log_inv] using hh
  have habss : |Real.log s| ≤ L / 4 := by
    rw [abs_of_nonpos hlogs0]
    rw [hlogΓ] at hlogs1
    linarith only [hlogs1]
  have hlog6Γ : Real.log (6 * Γ) = Real.log 6 + L / 4 := by
    rw [Real.log_mul (by norm_num) hΓ.ne', hlogΓ]
  have hlog6Γ0 : 0 ≤ Real.log (6 * Γ) := Real.log_nonneg (by linarith only [hΓ1])
  have hH : |Real.log s| + |Real.log (6 * Γ)| ≤ 2 * L := by
    rw [abs_of_nonneg hlog6Γ0, hlog6Γ]
    linarith only [habss, hlog6]
  have hMH := mul_le_mul hM hH (by positivity : 0 ≤ |Real.log s| + |Real.log (6 * Γ)|)
    (by positivity : 0 ≤ 2 * Γ ^ 2)
  have hΓsqL : 1 ≤ Γ ^ 2 * L := by
    have hh := mul_le_mul_of_nonneg_right hΓL1 hΓ.le
    nlinarith only [hh, hΓ1]
  have hΓ256 : 256 * L ≤ Γ := by linarith only [hΓL, hL]
  have h256 := mul_le_mul_of_nonneg_right hΓ256 hΓsq0
  have hsize : 2 * (2 * ((k + 1 : ℕ) : ℝ) *
      (|Real.log s| + |Real.log (6 * Γ)|) + 2 * Real.pi) ≤ r * T := by
    nlinarith only [hMH, Real.pi_lt_four, hΓsqL, h256, hrT]
  exact ⟨hk, hr, hrsmall, hkL, hkΓ, hcontract, hsize, hceil⟩

/-- A polynomial frequency scale supports a calibrated positive block throughout a prescribed window. -/
theorem exists_positive_growing_calibrated_grid {Γ L R η T : ℝ}
    (hL : 1 ≤ L) (hlog6 : Real.log 6 ≤ L) (hΓL : 20000 * L ≤ Γ)
    (hlogΓ : Real.log Γ = L / 4) (hT : Γ ^ 4 = T)
    (hR0 : 0 ≤ R) (hRL : R ≤ L) (hη : 1 / (8 * Γ) ≤ η) :
    let k := calibratedGridDegree Γ R
    ∃ z : Fin (k + 1) → ℂ,
      Function.Injective z ∧
      (∀ i, |(z i).re| ≤ η ∧ Γ / 2 ≤ (z i).im ∧ (z i).im ≤ 4 * Γ ∧ ‖z i‖ ≤ 4 * Γ) ∧
      (∀ i j, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * (Γ / k) ≤ ‖z i - z j‖) ∧
      ∀ v : ℝ, |v| ≤ R + 8 →
        (3 / 4 : ℝ) ≤ (∑ i, Complex.exp (((T + v : ℝ) : ℂ) * z i)).re := by
  dsimp only
  obtain ⟨hk, hr, hsmall, _, _, hcontract, hsize, hwindow⟩ :=
    growing_calibrated_grid_bounds hL hlog6 hΓL hlogΓ hT hR0 hRL hη
  have hΓ : 0 < Γ := by linarith only [hL, hΓL]
  have hT0 : 0 < T := by rw [← hT]; positivity
  obtain ⟨z, _, hzi, hgeom, hsep, hpos⟩ := exists_positive_calibrated_grid hΓ hk hr hT0
    (by linarith only [hR0] : 0 ≤ R + 8) hsmall hcontract hsize hwindow
  refine ⟨z, hzi, ?_, hsep, hpos⟩
  intro i
  exact ⟨(hgeom i).1.trans (min_le_right _ _), (hgeom i).2⟩

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
