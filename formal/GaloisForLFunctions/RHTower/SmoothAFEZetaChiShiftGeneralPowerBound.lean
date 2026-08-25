import GaloisForLFunctions.RHTower.SmoothAFEZetaChiPowerBound
import GaloisForLFunctions.RHTower.SmoothAFEZetaGeneralDualExpansion

/-!
# Conductor decay of shifted chi ratios off the critical line

Reflection controls the denominator at `Re s = 1/2-d`, while the existing
right-line bound controls the numerator after a contour shift by `d+η`.
The exact shifted ratio then gains the full conductor power `d+η`.
-/

noncomputable section

namespace RHTower

open Complex

/-- The displaced vertical point `1/2-d+iτ`. -/
def displacedLinePt (d τ : ℝ) : ℂ :=
  ((1 / 2 - d : ℝ) : ℂ) + (τ : ℂ) * I

theorem displacedLinePt_re (d τ : ℝ) :
    (displacedLinePt d τ).re = 1 / 2 - d := by
  simp [displacedLinePt]

theorem displacedLinePt_mem_openStrip
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) (τ : ℝ) :
    0 < (displacedLinePt d τ).re ∧ (displacedLinePt d τ).re < 1 := by
  rw [displacedLinePt_re]
  constructor <;> linarith

/-- Reflection turns the inverse chi factor on the displaced left line into
the chi factor on the matching right line. -/
theorem inv_zetaChi_displacedLinePt
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) (τ : ℝ) :
    (zetaChi (displacedLinePt d τ))⁻¹ =
      zetaChi (((1 / 2 + d : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I) := by
  obtain ⟨h0, h1⟩ := displacedLinePt_mem_openStrip hd hdhalf τ
  have hprod := zetaChi_mul_one_sub_of_mem_strip h0 h1
  have hsne := zetaChi_ne_zero_of_mem_openStrip h0 h1
  have href : 1 - displacedLinePt d τ =
      (((1 / 2 + d : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I) := by
    unfold displacedLinePt
    push_cast
    ring
  rw [href] at hprod
  calc
    (zetaChi (displacedLinePt d τ))⁻¹ =
        (zetaChi (displacedLinePt d τ))⁻¹ *
          (zetaChi (displacedLinePt d τ) *
            zetaChi (((1 / 2 + d : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I)) := by
      rw [hprod]
      simp
    _ = zetaChi (((1 / 2 + d : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I) := by
      rw [inv_mul_cancel_left₀ hsne]

/-- Uniform conductor decay for the exact shifted chi ratio based at
`1/2-d+iτ` and shifted right by `d+η-iv`. -/
theorem exists_norm_smoothAFEZetaChiShiftRatio_displaced_le
    {d η : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hη : 0 < η) (hηhalf : η < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (τ v : ℝ),
      ‖smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
          (-(((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤
        K * (1 + |v|) ^ η / (max 1 |τ|) ^ (d + η) := by
  obtain ⟨Kη, hKη0, hKη⟩ :=
    exists_norm_zetaChi_fixed_right_line_le_rpow hη hηhalf
  obtain ⟨Kd, hKd0, hKd⟩ :=
    exists_norm_zetaChi_fixed_right_line_le_rpow hd hdhalf
  refine ⟨Kη * Kd, mul_nonneg hKη0 hKd0, fun τ v => ?_⟩
  have harg :
      displacedLinePt d τ +
          -(((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I) =
        (((1 / 2 + η : ℝ) : ℂ) + ((τ - v : ℝ) : ℂ) * I) := by
    unfold displacedLinePt
    push_cast
    ring
  have hnum :
      ‖zetaChi (displacedLinePt d τ +
          -(((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤
        Kη / (max 1 |τ - v|) ^ η := by
    rw [harg]
    exact hKη (τ - v)
  have hgeom := one_div_max_one_abs_shift_rpow_le hη.le τ v
  have hnum' :
      ‖zetaChi (displacedLinePt d τ +
          -(((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤
        Kη * (1 + |v|) ^ η / (max 1 |τ|) ^ η := by
    calc
      ‖zetaChi (displacedLinePt d τ +
          -(((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I))‖
          ≤ Kη / (max 1 |τ - v|) ^ η := hnum
      _ ≤ Kη * ((1 + |v|) ^ η / (max 1 |τ|) ^ η) := by
        simpa [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_left hgeom hKη0
      _ = Kη * (1 + |v|) ^ η / (max 1 |τ|) ^ η := by ring
  have href :
      ‖zetaChi (((1 / 2 + d : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I)‖ ≤
        Kd / (max 1 |τ|) ^ d := by
    simpa only [abs_neg] using hKd (-τ)
  unfold smoothAFEZetaChiShiftRatio
  rw [div_eq_mul_inv, inv_zetaChi_displacedLinePt hd hdhalf τ,
    norm_mul]
  have hleft0 : 0 ≤
      ‖zetaChi (displacedLinePt d τ +
        -(((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I))‖ := norm_nonneg _
  have hright0 : 0 ≤
      ‖zetaChi (((1 / 2 + d : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I)‖ := norm_nonneg _
  calc
    ‖zetaChi (displacedLinePt d τ +
          -(((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I))‖ *
        ‖zetaChi (((1 / 2 + d : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I)‖
      ≤ (Kη * (1 + |v|) ^ η / (max 1 |τ|) ^ η) *
          (Kd / (max 1 |τ|) ^ d) := by
        exact mul_le_mul hnum' href hright0
          (by positivity)
    _ = (Kη * Kd) * (1 + |v|) ^ η /
          (max 1 |τ|) ^ (d + η) := by
      have hm : 0 < max 1 |τ| :=
        lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      rw [Real.rpow_add hm]
      have hmd : (max 1 |τ|) ^ d ≠ 0 :=
        (Real.rpow_pos_of_pos hm d).ne'
      have hmη : (max 1 |τ|) ^ η ≠ 0 :=
        (Real.rpow_pos_of_pos hm η).ne'
      field_simp [hmd, hmη]

end RHTower
