import GaloisForLFunctions.RHTower.SmoothAFEZetaChiLeftPowerBound
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftGeneralPowerBound

/-!
# Conductor decay of shifted chi ratios on a displaced right line

For `s = 1/2+d+iτ`, shift the dual contour left to `Re w = -η`.
The numerator of `χ(s-w)/χ(s)` then lies on `Re = 1/2+d+η` and
contributes height power `-(d+η)`, while reflection of the denominator
contributes height power `d`.  Their quotient therefore gains exactly
`(max 1 |τ|)⁻η`.
-/

noncomputable section

namespace RHTower

open Complex

/-- The point `1/2+d+iτ` in the right half of the critical strip. -/
def rightDisplacedLinePt (d τ : ℝ) : ℂ :=
  ((1 / 2 + d : ℝ) : ℂ) + (τ : ℂ) * I

@[simp] theorem rightDisplacedLinePt_re (d τ : ℝ) :
    (rightDisplacedLinePt d τ).re = 1 / 2 + d := by
  simp [rightDisplacedLinePt]

@[simp] theorem rightDisplacedLinePt_im (d τ : ℝ) :
    (rightDisplacedLinePt d τ).im = τ := by
  simp [rightDisplacedLinePt]

theorem rightDisplacedLinePt_mem_openStrip
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) (τ : ℝ) :
    0 < (rightDisplacedLinePt d τ).re ∧
      (rightDisplacedLinePt d τ).re < 1 := by
  rw [rightDisplacedLinePt_re]
  constructor <;> linarith

theorem rightDisplacedLinePt_eq_one_sub_displacedLinePt_neg (d τ : ℝ) :
    rightDisplacedLinePt d τ = 1 - displacedLinePt d (-τ) := by
  unfold rightDisplacedLinePt displacedLinePt
  push_cast
  ring

theorem displacedLinePt_neg_eq_one_sub_rightDisplacedLinePt (d τ : ℝ) :
    displacedLinePt d (-τ) = 1 - rightDisplacedLinePt d τ := by
  rw [rightDisplacedLinePt_eq_one_sub_displacedLinePt_neg]
  ring

theorem rightDisplacedLinePt_sub_one_eq_neg_displacedLinePt_neg (d τ : ℝ) :
    rightDisplacedLinePt d τ - 1 = -displacedLinePt d (-τ) := by
  rw [rightDisplacedLinePt_eq_one_sub_displacedLinePt_neg]
  ring

theorem displacedLinePt_neg_sub_one_eq_neg_rightDisplacedLinePt (d τ : ℝ) :
    displacedLinePt d (-τ) - 1 = -rightDisplacedLinePt d τ := by
  rw [displacedLinePt_neg_eq_one_sub_rightDisplacedLinePt]
  ring

theorem zetaChi_right_mul_reflected_left
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) (τ : ℝ) :
    zetaChi (rightDisplacedLinePt d τ) *
        zetaChi (displacedLinePt d (-τ)) = 1 := by
  have hstrip := rightDisplacedLinePt_mem_openStrip hd hdhalf τ
  have h := zetaChi_mul_one_sub_of_mem_strip hstrip.1 hstrip.2
  rwa [← displacedLinePt_neg_eq_one_sub_rightDisplacedLinePt] at h

/-- Reflection turns the inverse chi factor on the displaced right line
into the chi factor on the matching left line. -/
theorem inv_zetaChi_rightDisplacedLinePt
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) (τ : ℝ) :
    (zetaChi (rightDisplacedLinePt d τ))⁻¹ =
      zetaChi (displacedLinePt d (-τ)) := by
  obtain ⟨h0, h1⟩ := rightDisplacedLinePt_mem_openStrip hd hdhalf τ
  have hne := zetaChi_ne_zero_of_mem_openStrip h0 h1
  have hprod := zetaChi_right_mul_reflected_left hd hdhalf τ
  calc
    (zetaChi (rightDisplacedLinePt d τ))⁻¹ =
        (zetaChi (rightDisplacedLinePt d τ))⁻¹ *
          (zetaChi (rightDisplacedLinePt d τ) *
            zetaChi (displacedLinePt d (-τ))) := by rw [hprod, mul_one]
    _ = zetaChi (displacedLinePt d (-τ)) := by
      rw [inv_mul_cancel_left₀ hne]

/-- Direct right-line conductor bound.  On the contour `Re w = -η`,
the shifted chi ratio gains the full height power `η`. -/
theorem exists_norm_smoothAFEZetaChiShiftRatio_rightDisplaced_le
    {d η : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hη : 0 < η) (hdηhalf : d + η < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (τ v : ℝ),
      ‖smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
          (-(((-η : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤
        K * (1 + |v|) ^ (d + η) / (max 1 |τ|) ^ η := by
  have hdη : 0 < d + η := by linarith
  obtain ⟨Kde, hKde0, hKde⟩ :=
    exists_norm_zetaChi_fixed_right_line_le_rpow hdη hdηhalf
  obtain ⟨Kd, hKd0, hKd⟩ :=
    exists_norm_zetaChi_fixed_left_line_le_rpow hd hdhalf
  refine ⟨Kde * Kd, mul_nonneg hKde0 hKd0, fun τ v => ?_⟩
  have harg :
      rightDisplacedLinePt d τ +
          -(((-η : ℝ) : ℂ) + (v : ℂ) * I) =
        (((1 / 2 + (d + η) : ℝ) : ℂ) +
          ((τ - v : ℝ) : ℂ) * I) := by
    unfold rightDisplacedLinePt
    push_cast
    ring
  have hnum :
      ‖zetaChi (rightDisplacedLinePt d τ +
          -(((-η : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤
        Kde / (max 1 |τ - v|) ^ (d + η) := by
    rw [harg]
    exact hKde (τ - v)
  have hgeom := one_div_max_one_abs_shift_rpow_le hdη.le τ v
  have hnum' :
      ‖zetaChi (rightDisplacedLinePt d τ +
          -(((-η : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤
        Kde * (1 + |v|) ^ (d + η) /
          (max 1 |τ|) ^ (d + η) := by
    calc
      ‖zetaChi (rightDisplacedLinePt d τ +
          -(((-η : ℝ) : ℂ) + (v : ℂ) * I))‖
          ≤ Kde / (max 1 |τ - v|) ^ (d + η) := hnum
      _ ≤ Kde * ((1 + |v|) ^ (d + η) /
          (max 1 |τ|) ^ (d + η)) := by
        simpa [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_left hgeom hKde0
      _ = Kde * (1 + |v|) ^ (d + η) /
          (max 1 |τ|) ^ (d + η) := by ring
  have href :
      ‖zetaChi (displacedLinePt d (-τ))‖ ≤
        Kd * (max 1 |τ|) ^ d := by
    simpa [displacedLinePt, abs_neg] using hKd (-τ)
  unfold smoothAFEZetaChiShiftRatio
  rw [div_eq_mul_inv, inv_zetaChi_rightDisplacedLinePt hd hdhalf τ,
    norm_mul]
  have hright0 : 0 ≤ ‖zetaChi (displacedLinePt d (-τ))‖ := norm_nonneg _
  calc
    ‖zetaChi (rightDisplacedLinePt d τ +
          -(((-η : ℝ) : ℂ) + (v : ℂ) * I))‖ *
        ‖zetaChi (displacedLinePt d (-τ))‖
      ≤ (Kde * (1 + |v|) ^ (d + η) /
          (max 1 |τ|) ^ (d + η)) *
          (Kd * (max 1 |τ|) ^ d) := by
        exact mul_le_mul hnum' href hright0 (by positivity)
    _ = (Kde * Kd) * (1 + |v|) ^ (d + η) /
          (max 1 |τ|) ^ η := by
      have hm : 0 < max 1 |τ| :=
        lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      rw [Real.rpow_add hm]
      have hmd : (max 1 |τ|) ^ d ≠ 0 :=
        (Real.rpow_pos_of_pos hm d).ne'
      have hmη : (max 1 |τ|) ^ η ≠ 0 :=
        (Real.rpow_pos_of_pos hm η).ne'
      field_simp [hmd, hmη]

end RHTower
