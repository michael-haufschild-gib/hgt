import GaloisForLFunctions.SquareRootThreshold.EffectiveHorizons.HausdorffModulus

/-!
# Positive bands around the Hausdorff saddle

The mass-bearing core has width `w=s/√p`. Phase cancellation makes the
larger band of half-width `min(s/8,w²/64)` nonnegative. The estimates retain
the exact real saddle value, allowing comparison with the complete tails.
-/

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold.HausdorffSaddle

/-- Relative complex displacement from a positive real saddle. -/
def relativePoint (s x y : ℝ) : ℂ := ((x - s) / s : ℝ) + ((y / s : ℝ) : ℂ) * Complex.I

@[simp] theorem relativePoint_re (s x y : ℝ) : (relativePoint s x y).re = (x - s) / s := by
  simp [relativePoint]

@[simp] theorem relativePoint_im (s x y : ℝ) : (relativePoint s x y).im = y / s := by
  simp [relativePoint]

theorem relativePoint_abs_sum {s : ℝ} (hs : 0 < s) (x y : ℝ) :
    |(relativePoint s x y).re| + |(relativePoint s x y).im| = (|x - s| + |y|) / s := by
  rw [relativePoint_re, relativePoint_im, abs_div, abs_div, abs_of_pos hs]
  ring

theorem relativePoint_norm_sq {s : ℝ} (hs : s ≠ 0) (x y : ℝ) :
    ‖relativePoint s x y‖ ^ 2 = ((x - s) ^ 2 + y ^ 2) / s ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, relativePoint_re, relativePoint_im]
  field_simp [hs]

theorem mul_one_add_relativePoint {s : ℝ} (hs : s ≠ 0) (x y : ℝ) :
    (s : ℂ) * (1 + relativePoint s x y) = (x : ℂ) + (y : ℂ) * Complex.I := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  unfold relativePoint
  push_cast
  field_simp [hsC]
  ring

/-- The normalized exponential represents the atom at its actual complex coordinate. -/
theorem kernel_at_relativePoint {R s : ℝ} {p r : ℕ} (hs : s ≠ 0) (hr : 0 < r)
    (hpr : 8 * (p : ℝ) ≤ r) (hbalance : (p : ℝ) * (R * s ^ 2 - 1) = r)
    {x y : ℝ} (hu : ‖relativePoint s x y‖ ≤ 1 / 4) :
    kernel R p r ((x : ℂ) + (y : ℂ) * Complex.I) =
      (realKernel R p r s : ℂ) * Complex.exp (saddleLog p r (relativePoint s x y)) := by
  rw [← mul_one_add_relativePoint hs x y, kernel_eq_saddle_mul_exp hs hr hpr hbalance hu,
    kernel_ofReal]

/-- The core retains at least half the real saddle value. -/
theorem half_saddle_le_re_kernel {R s w x y : ℝ} {p r : ℕ} (hs : 0 < s)
    (hp : 0 < p) (hr : 0 < r) (hpr : 8 * (p : ℝ) ≤ r)
    (hbalance : (p : ℝ) * (R * s ^ 2 - 1) = r)
    (hwidth : (p : ℝ) * w ^ 2 = s ^ 2) (hw : 32 ≤ w) (hws : w ≤ s)
    (hx : |x - s| ≤ w / 10) (hy : |y| ≤ 1 / 2) :
    (1 / 2) * realKernel R p r s ≤ (kernel R p r ((x : ℂ) + (y : ℂ) * Complex.I)).re := by
  have hsum : |(relativePoint s x y).re| + |(relativePoint s x y).im| ≤ 1 / 4 := by
    rw [relativePoint_abs_sum hs, div_le_iff₀ hs]
    linarith only [hx, hy, hw, hws]
  have hu := (Complex.norm_le_abs_re_add_abs_im (relativePoint s x y)).trans hsum
  have hx2 : (x - s) ^ 2 ≤ w ^ 2 / 100 := by
    have h := pow_le_pow_left₀ (abs_nonneg (x - s)) hx 2
    rw [sq_abs] at h
    nlinarith only [h]
  have hy2 : y ^ 2 ≤ 1 / 4 := by
    have h := pow_le_pow_left₀ (abs_nonneg y) hy 2
    rw [sq_abs] at h
    nlinarith only [h]
  have hw2 : 100 ≤ w ^ 2 := by nlinarith only [hw]
  have hsmall : 11 * (p : ℝ) * ‖relativePoint s x y‖ ^ 2 ≤ 1 / 4 := by
    rw [relativePoint_norm_sq hs.ne']
    rw [show 11 * (p : ℝ) * (((x - s) ^ 2 + y ^ 2) / s ^ 2) =
      (11 * (p : ℝ) * ((x - s) ^ 2 + y ^ 2)) / s ^ 2 by ring,
      div_le_iff₀ (sq_pos_of_pos hs)]
    have h₁ := mul_le_mul_of_nonneg_left (add_le_add hx2 hy2)
      (show 0 ≤ 11 * (p : ℝ) by positivity)
    have hbase : 11 * (w ^ 2 / 100 + 1 / 4) ≤ w ^ 2 / 4 := by linarith only [hw2]
    have h₂ := mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg p)
    nlinarith only [h₁, h₂, hwidth]
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hE := re_exp_saddleLog_ge_half (Nat.cast_nonneg p) hrR hpr hu hsmall
  have hM := realKernel_saddle_pos hs hp hr hbalance
  rw [kernel_at_relativePoint hs.ne' hr hpr hbalance hu, Complex.re_ofReal_mul]
  have h := mul_le_mul_of_nonneg_left hE hM.le
  nlinarith only [h]

/-- Phase cancellation keeps the wider saddle band nonnegative. -/
theorem re_kernel_nonneg_of_saddle_band {R s w x y : ℝ} {p r : ℕ} (hs : 0 < s)
    (hp : 0 < p) (hr : 0 < r) (hpr : 8 * (p : ℝ) ≤ r)
    (hbalance : (p : ℝ) * (R * s ^ 2 - 1) = r)
    (hwidth : (p : ℝ) * w ^ 2 = s ^ 2) (hs4 : 4 ≤ s) (hw : 4 ≤ w)
    (hxS : |x - s| ≤ s / 8) (hxW : |x - s| ≤ w ^ 2 / 64) (hy : |y| ≤ 1 / 2) :
    0 ≤ (kernel R p r ((x : ℂ) + (y : ℂ) * Complex.I)).re := by
  have hsum : |(relativePoint s x y).re| + |(relativePoint s x y).im| ≤ 1 / 4 := by
    rw [relativePoint_abs_sum hs, div_le_iff₀ hs]
    linarith only [hxS, hy, hs4]
  have hu := (Complex.norm_le_abs_re_add_abs_im (relativePoint s x y)).trans hsum
  have hy2 : |y| ^ 2 ≤ 1 / 4 := by nlinarith only [hy, abs_nonneg y]
  have hw2 : 16 ≤ w ^ 2 := by nlinarith only [hw]
  have hphase : 16 * (p : ℝ) *
      (|(relativePoint s x y).re| + |(relativePoint s x y).im|) *
        |(relativePoint s x y).im| ≤ 1 / 2 := by
    rw [relativePoint_abs_sum hs, relativePoint_im, abs_div, abs_of_pos hs]
    rw [show 16 * (p : ℝ) * ((|x - s| + |y|) / s) * (|y| / s) =
      (16 * (p : ℝ) * (|x - s| + |y|) * |y|) / s ^ 2 by ring,
      div_le_iff₀ (sq_pos_of_pos hs)]
    have hab := mul_le_mul_of_nonneg_left hy (abs_nonneg (x - s))
    have h₁ := mul_le_mul_of_nonneg_left
      (show (|x - s| + |y|) * |y| ≤ |x - s| / 2 + 1 / 4 by nlinarith only [hab, hy2])
      (show 0 ≤ 16 * (p : ℝ) by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hxW (show 0 ≤ 8 * (p : ℝ) by positivity)
    have h₃ := mul_le_mul_of_nonneg_left hw2 (Nat.cast_nonneg p)
    nlinarith only [h₁, h₂, h₃, hwidth]
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hE := re_exp_saddleLog_nonneg (Nat.cast_nonneg p) hrR hpr hsum hphase
  have hM := realKernel_saddle_pos hs hp hr hbalance
  rw [kernel_at_relativePoint hs.ne' hr hpr hbalance hu, Complex.re_ofReal_mul]
  exact mul_nonneg hM.le hE

end GaloisForLFunctions.SquareRootThreshold.HausdorffSaddle
