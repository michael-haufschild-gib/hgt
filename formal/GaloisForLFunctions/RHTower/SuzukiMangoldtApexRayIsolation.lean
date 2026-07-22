import GaloisForLFunctions.RHTower.SuzukiMangoldtApexLock

/-!
# Aligned Suzuki apices isolate every power ray

At width `log 2`, align the moving Suzuki apex with the Mangoldt node `2 log n` by
choosing aperture `log (2n) / 2`.  The resulting sample channel has the exact value

`sqrt m * max 0 (log 2 - |log (m / n)|)`

at the node `2 log m`.  Thus only indices in the open multiplicative annulus
`n / 2 < m < 2n` can be nonzero.  Distinct positive powers of any fixed base at least two
never lie in that annulus, so every power ray is diagonal for the aligned sample channel.

This rules out valuation-diagonal flank blocks at the remaining Suzuki--Mangoldt apex seam.
Any block transport that pays an apex deficit with nonzero flank samples must first mix
different power rays.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

/-- Exact sample law at the width-`log 2` aperture aligned with the node `2 log n`. -/
theorem suzukiMangoldtAlignedApex_sample_eq
    {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) :
    suzukiRectangularPositiveArchSampleChannel (Real.log 2)
        (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode m) =
      Real.sqrt m *
        max 0 (Real.log 2 - |Real.log ((m : ℝ) / (n : ℝ))|) := by
  have hnR : (0 : ℝ) < n := by positivity
  have hmR : (0 : ℝ) < m := by positivity
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hlogm : Real.log 2 ≤ Real.log (m : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hm)
  have hlogMulN : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log n :=
    Real.log_mul (by norm_num) hnR.ne'
  have ha : Real.log 2 ≤ suzukiMangoldtApexAperture n := by
    rw [suzukiMangoldtApexAperture, hlogMulN]
    linarith
  have ht : 0 ≤ mangoldtLogHaarNode m := by
    rw [mangoldtLogHaarNode]
    positivity
  rw [suzukiRectangularPositiveArchSampleChannel_eq_fixed_add_moving
    hlogTwo.le ha ht]
  have hfixed : suzukiRectangularFixedArchChannel (Real.log 2)
      (mangoldtLogHaarNode m) = 0 := by
    rw [suzukiRectangularFixedArchChannel, mangoldtLogHaarNode]
    have hheight : Real.log 2 - (2 * Real.log (m : ℝ)) / 2 ≤ 0 := by
      linarith
    rw [max_eq_left hheight]
    ring
  rw [hfixed, zero_add, suzukiRectangularMovingArchChannel,
    mangoldtLogHaarNode, suzukiMangoldtApexAperture, hlogMulN]
  have hcenter : 2 * ((Real.log 2 + Real.log (n : ℝ)) / 2) - Real.log 2 =
      Real.log (n : ℝ) := by ring
  rw [hcenter]
  have hexp : Real.exp (Real.log (m : ℝ) / 2) = Real.sqrt (m : ℝ) := by
    rw [← Real.log_sqrt hmR.le, Real.exp_log (Real.sqrt_pos.mpr hmR)]
  rw [show 2 * Real.log (m : ℝ) / 4 = Real.log (m : ℝ) / 2 by ring,
    show 2 * Real.log (m : ℝ) / 2 - Real.log (n : ℝ) =
      Real.log ((m : ℝ) / (n : ℝ)) by
        rw [Real.log_div hmR.ne' hnR.ne']
        ring,
    hexp]

/-- The aligned channel vanishes outside the open multiplicative annulus around its apex. -/
theorem suzukiMangoldtAlignedApex_sample_eq_zero_of_outside
    {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hfar : 2 * m ≤ n ∨ 2 * n ≤ m) :
    suzukiRectangularPositiveArchSampleChannel (Real.log 2)
        (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode m) = 0 := by
  rw [suzukiMangoldtAlignedApex_sample_eq hn hm]
  have hnR : (0 : ℝ) < n := by positivity
  have hmR : (0 : ℝ) < m := by positivity
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have habs : Real.log 2 ≤ |Real.log ((m : ℝ) / (n : ℝ))| := by
    rcases hfar with hlow | hhigh
    · have hlowR : 2 * (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlow
      have hratio : (m : ℝ) / (n : ℝ) ≤ 1 / 2 := by
        rw [div_le_iff₀ hnR]
        linarith
      have hratioPos : 0 < (m : ℝ) / (n : ℝ) := div_pos hmR hnR
      have hlog := Real.log_le_log hratioPos hratio
      have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
        rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
        simp
      rw [hhalf] at hlog
      rw [abs_of_nonpos (by linarith : Real.log ((m : ℝ) / (n : ℝ)) ≤ 0)]
      linarith
    · have hhighR : 2 * (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hhigh
      have hratio : (2 : ℝ) ≤ (m : ℝ) / (n : ℝ) := by
        rw [le_div_iff₀ hnR]
        linarith
      have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hratio
      rw [abs_of_nonneg (hlogTwo.le.trans hlog)]
      exact hlog
  rw [max_eq_left (by linarith : Real.log 2 -
    |Real.log ((m : ℝ) / (n : ℝ))| ≤ 0), mul_zero]

private theorem sameBasePow_far
    {b j k : ℕ} (hb : 2 ≤ b) (hjk : j ≠ k) :
    2 * b ^ j ≤ b ^ k ∨ 2 * b ^ k ≤ b ^ j := by
  have hb0 : 0 < b := by omega
  rcases lt_or_gt_of_ne hjk with hjk | hkj
  · left
    calc
      2 * b ^ j ≤ b * b ^ j := Nat.mul_le_mul_right (b ^ j) hb
      _ = b ^ (j + 1) := by rw [pow_succ']
      _ ≤ b ^ k := Nat.pow_le_pow_right hb0 (by omega)
  · right
    calc
      2 * b ^ k ≤ b * b ^ k := Nat.mul_le_mul_right (b ^ k) hb
      _ = b ^ (k + 1) := by rw [pow_succ']
      _ ≤ b ^ j := Nat.pow_le_pow_right hb0 (by omega)

/-- The node aligned with the aperture has strictly positive sample value. -/
theorem suzukiMangoldtAlignedApex_self_pos
    {n : ℕ} (hn : 2 ≤ n) :
    0 < suzukiRectangularPositiveArchSampleChannel (Real.log 2)
        (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) := by
  rw [suzukiMangoldtAlignedApex_sample_eq hn hn]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [div_self hn0, Real.log_one, abs_zero, sub_zero,
    max_eq_right (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le]
  positivity

/-- On every positive power ray, an aligned sample is positive exactly at its own exponent. -/
theorem suzukiMangoldtAlignedApex_samePowerRay_pos_iff
    {b j k : ℕ} (hb : 2 ≤ b) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    0 < suzukiRectangularPositiveArchSampleChannel (Real.log 2)
        (suzukiMangoldtApexAperture (b ^ k))
        (mangoldtLogHaarNode (b ^ j)) ↔ j = k := by
  have hb0 : 0 < b := by omega
  have hbj : 2 ≤ b ^ j := by
    have hpow : b ≤ b ^ j := by
      simpa only [pow_one] using Nat.pow_le_pow_right hb0 hj
    exact hb.trans hpow
  have hbk : 2 ≤ b ^ k := by
    have hpow : b ≤ b ^ k := by
      simpa only [pow_one] using Nat.pow_le_pow_right hb0 hk
    exact hb.trans hpow
  constructor
  · intro hpos
    by_contra hjk
    have hzero := suzukiMangoldtAlignedApex_sample_eq_zero_of_outside hbk hbj
      (sameBasePow_far hb hjk)
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos
  · rintro rfl
    exact suzukiMangoldtAlignedApex_self_pos hbk

end RHTower
