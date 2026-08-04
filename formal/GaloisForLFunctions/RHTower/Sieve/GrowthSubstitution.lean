import GaloisForLFunctions.RHTower.Sieve.SavingSubstitution

/-!
# The right edge at the balanced parameter

The right abscissa `d(K) = 1 + c₀/(2 log⁹K)` contributes a growth rather than a saving.  At the
balanced parameter it is bounded by `exp(c₀ (log x)^{1/10})`, and the truncation height is at least
`exp((log x)^{1/10})/4`, so the ratio the truncation error forms is at most
`4·exp((c₀-1)(log x)^{1/10})` — decaying, because `c₀ ≤ 1/2`.
-/

namespace RHTower.Sieve

open Real

/-- The right-edge power, written as the trivial size times an explicit growth. -/
theorem rpow_rightAbscissa {K : ℕ} {x : ℝ} (hx : 0 < x) :
    x ^ rightAbscissa K
      = x * Real.exp ((zeroFreeConst / (2 * (Real.log K) ^ 9)) * Real.log x) := by
  rw [rightAbscissa, Real.rpow_def_of_pos hx,
    show Real.log x * (1 + zeroFreeConst / (2 * (Real.log K) ^ 9))
      = Real.log x + (zeroFreeConst / (2 * (Real.log K) ^ 9)) * Real.log x by ring,
    Real.exp_add, Real.exp_log hx]

/-- **The right-edge power at the balanced parameter.** -/
theorem rpow_rightAbscissa_le {x y : ℝ} (hx : 1 ≤ Real.log x) (hy0 : 0 < y)
    (hy1 : 0 ≤ Real.log y) (hxy : Real.log y ≤ 2 * Real.log x) :
    y ^ rightAbscissa (contourParam x)
      ≤ y * Real.exp (zeroFreeConst * (Real.log x) ^ ((1 : ℝ) / 10)) := by
  have hx0 : (0 : ℝ) ≤ Real.log x := by linarith
  have hA0 := zeroFreeConst_pos
  set t : ℝ := (Real.log x) ^ ((1 : ℝ) / 10) with htdef
  have ht1 : 1 ≤ t := by rw [htdef]; exact Real.one_le_rpow hx (by norm_num)
  have ht0 : (0 : ℝ) < t := by linarith
  have hten : t ^ (10 : ℕ) = Real.log x := rpow_tenth_pow hx0
  have hL : t ≤ Real.log (contourParam x) := le_log_contourParam x
  have hL0 : (0 : ℝ) < Real.log (contourParam x) := by linarith
  have ht9 : t ^ 9 ≤ (Real.log (contourParam x)) ^ 9 := by gcongr
  have ht9pos : (0 : ℝ) < t ^ 9 := by positivity
  have hδ : zeroFreeConst / (2 * (Real.log (contourParam x)) ^ 9) ≤ zeroFreeConst / (2 * t ^ 9) := by
    gcongr
  rw [rpow_rightAbscissa hy0]
  refine mul_le_mul_of_nonneg_left ?_ hy0.le
  refine Real.exp_le_exp.2 ?_
  have hstep : zeroFreeConst / (2 * (Real.log (contourParam x)) ^ 9) * Real.log y
      ≤ zeroFreeConst / (2 * t ^ 9) * (2 * Real.log x) := by
    refine mul_le_mul hδ hxy hy1 (by positivity)
  refine le_trans hstep (le_of_eq ?_)
  have hexpand : Real.log x = t * t ^ 9 := by
    rw [show t * t ^ 9 = t ^ (10 : ℕ) by ring, hten]
  rw [hexpand]
  field_simp

/-- **The truncation height at the balanced parameter.** -/
theorem exp_div_four_le_truncHeight {x : ℝ} (ht : 2 ≤ (Real.log x) ^ ((1 : ℝ) / 10)) :
    Real.exp ((Real.log x) ^ ((1 : ℝ) / 10)) / 4 ≤ truncHeight (contourParam x) := by
  set t : ℝ := (Real.log x) ^ ((1 : ℝ) / 10) with htdef
  have he1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have he2 : (6 : ℝ) ≤ Real.exp 2 := by
    have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [he1, Real.exp_pos 1]
  have het : Real.exp 2 ≤ Real.exp t := Real.exp_le_exp.2 ht
  have h6 : (6 : ℝ) ≤ Real.exp t := by linarith
  have hK : Real.exp t ≤ ((contourParam x : ℕ) : ℝ) := Nat.le_ceil _
  rw [truncHeight]
  linarith

end RHTower.Sieve
