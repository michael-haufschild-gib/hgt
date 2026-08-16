import GaloisForLFunctions.RHTower.SuzukiTorqueEulerTransform

/-!
# `(18)`: the archimedean layer's exponential order

Its closed form is four elementary pieces, three of them decaying; only the `e^{3L/2}` piece can
grow, and its polynomial factor is linear.  So the layer is `O(L³e^{3L/2})` with a fixed constant,
which is all the card asks — it says the constants are inessential and uses the bound only to place
the convergence abscissa at most `3/2`.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

/-- **`(18)`: the archimedean layer has exponential order `3/2`.** -/
theorem abs_suzukiFreeArchPositionTorque_le {L : ℝ} (hL : 1 ≤ L) :
    |suzukiFreeArchPositionTorque L| ≤ 22 * L ^ 3 * Real.exp (3 * L / 2) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hE : (1 : ℝ) ≤ Real.exp (3 * L / 2) := Real.one_le_exp (by linarith)
  have hEp : (0 : ℝ) < Real.exp (3 * L / 2) := Real.exp_pos _
  have he1 : Real.exp (-L / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have he1p : (0 : ℝ) < Real.exp (-L / 2) := Real.exp_pos _
  have he3 : Real.exp (-3 * L / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have he3p : (0 : ℝ) < Real.exp (-3 * L / 2) := Real.exp_pos _
  have hL3 : L ≤ L ^ 3 := by
    nlinarith [mul_nonneg (mul_nonneg hL0.le (by linarith : (0:ℝ) ≤ L - 1))
      (by linarith : (0:ℝ) ≤ L + 1)]
  have hL3nn : (0 : ℝ) ≤ L ^ 3 := by positivity
  have hL3E : L ^ 3 ≤ L ^ 3 * Real.exp (3 * L / 2) := by nlinarith [hE, hL3nn]
  have hLE : L ≤ L ^ 3 * Real.exp (3 * L / 2) := le_trans hL3 hL3E
  have hLLE : L * Real.exp (3 * L / 2) ≤ L ^ 3 * Real.exp (3 * L / 2) :=
    mul_le_mul_of_nonneg_right hL3 hEp.le
  rw [suzukiFreeArchPositionTorque_closedForm, abs_le]
  constructor
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 * L + 8) he1p.le,
      mul_nonneg (by linarith : (0:ℝ) ≤ 2 * L / 9 + 8 / 27) he3p.le,
      mul_le_mul_of_nonneg_left hE (by linarith : (0:ℝ) ≤ 2 * L / 9), hLE, hLLE]
  · nlinarith [mul_le_mul_of_nonneg_right he1 (by linarith : (0:ℝ) ≤ 2 * L + 8),
      mul_le_mul_of_nonneg_right he3 (by linarith : (0:ℝ) ≤ 2 * L / 9 + 8 / 27),
      mul_le_mul_of_nonneg_right hLLE (by norm_num : (0:ℝ) ≤ 1), hLE, hLLE,
      mul_le_mul_of_nonneg_left hE (by linarith : (0:ℝ) ≤ L)]

end RHTower
