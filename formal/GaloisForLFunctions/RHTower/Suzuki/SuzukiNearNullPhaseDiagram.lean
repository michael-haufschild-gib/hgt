import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The near-null / exponential-scale alternative and the low-only ceiling

Two elementary facts split the high-assisted branch.  The minimum of two nonnegative Rayleigh
quotients never exceeds their geometric mean, so the capacity bound on the product bounds the
smaller one; and if the aperture is at most a constant times the squared logarithm of the inverse
shift, then the shift is exponentially small in the square root of the aperture.

The low-only branch has a genuine rate because its certificate is support confined: comparing the
square-root active-zero floor with the zero count below the cutoff gives a quartic inequality for
the shift, and taking fourth roots gives the ceiling.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## `(427)`: the geometric-mean step -/

/-- **The minimum of two nonnegative numbers is at most their geometric mean.** -/
theorem min_le_sqrt_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : min x y ≤ Real.sqrt (x * y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h]
    have hxx : x * x ≤ x * y := mul_le_mul_of_nonneg_left h hx
    calc x = Real.sqrt (x * x) := by rw [← sq, Real.sqrt_sq hx]
      _ ≤ Real.sqrt (x * y) := Real.sqrt_le_sqrt hxx
  · rw [min_eq_right h]
    have hyy : y * y ≤ x * y := mul_le_mul_of_nonneg_right h hy
    calc y = Real.sqrt (y * y) := by rw [← sq, Real.sqrt_sq hy]
      _ ≤ Real.sqrt (x * y) := Real.sqrt_le_sqrt hyy

/-! ## `(428)`: the exponential shift scale -/

/-- **`(428)`: an aperture controlled by the squared logarithm of the inverse shift forces an
exponentially small shift.** -/
theorem exp_decay_of_log_sq_bound {a C r : ℝ} (hC : 0 < C) (hr0 : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ a) (hbound : a ≤ C * Real.log (1 / r) ^ 2) :
    r ≤ Real.exp (-(Real.sqrt a / Real.sqrt C)) := by
  have hinv : (1 : ℝ) < 1 / r := by
    rw [lt_div_iff₀ hr0]
    linarith
  have hlog : 0 < Real.log (1 / r) := Real.log_pos hinv
  have hdiv : a / C ≤ Real.log (1 / r) ^ 2 := by
    rw [div_le_iff₀ hC]
    linarith
  have hsqrt : Real.sqrt (a / C) ≤ Real.log (1 / r) := by
    calc Real.sqrt (a / C) ≤ Real.sqrt (Real.log (1 / r) ^ 2) := Real.sqrt_le_sqrt hdiv
      _ = Real.log (1 / r) := Real.sqrt_sq hlog.le
  have hsplit : Real.sqrt (a / C) = Real.sqrt a / Real.sqrt C := Real.sqrt_div ha C
  rw [hsplit] at hsqrt
  have hexp : Real.exp (Real.sqrt a / Real.sqrt C) ≤ 1 / r := by
    calc Real.exp (Real.sqrt a / Real.sqrt C) ≤ Real.exp (Real.log (1 / r)) :=
          Real.exp_le_exp.mpr hsqrt
      _ = 1 / r := Real.exp_log (by linarith)
  rw [Real.exp_neg]
  rw [le_div_iff₀ hr0] at hexp
  rw [le_inv_comm₀ hr0 (Real.exp_pos _), inv_eq_one_div, le_div_iff₀ hr0]
  linarith [hexp]

/-! ## `(432)`: the low-only ceiling -/

/-- **`(432)`: a quartic bound on the shift gives the fourth-root ceiling.** -/
theorem rate_of_quartic_bound {r X : ℝ} (hr : 0 ≤ r) (h : r ^ 4 ≤ X) :
    r ≤ X ^ ((1 : ℝ) / 4) := by
  have hr4 : (0 : ℝ) ≤ r ^ 4 := by positivity
  have hmono : (r ^ 4) ^ ((1 : ℝ) / 4) ≤ X ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow hr4 h (by norm_num)
  have hid : (r ^ 4 : ℝ) ^ ((1 : ℝ) / 4) = r := by
    rw [← Real.rpow_natCast r 4, ← Real.rpow_mul hr]
    norm_num
  rwa [hid] at hmono

end GaloisForLFunctions.RHTower
