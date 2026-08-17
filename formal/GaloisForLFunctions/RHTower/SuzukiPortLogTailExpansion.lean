import GaloisForLFunctions.RHTower.SuzukiPrimeSeamHankelStrength
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# The logarithmic port tail is a constant plus a square-integrable remainder

The only long-range term of a completed ground mode's exterior residual is the logarithmic kernel,
and for a mode supported in `[-a, a]` the elementary expansion

`1/(t - y) = 1/t + y/(t(t - y))`

separates it into a pure `1/t` head and a remainder.  Beyond `t ≥ 2a` the remainder is bounded by
`2a/t²`, so `t` times it is bounded by `2a/t` — and `t ↦ 1/t` is square integrable on any ray
bounded away from the origin.  Hence `t·r(t)` is square integrable on the tail, which is exactly
what the `H¹` conclusion consumes.

The model head is handled by the identity `t/(1+t) = 1 - 1/(1+t)`, whose transform is a
distribution at zero frequency plus a principal value plus a locally square-integrable function.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

/-! ## The elementary separation -/

/-- **The elementary logarithmic-kernel expansion.** -/
theorem inv_sub_expansion {t y : ℝ} (ht : t ≠ 0) (hty : t - y ≠ 0) :
    1 / (t - y) = 1 / t + y / (t * (t - y)) := by
  field_simp
  ring

/-- **`(88)`: the model tail.** -/
theorem tail_model {t : ℝ} (ht : t ≠ -1) :
    t / (1 + t) = 1 - 1 / (1 + t) := by
  have h : (1 : ℝ) + t ≠ 0 := by
    intro h
    exact ht (by linarith)
  field_simp
  ring

/-! ## The remainder bound -/

/-- Beyond twice the aperture the remainder is quadratically small. -/
theorem abs_remainder_le {a t y : ℝ} (ha : 0 < a) (hy : |y| ≤ a) (ht : 2 * a ≤ t) :
    |y / (t * (t - y))| ≤ 2 * a / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  rcases abs_le.mp hy with ⟨hy1, hy2⟩
  have hty : t / 2 ≤ t - y := by linarith
  have hty0 : 0 < t - y := by linarith
  have hden : 0 < t * (t - y) := by positivity
  rw [abs_div, abs_of_pos hden, div_le_div_iff₀ hden (by positivity)]
  calc |y| * t ^ 2 ≤ a * t ^ 2 := by nlinarith [sq_nonneg t]
    _ ≤ 2 * a * (t * (t - y)) := by
        have hstep : t * (t / 2) ≤ t * (t - y) := mul_le_mul_of_nonneg_left hty ht0.le
        nlinarith [hstep, ha.le]

/-- The scaled remainder decays like the reciprocal. -/
theorem abs_mul_remainder_le {a t y : ℝ} (ha : 0 < a) (hy : |y| ≤ a) (ht : 2 * a ≤ t) :
    |t * (y / (t * (t - y)))| ≤ 2 * a / t := by
  have ht0 : 0 < t := by linarith
  rw [abs_mul, abs_of_pos ht0]
  have hbase := abs_remainder_le ha hy ht
  calc t * |y / (t * (t - y))| ≤ t * (2 * a / t ^ 2) :=
        mul_le_mul_of_nonneg_left hbase ht0.le
    _ = 2 * a / t := by
        field_simp

/-- The squared scaled remainder is dominated by a multiple of `1/t²`. -/
theorem sq_abs_mul_remainder_le {a t y : ℝ} (ha : 0 < a) (hy : |y| ≤ a) (ht : 2 * a ≤ t) :
    (t * (y / (t * (t - y)))) ^ 2 ≤ (2 * a) ^ 2 / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hb := abs_mul_remainder_le ha hy ht
  have hnn : (0 : ℝ) ≤ 2 * a / t := by positivity
  calc (t * (y / (t * (t - y)))) ^ 2 = |t * (y / (t * (t - y)))| ^ 2 := (sq_abs _).symm
    _ ≤ (2 * a / t) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
    _ = (2 * a) ^ 2 / t ^ 2 := by rw [div_pow]

/-- **The tail is square integrable.**  The reciprocal square is integrable on any ray bounded away
from the origin, so the scaled remainder is square integrable there. -/
theorem integrableOn_inv_sq_Ioi {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => 1 / t ^ 2) (Ioi c) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hc
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t ht
  have ht0 : 0 < t := lt_trans hc ht
  have hval : t ^ (-2 : ℝ) = (t ^ (2 : ℝ))⁻¹ := by
    rw [← Real.rpow_neg ht0.le]
  simp [hval]

end RHTower
