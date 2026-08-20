import GaloisForLFunctions.RHTower.SmoothAFEZetaDualReflection
import GaloisForLFunctions.RHTower.ZetaChiHardyPhase
import GaloisForLFunctions.RHTower.HardyPhaseCellCancellation

/-!
# The Gaussian smooth approximate functional equation for Hardy's `Z`

Multiplying the exact two-series smooth AFE by the positive phase exponential `exp(iθ(τ))` turns
the direct edge into `exp(i(θ(τ) − τ log n))` and, through
`exp_theta_mul_zetaChi_line`, the reflected edge into `exp(−i(θ(τ) − τ log n))`.  The result is an
exact expansion of Hardy's real function `Z` in twisted Hardy phases, which is the shape the cell
cancellation estimate of `HardyPhaseCellCancellation` consumes.
-/

open Complex

noncomputable section

namespace RHTower

private theorem exp_neg_half_log (a : ℝ) (ha : 0 < a) :
    Real.exp (-(Real.log a) / 2) = (Real.sqrt a)⁻¹ := by
  have hsqrt : Real.sqrt a = Real.exp (Real.log a / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos ha]
    congr 1
    ring
  rw [hsqrt, ← Real.exp_neg]
  congr 1
  ring

theorem cpow_neg_linePt (τ : ℝ) {a : ℝ} (ha : 0 < a) :
    ((a : ℂ)) ^ (-linePt τ)
      = (((Real.sqrt a)⁻¹ : ℝ) : ℂ) * Complex.exp (-I * ((τ * Real.log a : ℝ) : ℂ)) := by
  have hne : ((a : ℂ)) ≠ 0 := by
    simpa using ne_of_gt ha
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log ha.le]
  rw [show ((Real.log a : ℝ) : ℂ) * (-linePt τ)
      = ((-(Real.log a) / 2 : ℝ) : ℂ) + -I * ((τ * Real.log a : ℝ) : ℂ) by
    unfold linePt
    push_cast
    ring]
  rw [Complex.exp_add, ← Complex.ofReal_exp, exp_neg_half_log a ha]

theorem cpow_linePt_sub_one (τ : ℝ) {a : ℝ} (ha : 0 < a) :
    ((a : ℂ)) ^ (linePt τ - 1)
      = (((Real.sqrt a)⁻¹ : ℝ) : ℂ) * Complex.exp (I * ((τ * Real.log a : ℝ) : ℂ)) := by
  have hne : ((a : ℂ)) ≠ 0 := by
    simpa using ne_of_gt ha
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log ha.le]
  rw [show ((Real.log a : ℝ) : ℂ) * (linePt τ - 1)
      = ((-(Real.log a) / 2 : ℝ) : ℂ) + I * ((τ * Real.log a : ℝ) : ℂ) by
    unfold linePt
    push_cast
    ring]
  rw [Complex.exp_add, ← Complex.ofReal_exp, exp_neg_half_log a ha]

theorem exp_theta_mul_cpow_neg_linePt (τ : ℝ) {a : ℝ} (ha : 0 < a) :
    Complex.exp (I * (gammaHardyTheta τ : ℂ)) * ((a : ℂ) ^ (-linePt τ))
      = (((Real.sqrt a)⁻¹ : ℝ) : ℂ) *
        Complex.exp (I * ((hardyTwistPhase (Real.log a) τ : ℝ) : ℂ)) := by
  rw [cpow_neg_linePt τ ha, ← mul_assoc, mul_comm (Complex.exp (I * (gammaHardyTheta τ : ℂ)))
    (((Real.sqrt a)⁻¹ : ℝ) : ℂ), mul_assoc, ← Complex.exp_add]
  congr 2
  rw [hardyTwistPhase]
  push_cast
  ring

theorem exp_neg_theta_mul_cpow_linePt_sub_one (τ : ℝ) {a : ℝ} (ha : 0 < a) :
    Complex.exp (-I * (gammaHardyTheta τ : ℂ)) * ((a : ℂ) ^ (linePt τ - 1))
      = (((Real.sqrt a)⁻¹ : ℝ) : ℂ) *
        Complex.exp (-I * ((hardyTwistPhase (Real.log a) τ : ℝ) : ℂ)) := by
  rw [cpow_linePt_sub_one τ ha, ← mul_assoc, mul_comm (Complex.exp (-I * (gammaHardyTheta τ : ℂ)))
    (((Real.sqrt a)⁻¹ : ℝ) : ℂ), mul_assoc, ← Complex.exp_add]
  congr 2
  rw [hardyTwistPhase]
  push_cast
  ring

/-- **The Gaussian smooth approximate functional equation for Hardy's `Z`.**  Exact and
unconditional for every cutoff scale `x > 0`. -/
theorem hardyZ_eq_two_tsum_smoothAFE {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    (hardyZ τ : ℂ) =
      (∑' n : ℕ, ((((Real.sqrt ((n : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
          Complex.exp (I * ((hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ : ℝ) : ℂ))) *
          smoothAFECutoff (((n : ℝ) + 1) / x)) +
      (∑' n : ℕ, ((((Real.sqrt ((n : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
          Complex.exp (-I * ((hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ : ℝ) : ℂ))) *
          smoothAFEZetaDualWeight τ (((n : ℝ) + 1) * x)) -
      Complex.exp (I * (gammaHardyTheta τ : ℂ)) *
        smoothAFEZetaShiftedPoleResidue (linePt τ) x := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  rw [← exp_theta_mul_riemannZeta_line_eq_hardyZ τ,
    riemannZeta_line_eq_two_tsum_smoothAFE_dualWeight hx τ]
  rw [mul_sub, mul_add, ← tsum_mul_left, ← tsum_mul_left]
  congr 1
  congr 1
  · refine tsum_congr fun n => ?_
    rw [← mul_assoc]
    congr 1
    have h := exp_theta_mul_cpow_neg_linePt τ (hpos n)
    rw [show ((((n : ℝ) + 1 : ℝ)) : ℂ) = ((n : ℂ) + 1) by push_cast; ring] at h
    exact h
  · refine tsum_congr fun n => ?_
    rw [← mul_assoc, ← mul_assoc, exp_theta_mul_zetaChi_line]
    congr 1
    have h := exp_neg_theta_mul_cpow_linePt_sub_one τ (hpos n)
    rw [show ((((n : ℝ) + 1 : ℝ)) : ℂ) = ((n : ℂ) + 1) by push_cast; ring] at h
    exact h

end RHTower

end
