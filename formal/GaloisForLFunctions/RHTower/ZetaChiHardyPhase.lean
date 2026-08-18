import GaloisForLFunctions.RHTower.HardyZPhaseAsymptotic

/-!
# The functional-equation factor is the square of the Hardy phase

On the critical line `1 - s = conj s`, so the archimedean ratio `zetaChi s = Gammaℝ(1-s)/Gammaℝ(s)`
is `conj G / G` with `G = Gammaℝ(½+iτ)`.  Dividing numerator and denominator by `‖G‖` identifies it
with the square of the normalized Gamma phase, hence with `exp(-2iθ(τ))` for the branch-free
Riemann--Siegel phase lift `θ = gammaHardyTheta`.

This is the phase-gauge identity that turns the two-series Gaussian smooth approximate functional
equation into a real expansion of Hardy's `Z`: multiplying by `exp(iθ)` sends the direct edge to
`exp(i(θ - τ log n))` and the reflected edge to `exp(-i(θ - τ log n))`.
-/

open Complex

noncomputable section

namespace RHTower

theorem one_sub_linePt (τ : ℝ) : 1 - linePt τ = (starRingEnd ℂ) (linePt τ) := by
  apply Complex.ext
  · simp [linePt]
    norm_num
  · simp [linePt]

/-- **The functional-equation factor on the critical line is the square of the Hardy phase.** -/
theorem zetaChi_line_eq_gammaHardyPhase_sq (τ : ℝ) :
    zetaChi (linePt τ) = gammaHardyPhase τ ^ 2 := by
  have hG : Gammaℝ (linePt τ) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (linePt_re_pos τ)
  have hn : (‖Gammaℝ (linePt τ)‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hG)
  have hmul : Gammaℝ (linePt τ) * (starRingEnd ℂ) (Gammaℝ (linePt τ))
      = (‖Gammaℝ (linePt τ)‖ : ℂ) ^ 2 := Complex.mul_conj' _
  have hcG : (starRingEnd ℂ) (Gammaℝ (linePt τ)) ≠ 0 := by
    simpa using hG
  rw [zetaChi, one_sub_linePt, Gammaℝ_conj, gammaHardyPhase, div_pow, ← hmul]
  field_simp

/-- **The functional-equation factor is the negative double phase exponential.** -/
theorem zetaChi_line_eq_exp_neg_two_theta (τ : ℝ) :
    zetaChi (linePt τ) = Complex.exp (-2 * I * (gammaHardyTheta τ : ℂ)) := by
  rw [zetaChi_line_eq_gammaHardyPhase_sq, gammaHardyPhase_eq_exp_neg_theta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **Phase unwinding of the reflected edge.**  Multiplying the functional-equation factor by the
positive phase exponential flips the sign of the phase. -/
theorem exp_theta_mul_zetaChi_line (τ : ℝ) :
    Complex.exp (I * (gammaHardyTheta τ : ℂ)) * zetaChi (linePt τ)
      = Complex.exp (-I * (gammaHardyTheta τ : ℂ)) := by
  rw [zetaChi_line_eq_exp_neg_two_theta, ← Complex.exp_add]
  congr 1
  ring

end RHTower

end
