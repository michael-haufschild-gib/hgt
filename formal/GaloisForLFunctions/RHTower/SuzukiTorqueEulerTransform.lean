import GaloisForLFunctions.RHTower.SuzukiTorqueTotalTransform

/-!
# `(16)`: the torque transform is the completed Xi curvature difference

Casting `(14)` into `ℂ` and feeding the prime series into the corpus's Euler expression identifies
the real Laplace transform with `suzukiPositionTorqueEulerSource`, and the corpus's exact
source-to-Xi identity then turns that into the curvature difference — the meromorphic continuation
the Landau argument needs.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

/-- **`(14)` in the corpus's Euler form.** -/
theorem integral_suzukiFreePositionTorque_mul_exp_eq_eulerSource {σ : ℝ} (hσ : 3 / 2 < σ) :
    ((∫ L in Ioi (0 : ℝ), suzukiFreePositionTorque L * Real.exp (-σ * L) : ℝ) : ℂ)
      = suzukiPositionTorqueEulerSource (σ : ℂ) := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hne : (σ : ℂ) ≠ 0 := by
    simpa using (ne_of_gt hσ0)
  have hne1 : (σ : ℂ) - 3 / 2 ≠ 0 := by
    intro h
    have hc : ((σ - 3 / 2 : ℝ) : ℂ) = 0 := by push_cast; exact h
    have := Complex.ofReal_eq_zero.mp hc
    linarith
  have hne2 : (σ : ℂ) + 1 / 2 ≠ 0 := by
    intro h
    have hc : ((σ + 1 / 2 : ℝ) : ℂ) = 0 := by push_cast; exact h
    have := Complex.ofReal_eq_zero.mp hc
    linarith
  have hne3 : (σ : ℂ) + 3 / 2 ≠ 0 := by
    intro h
    have hc : ((σ + 3 / 2 : ℝ) : ℂ) = 0 := by push_cast; exact h
    have := Complex.ofReal_eq_zero.mp hc
    linarith
  have hA : ((1 / (2 * σ ^ (2 : ℕ))
        * (1 / (σ + 1 / 2) ^ (2 : ℕ) - 1 / (σ - 3 / 2) ^ (2 : ℕ) + 1 / (σ + 3 / 2) ^ (2 : ℕ)) : ℝ) : ℂ)
      = 1 / (2 * (σ : ℂ) ^ (2 : ℕ))
        * (1 / ((σ : ℂ) + 1 / 2) ^ (2 : ℕ) - 1 / ((σ : ℂ) - 3 / 2) ^ (2 : ℕ)
          + 1 / ((σ : ℂ) + 3 / 2) ^ (2 : ℕ)) := by
    push_cast
    ring
  have hB : (((∑' n : ℕ, suzukiTentCoeff n * Real.exp (-σ * Real.log n)) / σ ^ (2 : ℕ) : ℝ) : ℂ)
      = ((1 : ℂ) / 2 * LSeries (LSeries.logMul filteredVonMangoldtCoeff) ((σ : ℂ) - 1 / 2))
        / (σ : ℂ) ^ (2 : ℕ) := by
    rw [Complex.ofReal_div, tsum_suzukiTentCoeff_mul_exp hσ]
    push_cast
    ring
  rw [integral_suzukiFreePositionTorque_mul_exp hσ, Complex.ofReal_add, hA, hB,
    suzukiPositionTorqueEulerSource]
  field_simp
  ring

/-- **`(16)`: the torque transform is the completed Xi curvature difference.** -/
theorem integral_suzukiFreePositionTorque_mul_exp_eq_continuation {σ : ℝ} (hσ : 3 / 2 < σ) :
    ((∫ L in Ioi (0 : ℝ), suzukiFreePositionTorque L * Real.exp (-σ * L) : ℝ) : ℂ)
      = suzukiPositionTorqueLaplaceContinuation (σ : ℂ) := by
  rw [integral_suzukiFreePositionTorque_mul_exp_eq_eulerSource hσ,
    suzukiPositionTorqueLaplaceContinuation_eq_eulerSource (s := (σ : ℂ)) (by simpa using hσ)]

end RHTower
