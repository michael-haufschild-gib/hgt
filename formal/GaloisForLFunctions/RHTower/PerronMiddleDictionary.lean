import GaloisForLFunctions.RHTower.PerronLineSplit

/-!
# The `2πξ → iy` dictionary for the middle Perron integral

`∫_{-W}^{W} F(a+2πiw) dw = (2π)⁻¹·∫_{-2πW}^{2πW} F(a+iy) dy` — the
substitution `y = 2πw` matching the `w`-line integral of the smoothed
explicit formula with the vertical-edge parametrization of
`rectIntegral`.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set

/-- **The middle-integral dictionary**: substituting `y = 2πw`. -/
theorem integral_middle_eq_interval {x a W : ℝ} (hW : 0 ≤ W) :
    ∫ w in Set.Ioc (-W) W,
        - deriv riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
          / riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
        * ((x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I)
          / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ (2 : ℕ))
      = (2 * Real.pi)⁻¹ •
        ∫ y in (-(2 * Real.pi * W))..(2 * Real.pi * W),
          - deriv riemannZeta ((a : ℂ) + y * Complex.I)
            / riemannZeta ((a : ℂ) + y * Complex.I)
          * ((x : ℂ) ^ ((a : ℂ) + y * Complex.I)
            / ((a : ℂ) + y * Complex.I) ^ (2 : ℕ)) := by
  have hπ0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hle : -W ≤ W := by linarith
  calc ∫ w in Set.Ioc (-W) W,
        - deriv riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
          / riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
        * ((x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I)
          / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ (2 : ℕ))
      = ∫ w in (-W)..W,
        - deriv riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
          / riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
        * ((x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I)
          / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ (2 : ℕ)) :=
        (intervalIntegral.integral_of_le hle).symm
    _ = ∫ w in (-W)..W, (fun y : ℝ =>
          - deriv riemannZeta ((a : ℂ) + y * Complex.I)
            / riemannZeta ((a : ℂ) + y * Complex.I)
          * ((x : ℂ) ^ ((a : ℂ) + y * Complex.I)
            / ((a : ℂ) + y * Complex.I) ^ (2 : ℕ))) (2 * Real.pi * w) := by
        apply intervalIntegral.integral_congr
        intro w _
        show - deriv riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
            / riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
          * ((x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I)
            / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ (2 : ℕ))
          = - deriv riemannZeta ((a : ℂ)
              + ((2 * Real.pi * w : ℝ) : ℂ) * Complex.I)
            / riemannZeta ((a : ℂ)
              + ((2 * Real.pi * w : ℝ) : ℂ) * Complex.I)
          * ((x : ℂ) ^ ((a : ℂ)
              + ((2 * Real.pi * w : ℝ) : ℂ) * Complex.I)
            / ((a : ℂ)
              + ((2 * Real.pi * w : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ))
        rw [show ((2 * Real.pi * w : ℝ) : ℂ)
            = 2 * (Real.pi : ℂ) * (w : ℂ) from by push_cast; ring]
    _ = (2 * Real.pi)⁻¹ •
          ∫ y in (2 * Real.pi * -W)..(2 * Real.pi * W), (fun y : ℝ =>
          - deriv riemannZeta ((a : ℂ) + y * Complex.I)
            / riemannZeta ((a : ℂ) + y * Complex.I)
          * ((x : ℂ) ^ ((a : ℂ) + y * Complex.I)
            / ((a : ℂ) + y * Complex.I) ^ (2 : ℕ))) y :=
        intervalIntegral.integral_comp_mul_left (fun y : ℝ =>
          - deriv riemannZeta ((a : ℂ) + y * Complex.I)
            / riemannZeta ((a : ℂ) + y * Complex.I)
          * ((x : ℂ) ^ ((a : ℂ) + y * Complex.I)
            / ((a : ℂ) + y * Complex.I) ^ (2 : ℕ))) hπne
    _ = (2 * Real.pi)⁻¹ •
          ∫ y in (-(2 * Real.pi * W))..(2 * Real.pi * W),
          - deriv riemannZeta ((a : ℂ) + y * Complex.I)
            / riemannZeta ((a : ℂ) + y * Complex.I)
          * ((x : ℂ) ^ ((a : ℂ) + y * Complex.I)
            / ((a : ℂ) + y * Complex.I) ^ (2 : ℕ)) := by
        rw [show 2 * Real.pi * -W = -(2 * Real.pi * W) from by ring]

end RHTower
