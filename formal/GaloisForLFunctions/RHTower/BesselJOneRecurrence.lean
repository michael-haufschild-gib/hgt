import GaloisForLFunctions.RHTower.BesselJZeroODE

/-!
# The Bessel function of order one and the recurrence `(u J₁)' = u J₀`

The order-one Bessel function is minus the derivative of the order-zero one, so the integral
representation of `J₀` already produces it.  The recurrence `(u J₁(u))' = u J₀(u)` then reduces to
the integration-by-parts identity behind Bessel's equation, and holds at every real point including
the origin.

The amplitude bound `|J₁(u)| ≤ |u|/2` follows from `|sin x| ≤ |x|` under the integral sign.

Together these are the two facts a weighted Bessel integral needs before an integration by parts:
an exact antiderivative for `u J₀(u)` and a bound on it near the origin.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set intervalIntegral

/-- The Bessel function of order one, as minus the derivative of the order-zero one. -/
def besselJ1 (u : ℝ) : ℝ := -besselJ0Deriv u

theorem besselJ1_eq_integral (u : ℝ) :
    besselJ1 u = (1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * Real.sin (u * Real.sin θ) := by
  simp [besselJ1, besselJ0Deriv]

theorem besselJ1_zero : besselJ1 0 = 0 := by
  simp [besselJ1_eq_integral]

theorem hasDerivAt_besselJ1 (u : ℝ) : HasDerivAt besselJ1 (-besselJ0SecondDeriv u) u :=
  (hasDerivAt_besselJ0Deriv u).neg

/-- The order-one function is `u` times the combination appearing in Bessel's equation. -/
theorem besselJ1_eq_mul (u : ℝ) :
    besselJ1 u = u * (besselJ0SecondDeriv u + besselJ0 u) := by
  rw [besselJ1_eq_integral, besselJ0SecondDeriv_add_besselJ0, integral_sin_mul_sin_eq]
  ring

/-- **The Bessel recurrence** `(u J₁(u))' = u J₀(u)`, valid at every real point. -/
theorem hasDerivAt_mul_besselJ1 (u : ℝ) :
    HasDerivAt (fun r : ℝ => r * besselJ1 r) (u * besselJ0 u) u := by
  have h : HasDerivAt (fun r : ℝ => r * besselJ1 r)
      ((1 : ℝ) * besselJ1 u + u * -besselJ0SecondDeriv u) u :=
    (hasDerivAt_id u).mul (hasDerivAt_besselJ1 u)
  have hval : (1 : ℝ) * besselJ1 u + u * -besselJ0SecondDeriv u = u * besselJ0 u := by
    rw [besselJ1_eq_mul]
    ring
  rwa [hval] at h

/-- The scaled recurrence `d/dr [r·J₁(c r)] = c·r·J₀(c r)`. -/
theorem hasDerivAt_mul_besselJ1_scaled (c r : ℝ) :
    HasDerivAt (fun s : ℝ => s * besselJ1 (c * s)) (c * r * besselJ0 (c * r)) r := by
  rcases eq_or_ne c 0 with rfl | hc
  · simpa [besselJ1_zero] using (hasDerivAt_const r (0 : ℝ))
  · have hinner : HasDerivAt (fun s : ℝ => c * s) c r := by
      simpa using (hasDerivAt_id r).const_mul c
    have h : HasDerivAt (fun s : ℝ => (c * s) * besselJ1 (c * s))
        ((c * r) * besselJ0 (c * r) * c) r :=
      (hasDerivAt_mul_besselJ1 (c * r)).comp r hinner
    have hsm : HasDerivAt (fun s : ℝ => c⁻¹ * ((c * s) * besselJ1 (c * s)))
        (c⁻¹ * ((c * r) * besselJ0 (c * r) * c)) r := h.const_mul (c⁻¹)
    have hfun : (fun s : ℝ => c⁻¹ * ((c * s) * besselJ1 (c * s)))
        = fun s : ℝ => s * besselJ1 (c * s) := by
      funext s
      field_simp
    have hval : c⁻¹ * ((c * r) * besselJ0 (c * r) * c) = c * r * besselJ0 (c * r) := by
      field_simp
    rw [hfun, hval] at hsm
    exact hsm

/-- The near-origin amplitude bound `|J₁(u)| ≤ |u|/2`. -/
theorem abs_besselJ1_le (u : ℝ) : |besselJ1 u| ≤ |u| / 2 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hle : |∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * Real.sin (u * Real.sin θ)|
      ≤ ∫ θ in (0 : ℝ)..Real.pi, |u| * Real.sin θ ^ 2 := by
    refine le_trans (intervalIntegral.abs_integral_le_integral_abs hpi.le) ?_
    refine intervalIntegral.integral_mono_on hpi.le
      ((continuous_sin_mul_sin u).abs.intervalIntegrable _ _)
      ((continuous_const.mul ((Real.continuous_sin).pow 2)).intervalIntegrable _ _) ?_
    intro θ hθ
    have hsnn : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ.1, hθ.2⟩
    calc |Real.sin θ * Real.sin (u * Real.sin θ)|
        = |Real.sin θ| * |Real.sin (u * Real.sin θ)| := abs_mul _ _
      _ ≤ Real.sin θ * |u * Real.sin θ| := by
          rw [abs_of_nonneg hsnn]
          exact mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs) hsnn
      _ = |u| * Real.sin θ ^ 2 := by
          rw [abs_mul, abs_of_nonneg hsnn]
          ring
  have hint : (∫ θ in (0 : ℝ)..Real.pi, |u| * Real.sin θ ^ 2) = |u| * (Real.pi / 2) := by
    rw [intervalIntegral.integral_const_mul, integral_sin_sq]
    simp
  rw [hint] at hle
  rw [besselJ1_eq_integral, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / Real.pi)]
  calc 1 / Real.pi * |∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * Real.sin (u * Real.sin θ)|
      ≤ 1 / Real.pi * (|u| * (Real.pi / 2)) := by
        exact mul_le_mul_of_nonneg_left hle (by positivity)
    _ = |u| / 2 := by field_simp

end GaloisForLFunctions.RHTower
