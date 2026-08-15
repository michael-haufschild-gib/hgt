import GaloisForLFunctions.RHTower.ProlateRadialODEBridge
import GaloisForLFunctions.RHTower.ProlateSeparationEnergy

/-!
# The prolate second moment is bounded by the radial separation ratio

The exact prolate Rayleigh identity

`s · ∫_{-1}^{1} Φ² = (∫_{-1}^{1} (1−x²)Φ′²)/c² + ∫_{-1}^{1} x²Φ² ,     s = −χ/c² ,`

has a nonnegative gradient term, because `1 − x² ≥ 0` on the aperture.  Dropping it gives the
normalized second-moment bound

`∫_{-1}^{1} x²Φ² ≤ s · ∫_{-1}^{1} Φ²` .

In the Hermite variable this reads `∫ ξ²u² ≤ (c s) ∫ u²`, so the rescaled profile's second moment is
controlled by the oscillator separation constant alone — the one moment of a prolate mode that stays
finite and uniformly bounded, and the tightness that makes the fixed-window comparison give a global
conclusion.
-/

open MeasureTheory Set

namespace RHTower

/-- The prolate gradient term is nonnegative on the aperture. -/
theorem integral_prolateGradient_nonneg {Phi : ℝ → ℝ} :
    (0 : ℝ) ≤ ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) * (deriv Phi x) ^ 2 := by
  refine intervalIntegral.integral_nonneg (by norm_num) ?_
  intro x hx
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
  nlinarith [sq_nonneg (deriv Phi x)]

/-- **Second-moment bound.**  A prolate eigenfunction's normalized second moment on the aperture is
at most its radial separation ratio. -/
theorem integral_sq_mul_sq_le_separation
    {c chi : ℝ} (hc : c ≠ 0) {Phi : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (heig : ∀ x ∈ Icc (-1 : ℝ) 1, prolateSLAction c Phi x = chi * Phi x) :
    (∫ x in (-1 : ℝ)..1, x ^ 2 * Phi x ^ 2)
      ≤ radialSeparationRatio c chi * ∫ x in (-1 : ℝ)..1, Phi x ^ 2 := by
  have hR := GaloisForLFunctions.RHTower.neg_separation_div_sq_mul_integral_sq_eq hc hsm heig
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  have hdivnn : (0 : ℝ)
      ≤ (∫ x in (-1 : ℝ)..1, (1 - x ^ 2) * (deriv Phi x) ^ 2) / c ^ 2 :=
    div_nonneg (integral_prolateGradient_nonneg (Phi := Phi)) hc2.le
  rw [radialSeparationRatio]
  linarith [hR]

end RHTower
