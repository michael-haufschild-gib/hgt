/-
# Böttcher tower — Tier 3: period ⟹ monodromy multiplier of order 2ⁿ

Chains the verified period formula (`period_eq`: `∮_γ dlogφ_c = 2πi·(enclosed mass)`)
to the dyadic order count (`orderOf_dyadicRoot`). When the loop encloses a depth-`n`
Cantor cylinder of equilibrium mass `2⁻ⁿ`, the monodromy multiplier `exp(∮_γ dlogφ_c)`
is `exp(2πi/2ⁿ)` — a primitive `2ⁿ`-th root of unity.

This is the order+multiplier content of the `mono` input to the disconnected case
(`algIndep_of_unbounded_monodromy`). The one remaining (analytic) piece is that
continuation around `γ` realises this multiplier as a field automorphism of the germ
field — the germ-field/deck-transformation construction.
-/
import GaloisForLFunctions.Bottcher.Period
import GaloisForLFunctions.Bottcher.DyadicMonodromy

open Complex Metric MeasureTheory

namespace Bottcher

/-- **Period ⟹ dyadic multiplier order.** If the loop `C(c,R)` is separated from
`supp μ_c` and encloses equilibrium mass exactly `2⁻ⁿ` (a depth-`n` Cantor cylinder
under Brolin's balanced measure), the monodromy multiplier `exp(∮_γ dlogφ_c)` has
order exactly `2ⁿ`. -/
theorem multiplier_orderOf_of_mass (μ : Measure ℂ) [IsFiniteMeasure μ] {c : ℂ} {R : ℝ}
    (n : ℕ) (h0 : 0 ≤ R) (hsphere : μ (sphere c R) = 0)
    (hint : Integrable (Function.uncurry fun (θ : ℝ) (ζ : ℂ) =>
        deriv (circleMap c R) θ • (circleMap c R θ - ζ)⁻¹)
      ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod μ))
    (hmass : (μ (ball c R)).toReal = (((2 ^ n : ℕ) : ℝ))⁻¹) :
    orderOf (Complex.exp (∮ z in C(c, R), ∫ ζ, (z - ζ)⁻¹ ∂μ)) = 2 ^ n := by
  rw [period_eq μ h0 hsphere hint, hmass,
      show 2 * (Real.pi : ℂ) * Complex.I * ((((2 ^ n : ℕ) : ℝ))⁻¹ : ℝ)
         = 2 * (Real.pi : ℂ) * Complex.I / (((2 ^ n : ℕ) : ℂ)) from by push_cast; ring]
  exact orderOf_dyadicRoot n

end Bottcher
