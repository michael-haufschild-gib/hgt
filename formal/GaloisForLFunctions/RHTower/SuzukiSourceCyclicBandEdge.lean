import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The band-edge density and the resolvent mass

The capacity gap bounds the odds transform at the global spectral edge: from `ρ r ≤ C(1-ρ²)` and
`ρ ≤ 1` one gets `ρ²/(1-ρ²) ≤ C/r`, which is the density bound that converts the surviving
source-cyclic gain into a mass floor.

The high resolvent mass obeys the matching elementary bound: a resolvent below the ridge mass has
inverse quadratic form at most the squared norm divided by that mass.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- **`(469)`: the capacity gap bounds the odds transform at the spectral edge.** -/
theorem odds_le_capacity {ρ C r : ℝ} (hr : 0 < r) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hgap : ρ * r ≤ C * (1 - ρ ^ (2 : ℕ))) : ρ ^ (2 : ℕ) / (1 - ρ ^ (2 : ℕ)) ≤ C / r := by
  have hden : (0 : ℝ) < 1 - ρ ^ (2 : ℕ) := by nlinarith
  have hsq : ρ ^ (2 : ℕ) ≤ ρ := by nlinarith
  rw [div_le_div_iff₀ hden hr]
  nlinarith [hgap, mul_le_mul_of_nonneg_right hsq hr.le]

/-- **`(462)`: a resolvent above the ridge mass has inverse quadratic form below the squared norm
over that mass.** -/
theorem resolvent_mass_le {τ un r : ℝ} (hr : 0 < r) (hτ : r * τ ≤ un) : τ ≤ un / r := by
  rw [le_div_iff₀ hr]
  linarith

end GaloisForLFunctions.RHTower
