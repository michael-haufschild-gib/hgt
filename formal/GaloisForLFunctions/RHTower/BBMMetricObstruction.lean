import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# The Bender--Brody--Muller pullback metric has no Mellin eigenvectors

In the proposed BBM metric, the difference operator sends the formal Hurwitz
eigenstate at `z` to the Mellin monomial `x ^ (-z)`.  Its squared metric density
is therefore `x ^ (-2 * Re z)` on the positive half-line.

The two ends impose incompatible conditions: local integrability at zero
requires `Re z < 1/2`, while integrability at infinity requires `Re z > 1/2`.
Consequently no formal BBM Hurwitz eigenstate is a vector in the Hilbert space
defined by this pullback metric.  This is a scalar integrability obstruction;
it does not rule out a different two-ended rigging or operator domain.
-/

noncomputable section

namespace RHTower

open Set MeasureTheory

/-- Squared metric density of the BBM Hurwitz eigenstate after the proposed
metric map sends it to the Mellin monomial `x ^ (-z)`. -/
def bbmMellinMetricDensity (z : ℂ) (x : ℝ) : ℝ := x ^ (-2 * z.re)

/-- The BBM metric density is integrable near the origin exactly to the left
of the critical line. -/
theorem integrableOn_bbmMellinMetricDensity_near_zero_iff (z : ℂ) :
    IntegrableOn (bbmMellinMetricDensity z) (Ioo 0 1) ↔ z.re < 1 / 2 := by
  change IntegrableOn (fun x : ℝ ↦ x ^ (-2 * z.re)) (Ioo 0 1) ↔ z.re < 1 / 2
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one]
  constructor <;> intro h <;> linarith

/-- The BBM metric density is integrable at infinity exactly to the right of
the critical line. -/
theorem integrableOn_bbmMellinMetricDensity_at_infinity_iff (z : ℂ) :
    IntegrableOn (bbmMellinMetricDensity z) (Ioi 1) ↔ 1 / 2 < z.re := by
  change IntegrableOn (fun x : ℝ ↦ x ^ (-2 * z.re)) (Ioi 1) ↔ 1 / 2 < z.re
  rw [integrableOn_Ioi_rpow_iff zero_lt_one]
  constructor <;> intro h <;> linarith

/-- No BBM Hurwitz eigenstate has finite norm in the proposed pullback metric:
the two Mellin ends impose the incompatible inequalities `Re z < 1/2` and
`Re z > 1/2`. -/
theorem not_integrableOn_bbmMellinMetricDensity (z : ℂ) :
    ¬ IntegrableOn (bbmMellinMetricDensity z) (Ioi 0) := by
  change ¬ IntegrableOn (fun x : ℝ ↦ x ^ (-2 * z.re)) (Ioi 0)
  exact not_integrableOn_Ioi_rpow (-2 * z.re)

end RHTower
