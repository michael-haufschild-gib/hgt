import GaloisForLFunctions.RHTower.ConstrainedProlateSignedTrial
import GaloisForLFunctions.RHTower.HermiteTruncationTailAsymptotic

/-!
# Sharp Hermite envelope for the true signed prolate spectrum

The exact normalized Hermite tail laws aggregate over the finite trial space and then pass through
the signed Courant--Fischer estimate.  This gives the true signed prolate leakage its sharp
step-four Hermite trial exponent `exp (-2*pi*a^2)` with no hypothesis and no aperture-dependent
constant.

This is a trial-envelope theorem, not the stronger Fuchs asymptotic: the latter has exponent
`exp (-4*pi*a^2)` and still requires fixed-mode identification through the prolate differential
equation.
-/

open Filter Topology
open scoped Real

noncomputable section

namespace RHTower

/-- Explicit finite-depth constant in the sharp Hermite trial envelope. -/
def hermiteTrialTailEnvelopeConstant (n : ℕ) : ℝ :=
  ∑ k : Fin (n + 1), 5 * (hermiteStepFourTailConstant (k : ℕ) + 1)

theorem hermiteTrialTailEnvelopeConstant_pos (n : ℕ) :
    0 < hermiteTrialTailEnvelopeConstant n := by
  rw [hermiteTrialTailEnvelopeConstant]
  apply Finset.sum_pos
  · intro k _
    have := hermiteStepFourTailConstant_pos (k : ℕ)
    positivity
  · exact Finset.univ_nonempty

/-- Sharp fixed-depth Hermite envelope for the true unsigned leakage values. -/
theorem eventually_evenProlateLeakageValue_le_hermiteTailScale (n : ℕ) :
    ∀ᶠ a : ℝ in atTop,
      evenProlateLeakageValue a n ≤
        hermiteTrialTailEnvelopeConstant n * hermiteStepFourTailScale n a := by
  filter_upwards [eventually_hermiteTrialDefect_le_tailScale n] with a ha
  exact (evenProlateLeakageValue_le_hermite_tail_sq a n).trans (by
    simpa [hermiteTrialTailEnvelopeConstant] using ha)

/-- Sharp fixed-depth Hermite envelope for the leakage of the true signed prolate values. -/
theorem eventually_one_sub_evenProlateSignedValue_sq_le_hermiteTailScale (n : ℕ) :
    ∀ᶠ a : ℝ in atTop,
      1 - evenProlateSignedValue a n ^ 2 ≤
        hermiteTrialTailEnvelopeConstant n * hermiteStepFourTailScale n a := by
  filter_upwards [eventually_hermiteTrialDefect_le_tailScale n,
    eventually_gt_atTop (0 : ℝ)] with a htail ha
  exact (one_sub_evenProlateSignedValue_sq_le_hermite a ha n).trans (by
    simpa [hermiteTrialTailEnvelopeConstant] using htail)

/-- Positive-index specialization of the signed leakage envelope, exposing the exact
polynomial--Gaussian rate. -/
theorem eventually_one_sub_evenProlateSignedValue_sq_le_hermiteTailScale_of_pos
    (n : ℕ) (hn : 0 < n) :
    ∀ᶠ a : ℝ in atTop,
      1 - evenProlateSignedValue a n ^ 2 ≤
        hermiteTrialTailEnvelopeConstant n *
          (a ^ (8 * n - 1) * Real.exp (-(2 * Real.pi * a ^ 2))) := by
  simpa [hermiteStepFourTailScale, ne_of_gt hn] using
    eventually_one_sub_evenProlateSignedValue_sq_le_hermiteTailScale n

/-- Ground-index specialization of the signed leakage envelope. -/
theorem eventually_one_sub_evenProlateSignedValue_zero_sq_le_hermiteTailScale :
    ∀ᶠ a : ℝ in atTop,
      1 - evenProlateSignedValue a 0 ^ 2 ≤
        hermiteTrialTailEnvelopeConstant 0 *
          (a⁻¹ * Real.exp (-(2 * Real.pi * a ^ 2))) := by
  simpa [hermiteStepFourTailScale] using
    eventually_one_sub_evenProlateSignedValue_sq_le_hermiteTailScale 0

end RHTower

end
