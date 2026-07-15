import GaloisForLFunctions.HTGeometry.FiniteInvolutiveClockFidelityAsymmetry
import GaloisForLFunctions.RHTower.SoninLogCoordinateScattering

/-!
# Fidelity asymmetry of logarithmic Sonin scattering

The general involutive-clock fidelity identity evaluates the asymmetry resource of a pure Sonin
state exactly in terms of its invariant and anti-invariant logarithmic-scattering weights.  These
weights are static constraint-sector values, not probabilities along a temporal evolution.
-/

open Complex
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- The Sonin scattering overlap is the physical-sector weight minus the complementary-sector
weight, hence is automatically real. -/
theorem inner_soninLogFourierScattering_eq_sectorNormSq_sub (ψ : SoninL2) :
    inner ℂ ψ (soninLogFourierScattering ψ) =
      (‖soninLogFourierInvariantAverage ψ‖ ^ 2 -
        ‖(1 - soninLogFourierInvariantAverage) ψ‖ ^ 2 : ℝ) := by
  simpa only [soninLogFourierInvariantAverage] using
    HTGeometry.inner_finiteInvolutiveClockTransform_eq_sectorNormSq_sub
      soninLogFourierScattering soninLogFourierScattering_adjoint_mul_self
      soninLogFourierScattering_sq_eq_one ψ

/-- **Sonin fidelity-sector identity.**  For a normalized state, squared infidelity with its
logarithmic Fourier transform is exactly four times the product of its physical and nonphysical
scattering-sector weights. -/
theorem soninLogFourierScattering_pureStateFidelityDeficit_eq_four_mul_sectorWeights
    {ψ : SoninL2} (hψnorm : ‖ψ‖ = 1) :
    1 - ‖inner ℂ ψ (soninLogFourierScattering ψ)‖ ^ 2 =
      4 * ‖soninLogFourierInvariantAverage ψ‖ ^ 2 *
        ‖(1 - soninLogFourierInvariantAverage) ψ‖ ^ 2 := by
  simpa only [soninLogFourierInvariantAverage] using
    HTGeometry.finiteInvolutiveClock_pureStateFidelityDeficit_eq_four_mul_sectorWeights
      soninLogFourierScattering soninLogFourierScattering_adjoint_mul_self
      soninLogFourierScattering_sq_eq_one hψnorm

/-- The same sector product is the projective Gram distance from a normalized state to its
scattering transform. -/
theorem soninLogFourierScattering_projectiveAsymmetry_eq_four_mul_sectorWeights
    {ψ : SoninL2} (hψnorm : ‖ψ‖ = 1) :
    HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ) ψ
        (soninLogFourierScattering ψ) =
      4 * ‖soninLogFourierInvariantAverage ψ‖ ^ 2 *
        ‖(1 - soninLogFourierInvariantAverage) ψ‖ ^ 2 := by
  simpa only [soninLogFourierInvariantAverage] using
    HTGeometry.finiteInvolutiveClock_projectiveAsymmetry_eq_four_mul_sectorWeights
      soninLogFourierScattering soninLogFourierScattering_adjoint_mul_self
      soninLogFourierScattering_sq_eq_one hψnorm

end

end RHTower
