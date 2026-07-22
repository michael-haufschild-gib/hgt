import GaloisForLFunctions.RHTower.SoninLogClockQFIPhysicalityUniversalityLaw
import GaloisForLFunctions.RHTower.SoninLogConstraintPinchingCompression
import GaloisForLFunctions.RHTower.SoninLogClockMultiplicativeDomain

/-!
# Sonin logarithmic pinching QFI--multiplicative--compression law

Invariant-sector pinching maps every Sonin observable into the scattering commutant.
On every normalized physical state, this single pinched observable simultaneously has zero
hidden-clock quantum Fisher value, vanishing Ward values, zero complete star-Kadison defect, and
zero compressed adjoint scattering-constraint sandwich.
-/

open Complex
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- **Sonin pinching universality law.**  Static invariant-sector measurement sends every
observable to the common zero locus of the state QFI, all positive-master Ward
functionals, the operator multiplicative-domain defect, and the compressed constraint sandwich. -/
theorem soninLogPinching_zeroQFI_multiplicativeDomain_compression
    (X : SoninL2 →L[ℂ] SoninL2)
    {ψ : SoninL2} (hψnorm : ‖ψ‖ = 1)
    (hψ : GaloisForLFunctions.PhysicalState
      (soninLogFourierScattering - 1).toLinearMap ψ) :
    let Y := HTGeometry.twoOutcomePinching soninLogFourierInvariantAverage X
    HTGeometry.pureStateQuantumFisherValue (‖ψ‖ ^ 2)
        (‖inner ℂ ψ ((1 - soninLogFourierInvariantAverage) (Y ψ))‖)
        (‖(1 - soninLogFourierInvariantAverage) (Y ψ)‖ ^ 2) = 0 ∧
      (∀ A : SoninL2 →L[ℂ] SoninL2,
        inner ℂ (Y ψ)
          (HTGeometry.quantumMasterConstraint (soninLogFourierScattering - 1)
            (A (Y ψ))) = 0) ∧
      soninLogFourierObservableTwirlStarKadisonDefect Y = 0 ∧
      soninLogFourierInvariantAverage *
          (Y.adjoint * (soninLogFourierScattering - 1) * Y) *
        soninLogFourierInvariantAverage = 0 := by
  dsimp only
  let Y := HTGeometry.twoOutcomePinching soninLogFourierInvariantAverage X
  have hYeq : Y = soninLogFourierObservableTwirl X := by
    simpa only [Y, soninLogFourierInvariantAverage,
      soninLogFourierObservableTwirl] using
      HTGeometry.twoOutcomePinching_finiteInvolutiveGaugeAverage_eq_observableTwirl
        soninLogFourierScattering X soninLogFourierScattering_sq_eq_one
  have hYcomm : soninLogFourierScattering * Y =
      Y * soninLogFourierScattering := by
    rw [hYeq]
    simpa only [soninLogFourierObservableTwirl] using
      HTGeometry.finiteCyclicObservableTwirl_commutes
        soninLogFourierScattering X 2 soninLogFourierScattering_sq_eq_one
  have hYphysical : GaloisForLFunctions.PhysicalState
      (soninLogFourierScattering - 1).toLinearMap (Y ψ) := by
    rw [GaloisForLFunctions.PhysicalState] at hψ ⊢
    have hfixed : soninLogFourierScattering ψ = ψ := by
      apply sub_eq_zero.mp
      simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] using hψ
    change soninLogFourierScattering (Y ψ) - Y ψ = 0
    rw [← ContinuousLinearMap.mul_apply, hYcomm,
      ContinuousLinearMap.mul_apply, hfixed, sub_self]
  have hQFI : HTGeometry.pureStateQuantumFisherValue (‖ψ‖ ^ 2)
      (‖inner ℂ ψ ((1 - soninLogFourierInvariantAverage) (Y ψ))‖)
      (‖(1 - soninLogFourierInvariantAverage) (Y ψ)‖ ^ 2) = 0 :=
    (soninLogClock_erasedPureStateQuantumFisherValue_eq_zero_iff_observedPhysical
      Y hψnorm hψ).mpr hYphysical
  refine ⟨hQFI, ?_, ?_, ?_⟩
  · intro A
    exact soninLogClock_zeroQFI_WardValue_eq_zero
      Y A hψnorm hψ hQFI
  · exact (soninLogFourierObservableTwirlStarKadisonDefect_eq_zero_iff_commutes Y).mpr
      hYcomm
  · simpa only [Y] using
      soninLogConstraintPinchedAdjointSandwich_compression_eq_zero X

end

end RHTower
