import GaloisForLFunctions.RHTower.SoninLogClockQuantumFisher
import GaloisForLFunctions.HTGeometry.FiniteConstraintGroupAverage

open Complex
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-!
# Sonin logarithmic-clock QFI physicality law

On a physical Sonin state, the hidden logarithmic-clock quantum Fisher value vanishes exactly
when the observed state remains physical.  Thus the scalar QFI zero condition is a complete
state-dependent constraint test and automatically supplies all positive-master Ward values.
-/

/-- **Sonin QFI physicality law.**  Hidden logarithmic-clock QFI vanishes exactly when the
observable preserves the physical Sonin constraint on the chosen state. -/
theorem soninLogClock_erasedPureStateQuantumFisherValue_eq_zero_iff_observedPhysical
    (X : SoninL2 →L[ℂ] SoninL2)
    {ψ : SoninL2} (hψnorm : ‖ψ‖ = 1)
    (hψ : GaloisForLFunctions.PhysicalState
      (soninLogFourierScattering - 1).toLinearMap ψ) :
    HTGeometry.pureStateQuantumFisherValue (‖ψ‖ ^ (2 : ℕ))
        (‖inner ℂ ψ ((1 - soninLogFourierInvariantAverage) (X ψ))‖)
        (‖(1 - soninLogFourierInvariantAverage) (X ψ)‖ ^ (2 : ℕ)) = 0 ↔
      GaloisForLFunctions.PhysicalState
        (soninLogFourierScattering - 1).toLinearMap (X ψ) := by
  rw [GaloisForLFunctions.PhysicalState] at hψ
  have hfixed : soninLogFourierScattering ψ = ψ := by
    apply sub_eq_zero.mp
    simpa using hψ
  simpa only [soninLogFourierInvariantAverage] using
    HTGeometry.finiteClock_erasedPureStateQuantumFisherValue_eq_zero_iff_physical
      soninLogFourierScattering X 2 two_ne_zero
      soninLogFourierScattering_adjoint_mul_self
      soninLogFourierScattering_sq_eq_one hψnorm hfixed

/-- Zero hidden-clock QFI supplies every positive-master Ward identity for the observed Sonin
state. -/
theorem soninLogClock_zeroQFI_WardValue_eq_zero
    (X A : SoninL2 →L[ℂ] SoninL2)
    {ψ : SoninL2} (hψnorm : ‖ψ‖ = 1)
    (hψ : GaloisForLFunctions.PhysicalState
      (soninLogFourierScattering - 1).toLinearMap ψ)
    (hzero : HTGeometry.pureStateQuantumFisherValue (‖ψ‖ ^ (2 : ℕ))
        (‖inner ℂ ψ ((1 - soninLogFourierInvariantAverage) (X ψ))‖)
        (‖(1 - soninLogFourierInvariantAverage) (X ψ)‖ ^ (2 : ℕ)) = 0) :
    inner ℂ (X ψ)
      (HTGeometry.quantumMasterConstraint (soninLogFourierScattering - 1)
        (A (X ψ))) = 0 := by
  rw [GaloisForLFunctions.PhysicalState] at hψ
  have hfixed : soninLogFourierScattering ψ = ψ := by
    apply sub_eq_zero.mp
    simpa using hψ
  apply HTGeometry.finiteClock_zeroQFI_WardValue_eq_zero
    soninLogFourierScattering X A 2 two_ne_zero
    soninLogFourierScattering_adjoint_mul_self
    soninLogFourierScattering_sq_eq_one hψnorm hfixed
  simpa only [soninLogFourierInvariantAverage] using hzero

end

end RHTower
