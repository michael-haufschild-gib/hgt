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
    (X : SoninL2 →L[ℂ] SoninL2) (hX : IsSelfAdjoint X)
    {ψ : SoninL2} (hψnorm : ‖ψ‖ = 1)
    (hψ : GaloisForLFunctions.PhysicalState
      (soninLogFourierScattering - 1).toLinearMap ψ) :
    HTGeometry.pureStateQuantumFisherValue (‖ψ‖ ^ 2)
        (‖inner ℂ ψ ((1 - soninLogFourierInvariantAverage) (X ψ))‖)
        (‖(1 - soninLogFourierInvariantAverage) (X ψ)‖ ^ 2) = 0 ↔
      GaloisForLFunctions.PhysicalState
        (soninLogFourierScattering - 1).toLinearMap (X ψ) := by
  rw [soninLogClock_erasedPureStateQuantumFisherValue_eq_commutatorNormSq
    X hX hψnorm hψ]
  rw [sq_eq_zero_iff, norm_eq_zero]
  rw [GaloisForLFunctions.PhysicalState] at hψ ⊢
  have hfixed : soninLogFourierScattering ψ = ψ := by
    apply sub_eq_zero.mp
    simpa using hψ
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, hfixed]
  constructor <;> intro h
  · exact sub_eq_zero.mpr (sub_eq_zero.mp h).symm
  · exact sub_eq_zero.mpr (sub_eq_zero.mp h).symm

/-- Zero hidden-clock QFI supplies every positive-master Ward identity for the observed Sonin
state. -/
theorem soninLogClock_zeroQFI_WardValue_eq_zero
    (X A : SoninL2 →L[ℂ] SoninL2) (hX : IsSelfAdjoint X)
    {ψ : SoninL2} (hψnorm : ‖ψ‖ = 1)
    (hψ : GaloisForLFunctions.PhysicalState
      (soninLogFourierScattering - 1).toLinearMap ψ)
    (hzero : HTGeometry.pureStateQuantumFisherValue (‖ψ‖ ^ 2)
        (‖inner ℂ ψ ((1 - soninLogFourierInvariantAverage) (X ψ))‖)
        (‖(1 - soninLogFourierInvariantAverage) (X ψ)‖ ^ 2) = 0) :
    inner ℂ (X ψ)
      (HTGeometry.quantumMasterConstraint (soninLogFourierScattering - 1)
        (A (X ψ))) = 0 := by
  apply HTGeometry.quantumMasterConstraint_WardValue_eq_zero
    (soninLogFourierScattering - 1) A
  exact (soninLogClock_erasedPureStateQuantumFisherValue_eq_zero_iff_observedPhysical
    X hX hψnorm hψ).mp hzero

end

end RHTower
