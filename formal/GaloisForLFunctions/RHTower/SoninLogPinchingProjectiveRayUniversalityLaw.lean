import GaloisForLFunctions.RHTower.SoninLogPinchingQFIMultiplicativeCompressionLaw
import GaloisForLFunctions.RHTower.SoninLogClockRayDistanceUniversalityLaw

/-!
# Sonin logarithmic pinching projective-ray universality

Invariant-sector pinching lands not only in the common QFI/Ward/multiplicative/compression zero
locus, but also exactly on the positive Sonin scattering ray. Its signed-ray distance and
projective scattering asymmetry therefore vanish on the same observed state.
-/

open Complex
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- **Sonin pinching projective-ray universality law.**  Every pinched observable sends a
normalized physical state into one sevenfold static locus: QFI, all Ward values, star-Kadison
defect, compressed constraint, signed-ray distance, and projective asymmetry all vanish, while the
observed vector remains physical. -/
theorem soninLogPinching_projectiveRayUniversality
    (X : SoninL2 →L[ℂ] SoninL2)
    {ψ : SoninL2} (hψnorm : ‖ψ‖ = 1)
    (hψ : GaloisForLFunctions.PhysicalState
      (soninLogFourierScattering - 1).toLinearMap ψ) :
    let Y := HTGeometry.twoOutcomePinching soninLogFourierInvariantAverage X
    (HTGeometry.pureStateQuantumFisherValue (‖ψ‖ ^ 2)
          (‖inner ℂ ψ ((1 - soninLogFourierInvariantAverage) (Y ψ))‖)
          (‖(1 - soninLogFourierInvariantAverage) (Y ψ)‖ ^ 2) = 0 ∧
        (∀ A : SoninL2 →L[ℂ] SoninL2,
          inner ℂ (Y ψ)
            (HTGeometry.quantumMasterConstraint (soninLogFourierScattering - 1)
              (A (Y ψ))) = 0) ∧
        soninLogFourierObservableTwirlStarKadisonDefect Y = 0 ∧
        soninLogFourierInvariantAverage *
            (Y.adjoint * (soninLogFourierScattering - 1) * Y) *
          soninLogFourierInvariantAverage = 0) ∧
      GaloisForLFunctions.PhysicalState
        (soninLogFourierScattering - 1).toLinearMap (Y ψ) ∧
      soninLogFourierScatteringRayDistanceSq (Y ψ) = 0 ∧
      HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ) (Y ψ)
        (soninLogFourierScattering (Y ψ)) = 0 := by
  dsimp only
  let Y := HTGeometry.twoOutcomePinching soninLogFourierInvariantAverage X
  have hbase :
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
    simpa only [Y] using
      soninLogPinching_zeroQFI_multiplicativeDomain_compression X hψnorm hψ
  have hphysical : GaloisForLFunctions.PhysicalState
      (soninLogFourierScattering - 1).toLinearMap (Y ψ) :=
    (soninLogClock_erasedPureStateQuantumFisherValue_eq_zero_iff_observedPhysical
      Y hψnorm hψ).1 hbase.1
  have hfixed : soninLogFourierScattering (Y ψ) = Y ψ := by
    rw [GaloisForLFunctions.PhysicalState] at hphysical
    apply sub_eq_zero.mp
    simpa only [_root_.sub_apply, one_apply_eq_self] using hphysical
  have havg : soninLogFourierInvariantAverage (Y ψ) = Y ψ := by
    rw [soninLogFourierInvariantAverage_apply, hfixed]
    module
  have hcomplement : (1 - soninLogFourierInvariantAverage) (Y ψ) = 0 := by
    simp only [_root_.sub_apply, one_apply_eq_self, havg, sub_self]
  have hray : soninLogFourierScatteringRayDistanceSq (Y ψ) = 0 := by
    simp [soninLogFourierScatteringRayDistanceSq, havg, hcomplement]
  have hprojective :
      HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ) (Y ψ)
          (soninLogFourierScattering (Y ψ)) = 0 := by
    rw [soninLogFourierScattering_projectiveAsymmetry_eq_rayDistanceSq_mul_massComplement,
      hray]
    simp
  exact ⟨hbase, hphysical, hray, hprojective⟩

end

end RHTower
