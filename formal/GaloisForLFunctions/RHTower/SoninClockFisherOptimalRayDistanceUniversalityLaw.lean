import GaloisForLFunctions.RHTower.SoninLogClockFidelityFisherSectorFactorizationUniversalityLaw
import GaloisForLFunctions.RHTower.SoninLogClockRayDistanceUniversalityLaw

/-!
# Sonin clock Fisher optimal-ray-distance universality

For every bounded observation of a physical Sonin state, invariant-sector-weighted erased
logarithmic-clock quantum Fisher information is the exact mass-complement polynomial of the
distance to the closer real scattering ray.  One of the two signs `±1` attains that distance.
-/

open Complex
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- Invariant-sector-weighted erased logarithmic-clock QFI is exactly the closest-scattering-ray
distance times its homogeneous mass complement. -/
theorem soninLogClock_invariantWeight_mul_erasedQFI_eq_rayDistanceSq_mul_massComplement
    (X : SoninL2 →L[ℂ] SoninL2)
    {ψ : SoninL2} (hψnorm : ‖ψ‖ = 1)
    (hψ : GaloisForLFunctions.PhysicalState
      (soninLogFourierScattering - 1).toLinearMap ψ) :
    ‖soninLogFourierInvariantAverage (X ψ)‖ ^ (2 : ℕ) *
        HTGeometry.pureStateQuantumFisherValue (‖ψ‖ ^ (2 : ℕ))
          (‖inner ℂ ψ
            ((1 - soninLogFourierInvariantAverage) (X ψ))‖)
          (‖(1 - soninLogFourierInvariantAverage) (X ψ)‖ ^ (2 : ℕ)) =
      soninLogFourierScatteringRayDistanceSq (X ψ) *
        (‖X ψ‖ ^ (2 : ℕ) -
          soninLogFourierScatteringRayDistanceSq (X ψ) / 4) := by
  have hfisher :=
    soninLogClock_homogeneousFidelityDeficit_eq_invariantWeight_mul_erasedQFI
      X hψnorm hψ
  have hray :=
    soninLogFourierScattering_projectiveAsymmetry_eq_rayDistanceSq_mul_massComplement
      (X ψ)
  calc
    ‖soninLogFourierInvariantAverage (X ψ)‖ ^ (2 : ℕ) *
          HTGeometry.pureStateQuantumFisherValue (‖ψ‖ ^ (2 : ℕ))
            (‖inner ℂ ψ
              ((1 - soninLogFourierInvariantAverage) (X ψ))‖)
            (‖(1 - soninLogFourierInvariantAverage) (X ψ)‖ ^ (2 : ℕ)) =
        ‖X ψ‖ ^ (4 : ℕ) -
          ‖inner ℂ (X ψ) (soninLogFourierScattering (X ψ))‖ ^ (2 : ℕ) :=
      hfisher.symm
    _ = HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ)
        (X ψ) (soninLogFourierScattering (X ψ)) := by
      unfold HTGeometry.projectiveGramTangentEnergy
      rw [soninLogFourierScattering_norm]
      ring
    _ = soninLogFourierScatteringRayDistanceSq (X ψ) *
        (‖X ψ‖ ^ (2 : ℕ) -
          soninLogFourierScatteringRayDistanceSq (X ψ) / 4) := hray

/-- **Sonin clock Fisher optimal-ray-distance universality.**  One real scattering phase attains
the distance that exactly determines invariant-weighted erased clock QFI. -/
theorem exists_sign_soninLogClock_invariantWeight_mul_erasedQFI_eq_rayDistance
    (X : SoninL2 →L[ℂ] SoninL2)
    {ψ : SoninL2} (hψnorm : ‖ψ‖ = 1)
    (hψ : GaloisForLFunctions.PhysicalState
      (soninLogFourierScattering - 1).toLinearMap ψ) :
    ∃ c : ℂ, (c = 1 ∨ c = -1) ∧ ‖c‖ = 1 ∧
      ‖soninLogFourierScattering (X ψ) - c • X ψ‖ ^ (2 : ℕ) =
        soninLogFourierScatteringRayDistanceSq (X ψ) ∧
      ‖soninLogFourierInvariantAverage (X ψ)‖ ^ (2 : ℕ) *
          HTGeometry.pureStateQuantumFisherValue (‖ψ‖ ^ (2 : ℕ))
            (‖inner ℂ ψ
              ((1 - soninLogFourierInvariantAverage) (X ψ))‖)
            (‖(1 - soninLogFourierInvariantAverage) (X ψ)‖ ^ (2 : ℕ)) =
        ‖soninLogFourierScattering (X ψ) - c • X ψ‖ ^ (2 : ℕ) *
          (‖X ψ‖ ^ (2 : ℕ) -
            ‖soninLogFourierScattering (X ψ) - c • X ψ‖ ^ (2 : ℕ) / 4) := by
  obtain ⟨c, hc, hcnorm, hdistance⟩ :=
    exists_sign_soninLogFourierScatteringRayDistanceSq (X ψ)
  refine ⟨c, hc, hcnorm, hdistance, ?_⟩
  rw [hdistance]
  exact
    soninLogClock_invariantWeight_mul_erasedQFI_eq_rayDistanceSq_mul_massComplement
      X hψnorm hψ

end

end RHTower
