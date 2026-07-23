import GaloisForLFunctions.RHTower.GammaQuarterRefinedPrimeArchHankelConeUniversalityLaw
import GaloisForLFunctions.RHTower.ThetaGammaPrimeArchStrictHankelRay

/-!
# Theta--black-hole quarter-completion strict-Hankel universality law

The Gamma--theta strict ray and the quarter-lattice Gamma complement share the central
real-Gamma connection.  Completing that shared summand rewrites the hybrid source exactly as a
higher theta tail plus the four-dilated normalized black-hole clock.  The completed source remains
strict Hankel at every finite depth and therefore gives a concrete prime--archimedean RH
classifier.
-/

namespace RHTower

noncomputable section

/-- The Gamma--theta clock completed by the three remaining quarter-lattice Gamma sectors. -/
def thetaBlackHoleQuarterCompletedMoment (B : ℝ) (m : ℕ) : ℝ :=
  thetaGammaPrimeArchStrictHankelMoment B m +
    gammaQuarterLatticeComplementMoment m

/-- The completed source is exactly the theta tail plus the four-dilated normalized black-hole
clock, independently of the black-hole scale convention. -/
theorem thetaBlackHoleQuarterCompletedMoment_eq
    (scaleLog : ℂ) (B : ℝ) (m : ℕ) :
    thetaBlackHoleQuarterCompletedMoment B m =
      (4 : ℝ) ^ (m + 2) *
          HTGeometry.normalizedBlackHoleFarZoneJet scaleLog m +
        thetaCuspHigherLikelihoodSpectralMoment B m := by
  rw [thetaBlackHoleQuarterCompletedMoment,
    thetaGammaPrimeArchStrictHankelMoment]
  calc
    (normalizedGammaRealConnectionJet m +
          thetaCuspHigherLikelihoodSpectralMoment B m) +
        gammaQuarterLatticeComplementMoment m =
      (normalizedGammaRealConnectionJet m +
          gammaQuarterLatticeComplementMoment m) +
        thetaCuspHigherLikelihoodSpectralMoment B m := by ring
    _ = (4 : ℝ) ^ (m + 2) *
          HTGeometry.normalizedBlackHoleFarZoneJet scaleLog m +
        thetaCuspHigherLikelihoodSpectralMoment B m := by
      rw [gammaRealConnection_add_quarterComplement_eq_dilatedBlackHoleClock]

/-- Hankel formation splits the completed clock into the original Gamma--theta ray and its
quarter-lattice complement. -/
theorem momentHankelMatrix_thetaBlackHoleQuarterCompletedMoment
    (B : ℝ) (n : ℕ) :
    HTGeometry.momentHankelMatrix
        (thetaBlackHoleQuarterCompletedMoment B) n =
      HTGeometry.momentHankelMatrix
          (thetaGammaPrimeArchStrictHankelMoment B) n +
        HTGeometry.momentHankelMatrix
          gammaQuarterLatticeComplementMoment n := by
  ext i j
  simp [HTGeometry.momentHankelMatrix,
    thetaBlackHoleQuarterCompletedMoment]

/-- Every finite Hankel block of the theta/black-hole quarter-completed clock is positive
definite. -/
theorem thetaBlackHoleQuarterCompletedMoment_hankel_posDef
    {B : ℝ} (hB : 0 < B) (n : ℕ) :
    (HTGeometry.momentHankelMatrix
      (thetaBlackHoleQuarterCompletedMoment B) n).PosDef := by
  rw [momentHankelMatrix_thetaBlackHoleQuarterCompletedMoment]
  exact (thetaGammaPrimeArchStrictHankelMoment_hankel_posDef hB n).add
    (gammaQuarterLatticeComplementMoment_hankel_posDef n)

/-- The completed hybrid source is an unconditional all-order strict Hankel ray at every
positive theta coordinate. -/
theorem thetaBlackHoleQuarterCompletedMoment_strictHankelRay
    {B : ℝ} (hB : 0 < B) :
    PrimeArchStrictHankelRay (thetaBlackHoleQuarterCompletedMoment B) :=
  thetaBlackHoleQuarterCompletedMoment_hankel_posDef hB

/-- RH is exactly closure of the physical cone after adjoining the concrete completed
theta/black-hole ray. -/
theorem riemannHypothesis_iff_primeArch_adjoin_thetaBlackHoleQuarterCompletedRay
    {B : ℝ} (hB : 0 < B) :
    RiemannHypothesis ↔
      PrimeArchStrictHankelRayAdjoiningCone
        (thetaBlackHoleQuarterCompletedMoment B) := by
  simpa [PrimeArchStrictHankelRayAdjoiningCone] using
    riemannHypothesis_iff_primeArch_adjoin_any_strictHankelRay
      (thetaBlackHoleQuarterCompletedMoment B)
      (thetaBlackHoleQuarterCompletedMoment_strictHankelRay hB)

/-- **Theta--black-hole quarter-completion strict-Hankel universality law.**  One concrete
completed source has an exact central-Gamma/quarter-sector and black-hole/theta presentation,
strict Hankel positivity at every depth, and an exact RH adjoining-cone classifier. -/
theorem thetaBlackHoleQuarterCompletion_strictHankelUniversality
    {B : ℝ} (hB : 0 < B) :
    (∀ (scaleLog : ℂ) (m : ℕ),
      thetaBlackHoleQuarterCompletedMoment B m =
        (4 : ℝ) ^ (m + 2) *
            HTGeometry.normalizedBlackHoleFarZoneJet scaleLog m +
          thetaCuspHigherLikelihoodSpectralMoment B m) ∧
    (∀ n : ℕ,
      (HTGeometry.momentHankelMatrix
        (thetaBlackHoleQuarterCompletedMoment B) n).PosDef) ∧
    (RiemannHypothesis ↔
      PrimeArchStrictHankelRayAdjoiningCone
        (thetaBlackHoleQuarterCompletedMoment B)) := by
  exact ⟨fun scaleLog m =>
      thetaBlackHoleQuarterCompletedMoment_eq scaleLog B m,
    thetaBlackHoleQuarterCompletedMoment_hankel_posDef hB,
    riemannHypothesis_iff_primeArch_adjoin_thetaBlackHoleQuarterCompletedRay hB⟩

end

end RHTower
