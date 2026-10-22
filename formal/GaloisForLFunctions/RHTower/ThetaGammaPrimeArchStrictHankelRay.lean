import GaloisForLFunctions.RHTower.GammaRealConnectionSpectralHankel
import GaloisForLFunctions.RHTower.PrimeArchExactReconstructionStrictHankelRayUniversalityLaw
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodSpectralMeasure

/-!
# Theta--Gamma strict Hankel ray in the prime--archimedean cone

The normalized central real-Gamma connection and the exponentially tilted higher theta-tail
measure each supply an unconditional infinite-support moment tower.  Their sum is therefore a
concrete hybrid strict Hankel ray.  This discharges the abstract strict-ray premise in the
prime--archimedean adjoining theorem and gives an exact RH classifier built from both source
sectors.
-/

namespace RHTower

noncomputable section

/-- Hybrid moment clock formed from the central real-Gamma connection and higher theta tail. -/
def thetaGammaPrimeArchStrictHankelMoment (B : ℝ) (m : ℕ) : ℝ :=
  normalizedGammaRealConnectionJet m +
    thetaCuspHigherLikelihoodSpectralMoment B m

/-- Hankel formation splits the hybrid clock into its Gamma and theta source blocks. -/
theorem momentHankelMatrix_thetaGammaPrimeArchStrictHankelMoment
    (B : ℝ) (n : ℕ) :
    HTGeometry.momentHankelMatrix
        (thetaGammaPrimeArchStrictHankelMoment B) n =
      HTGeometry.momentHankelMatrix normalizedGammaRealConnectionJet n +
        HTGeometry.momentHankelMatrix
          (thetaCuspHigherLikelihoodSpectralMoment B) n := by
  ext i j
  simp [HTGeometry.momentHankelMatrix,
    thetaGammaPrimeArchStrictHankelMoment]

/-- Every finite block of the hybrid Gamma--theta moment tower is positive definite. -/
theorem thetaGammaPrimeArchStrictHankelMoment_hankel_posDef
    {B : ℝ} (hB : 0 < B) (n : ℕ) :
    (HTGeometry.momentHankelMatrix
      (thetaGammaPrimeArchStrictHankelMoment B) n).PosDef := by
  rw [momentHankelMatrix_thetaGammaPrimeArchStrictHankelMoment]
  exact (normalizedGammaRealConnectionJet_hankel_posDef n).add
    (thetaCuspHigherLikelihoodSpectralMoment_hankel_posDef hB n)

/-- The hybrid Gamma--theta source discharges the abstract all-order strict-Hankel interface. -/
theorem thetaGammaPrimeArchStrictHankelMoment_strictHankelRay
    {B : ℝ} (hB : 0 < B) :
    PrimeArchStrictHankelRay (thetaGammaPrimeArchStrictHankelMoment B) :=
  thetaGammaPrimeArchStrictHankelMoment_hankel_posDef hB

/-- **Theta--Gamma prime--archimedean classifier.**  At every positive theta spectral
coordinate, RH is exactly closure of the physical cone after adjoining the concrete hybrid
Gamma--theta ray. -/
theorem riemannHypothesis_iff_primeArch_adjoin_thetaGammaStrictHankelRay
    {B : ℝ} (hB : 0 < B) :
    RiemannHypothesis ↔
      PrimeArchStrictHankelRayAdjoiningCone
        (thetaGammaPrimeArchStrictHankelMoment B) := by
  simpa [PrimeArchStrictHankelRayAdjoiningCone] using
    riemannHypothesis_iff_primeArch_adjoin_any_strictHankelRay
      (thetaGammaPrimeArchStrictHankelMoment B)
      (thetaGammaPrimeArchStrictHankelMoment_strictHankelRay hB)

/-- Canonical unit-coordinate specialization: no source-positivity hypothesis remains. -/
theorem riemannHypothesis_iff_primeArch_adjoin_unitThetaGammaStrictHankelRay :
    RiemannHypothesis ↔
      PrimeArchStrictHankelRayAdjoiningCone
        (thetaGammaPrimeArchStrictHankelMoment 1) :=
  riemannHypothesis_iff_primeArch_adjoin_thetaGammaStrictHankelRay zero_lt_one

end

end RHTower
