import GaloisForLFunctions.RHTower.GammaSewnPluckerGlobalMeanNuclearRoot
import GaloisForLFunctions.RHTower.XiOrderedPrimeSchattenThreshold

open ContinuousLinearMap
noncomputable section
namespace RHTower.HedenmalmThetaSource

local instance : ContinuousFunctionalCalculus ℝ
    (GammaSewnCriticalPhysicalPluckerHilbert →L[ℂ] GammaSewnCriticalPhysicalPluckerHilbert)
      IsSelfAdjoint := IsSelfAdjoint.instContinuousFunctionalCalculus

/-- Every bounded two-sided transport of the literal C1 positive root remains nuclear. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMeanPolarized_bounded_root_transport_memSchattenClass_one
    (A B : GammaSewnCriticalPhysicalPluckerHilbert →L[ℂ] GammaSewnCriticalPhysicalPluckerHilbert) :
    MemSchattenClass 1 (A ∘L
      CFC.sqrt gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator ∘L B) := by
  exact memSchattenClass_one_comp_left
    (memSchattenClass_one_comp_right
      gammaSewnCriticalPhysicalPluckerGlobalMeanPolarized_sqrt_memSchattenClass_one B) A

/-- Bounded, possibly nonlocal mixing cannot supply the exact full reciprocal-Xi singular
profile. No RH premise or truncation of multiplicity is used. -/
theorem not_gammaSewnCriticalPhysicalPluckerGlobalMeanPolarized_bounded_root_Xi_spectrum
    (A B : GammaSewnCriticalPhysicalPluckerHilbert →L[ℂ] GammaSewnCriticalPhysicalPluckerHilbert) :
    ¬ (∀ n : ℕ, approxNumber (A ∘L
      CFC.sqrt gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator ∘L B) n =
        approxNumber xiOrderedSignedPrimeOperator n) := by
  intro h
  apply xiOrderedSignedPrimeOperator_not_memSchattenClass_one
  have hsum :=
    (gammaSewnCriticalPhysicalPluckerGlobalMeanPolarized_bounded_root_transport_memSchattenClass_one
      A B).one_summable_approxNumber
  exact (hsum.congr h).congr fun _ => (Real.rpow_one _).symm

end RHTower.HedenmalmThetaSource
