import GaloisForLFunctions.HTGeometry.IntermediateFieldTensorCoboundaryDescent
import GaloisForLFunctions.HTGeometry.MeromorphicEllipticLinearDisjoint

/-!
# Product specialization for the paired elliptic compositum

For rationally independent periods `1`, `sigma`, and `tau`, a translation coboundary in the
paired elliptic compositum descends to the elliptic factor on which the translation acts.  The
other factor is fixed pointwise and is removed by finite-right-factor specialization.

These theorems are the concrete order-one product-descent gate used by the elliptic-gamma
Ostrowski argument.  The whole elliptic coefficient field need not be finite type.
-/

open Filter Set

namespace GaloisForLFunctions

open Bottcher

noncomputable section

local instance meromorphicEllipticProductSpecializationDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance meromorphicEllipticProductSpecializationComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance meromorphicEllipticProductSpecializationComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  ((algebraMap (analyticSubring Set.univ) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

/-- A `sigma`-translation coboundary in `E_sigma E_tau` whose right-hand side belongs to
`E_tau` already has a certificate in `E_tau`. -/
theorem exists_ellipticTau_coboundary_of_compositum_sigma
    (sigma tau : ℂ)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (a : ellipticMeroField tau) {g : meroField (Set.univ : Set ℂ)}
    (hg : g ∈ meromorphicEllipticCompositum sigma tau)
    (hcoboundary : addTranslationMeroAlgEquiv sigma g - g =
      (a : meroField Set.univ)) :
    ∃ u : ellipticMeroField tau,
      ellipticMeroFieldTranslationAlgEquiv tau sigma u - u = a := by
  have hdisjoint :
      (ellipticMeroField tau).LinearDisjoint (ellipticMeroField sigma) :=
    (ellipticMeroFields_linearDisjoint sigma tau hindependent).symm
  have hg' : g ∈ ellipticMeroField tau ⊔ ellipticMeroField sigma := by
    simpa [meromorphicEllipticCompositum, sup_comm] using hg
  have hleft : ∀ x : ellipticMeroField tau,
      addTranslationMeroAlgEquiv sigma (x : meroField Set.univ) =
        ((ellipticMeroFieldTranslationAlgEquiv tau sigma x :
          ellipticMeroField tau) : meroField Set.univ) := fun x =>
    (ellipticMeroFieldTranslationAlgEquiv_apply tau sigma x).symm
  have hright : ∀ y : ellipticMeroField sigma,
      addTranslationMeroAlgEquiv sigma (y : meroField Set.univ) =
        (y : meroField Set.univ) := by
    intro y
    change addTranslationMeroEquiv sigma (y : meroField Set.univ) = y
    exact ((mem_ellipticMeroField_iff sigma _).mp y.2).2
  exact exists_left_coboundary_of_mem_intermediateField_sup
    ℂ (meroField Set.univ)
    (ellipticMeroField tau) (ellipticMeroField sigma)
    hdisjoint (addTranslationMeroAlgEquiv sigma)
    (ellipticMeroFieldTranslationAlgEquiv tau sigma)
    hleft hright a hg' hcoboundary

/-- A `tau`-translation coboundary in `E_sigma E_tau` whose right-hand side belongs to
`E_sigma` already has a certificate in `E_sigma`. -/
theorem exists_ellipticSigma_coboundary_of_compositum_tau
    (sigma tau : ℂ)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (a : ellipticMeroField sigma) {g : meroField (Set.univ : Set ℂ)}
    (hg : g ∈ meromorphicEllipticCompositum sigma tau)
    (hcoboundary : addTranslationMeroAlgEquiv tau g - g =
      (a : meroField Set.univ)) :
    ∃ u : ellipticMeroField sigma,
      ellipticMeroFieldTranslationAlgEquiv sigma tau u - u = a := by
  have hdisjoint := ellipticMeroFields_linearDisjoint sigma tau hindependent
  have hg' : g ∈ ellipticMeroField sigma ⊔ ellipticMeroField tau := by
    simpa [meromorphicEllipticCompositum] using hg
  have hleft : ∀ x : ellipticMeroField sigma,
      addTranslationMeroAlgEquiv tau (x : meroField Set.univ) =
        ((ellipticMeroFieldTranslationAlgEquiv sigma tau x :
          ellipticMeroField sigma) : meroField Set.univ) := fun x =>
    (ellipticMeroFieldTranslationAlgEquiv_apply sigma tau x).symm
  have hright : ∀ y : ellipticMeroField tau,
      addTranslationMeroAlgEquiv tau (y : meroField Set.univ) =
        (y : meroField Set.univ) := by
    intro y
    change addTranslationMeroEquiv tau (y : meroField Set.univ) = y
    exact ((mem_ellipticMeroField_iff tau _).mp y.2).2
  exact exists_left_coboundary_of_mem_intermediateField_sup
    ℂ (meroField Set.univ)
    (ellipticMeroField sigma) (ellipticMeroField tau)
    hdisjoint (addTranslationMeroAlgEquiv tau)
    (ellipticMeroFieldTranslationAlgEquiv sigma tau)
    hleft hright a hg' hcoboundary

end

end GaloisForLFunctions
