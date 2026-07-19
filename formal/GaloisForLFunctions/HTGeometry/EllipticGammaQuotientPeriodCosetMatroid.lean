import GaloisForLFunctions.HTGeometry.CoordinatewiseDifferentialFamilyMatroid
import GaloisForLFunctions.HTGeometry.EllipticGammaPeriodCosetMatroid

/-!
# Period-coset matroid of elliptic-gamma shift quotients

The additive external defect is the algebraic logarithmic derivative of the corresponding
multiplicative elliptic-gamma shift quotient.  Coordinatewise logarithmic derivatives preserve
the entire represented differential matroid, so the exact pointed period-coset partition law
transfers without a finiteness hypothesis.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher
open HTGeometry

noncomputable section

local instance ellipticGammaQuotientPeriodCosetDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance ellipticGammaQuotientPeriodCosetComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance ellipticGammaQuotientPeriodCosetComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  meromorphicEllipticCompositumComplexAlgebraMero

local instance ellipticGammaQuotientPeriodCosetAmbientDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance ellipticGammaQuotientPeriodCosetMeroCharZero :
    CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap ℂ (meroField Set.univ)).injective

local instance ellipticGammaQuotientPeriodCosetRestrictedDifferential
    (sigma tau : ℂ) :
    Differential (meromorphicEllipticCompositum sigma tau) :=
  meromorphicEllipticCompositumDifferential sigma tau

local instance ellipticGammaQuotientPeriodCosetDifferentialAlgebra
    (sigma tau : ℂ) :
    DifferentialAlgebra (meromorphicEllipticCompositum sigma tau)
      (meroField Set.univ) :=
  ⟨fun x ↦ derivationClosedDifferential_apply
    (meromorphicEllipticCompositum sigma tau)
    (meromorphicEllipticCompositum_derivationClosed sigma tau) x⟩

/-- The genuine multiplicative shift quotient `Gamma(z+h)/Gamma(z)` in the global meromorphic
field. -/
def ellipticGammaExternalQuotientMero
    (h sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    meroField Set.univ :=
  addTranslationMeroEquiv h (ellipticGammaMero sigma tau hsigma htau) /
    ellipticGammaMero sigma tau hsigma htau

/-- Translation commutes with the algebraic logarithmic derivative of the genuine elliptic-gamma
field element. -/
theorem logDeriv_addTranslationMeroEquiv_ellipticGammaMero
    (h sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    Differential.logDeriv
        (addTranslationMeroEquiv h (ellipticGammaMero sigma tau hsigma htau)) =
      addTranslationMeroEquiv h
        (ellipticGammaLogDerivMero sigma tau hsigma htau) := by
  rw [Differential.logDeriv, ellipticGammaLogDerivMero,
    map_div₀, addTranslationMeroEquiv_deriv]

/-- The logarithmic derivative of a genuine shift quotient is exactly the external additive
defect. -/
theorem ellipticGammaExternalQuotientMero_logDeriv
    (h sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    (ellipticGammaExternalQuotientMero h sigma tau hsigma htau)′ /
        ellipticGammaExternalQuotientMero h sigma tau hsigma htau =
      ellipticGammaExternalLogDerivDefectMero h sigma tau hsigma htau := by
  change Differential.logDeriv
      (addTranslationMeroEquiv h (ellipticGammaMero sigma tau hsigma htau) /
        ellipticGammaMero sigma tau hsigma htau) = _
  rw [Differential.logDeriv_div]
  · rw [logDeriv_addTranslationMeroEquiv_ellipticGammaMero]
    rfl
  · exact (addTranslationMeroEquiv h).map_ne_zero_iff.mpr
      (ellipticGammaMero_ne_zero sigma tau hsigma htau)
  · exact ellipticGammaMero_ne_zero sigma tau hsigma htau

/-- A family of genuine multiplicative elliptic-gamma shift quotients. -/
def ellipticGammaExternalQuotientFamily
    {κ : Type*} (h : κ → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    κ → meroField Set.univ := fun j ↦
  ellipticGammaExternalQuotientMero (h j) sigma tau hsigma htau

/-- The quotient family and its additive external-defect family represent the same differential
matroid over the paired elliptic compositum. -/
theorem ellipticGammaExternalQuotientFamily_differentialMatroid_eq_defectFamily
    {κ : Type*} (h : κ → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    differentialFamilyMatroid (F := meromorphicEllipticCompositum sigma tau)
        (ellipticGammaExternalQuotientFamily h sigma tau hsigma htau) =
      differentialFamilyMatroid (F := meromorphicEllipticCompositum sigma tau)
        (ellipticGammaExternalDefectFamily h sigma tau hsigma htau) := by
  calc
    differentialFamilyMatroid (F := meromorphicEllipticCompositum sigma tau)
        (ellipticGammaExternalQuotientFamily h sigma tau hsigma htau) =
      differentialFamilyMatroid (F := meromorphicEllipticCompositum sigma tau)
        (fun j ↦
          (ellipticGammaExternalQuotientFamily h sigma tau hsigma htau j)′ /
            ellipticGammaExternalQuotientFamily h sigma tau hsigma htau j) :=
      HTGeometry.differentialFamilyMatroid_deriv_div_self_eq _
    _ = differentialFamilyMatroid
        (F := meromorphicEllipticCompositum sigma tau)
        (ellipticGammaExternalDefectFamily h sigma tau hsigma htau) := by
      congr 1
      funext j
      exact ellipticGammaExternalQuotientMero_logDeriv
        (h j) sigma tau hsigma htau

/-- **Full quotient period-coset partition matroid.**  For arbitrary shifts, the differential
matroid of genuine elliptic-gamma quotients over the paired elliptic compositum has the zero
period class as its loop class and one rank-one parallel class for every nonzero period coset. -/
theorem ellipticGammaExternalQuotientFamily_differentialMatroid_eq_periodCosetPartitionMatroid
    {κ : Type*} [DecidableEq κ]
    (h : κ → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)) :
    differentialFamilyMatroid (F := meromorphicEllipticCompositum sigma tau)
        (ellipticGammaExternalQuotientFamily h sigma tau hsigma htau) =
      affinePointedCollisionMatroid
        (ellipticGammaPeriodClass sigma tau ∘ h) 0 := by
  rw [ellipticGammaExternalQuotientFamily_differentialMatroid_eq_defectFamily,
    ellipticGammaExternalDefectFamily_differentialMatroid_eq_periodCosetPartitionMatroid
      h sigma tau hsigma htau hindependent]

/-- **Exact quotient-family rank law.**  The extended differential rank of any genuine
elliptic-gamma quotient packet is the number of distinct nonzero period classes it meets. -/
theorem ellipticGammaExternalQuotientFamily_eRk_eq_nonzeroPeriodClass_encard
    {κ : Type*} [DecidableEq κ]
    (h : κ → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (I : Set κ) :
    (differentialFamilyMatroid (F := meromorphicEllipticCompositum sigma tau)
      (ellipticGammaExternalQuotientFamily h sigma tau hsigma htau)).eRk I =
      (((ellipticGammaPeriodClass sigma tau ∘ h) '' I) ∩
        {q | q ≠ 0}).encard := by
  rw [ellipticGammaExternalQuotientFamily_differentialMatroid_eq_periodCosetPartitionMatroid
    h sigma tau hsigma htau hindependent,
    affinePointedCollisionMatroid_eRk]

end

end GaloisForLFunctions
