import GaloisForLFunctions.HTGeometry.EllipticGammaRationalBaseMatroid
import GaloisForLFunctions.HTGeometry.EllipticGammaQuotientPeriodCosetMatroid

/-!
# Paper-facing translation-coset rank law for the elliptic gamma function

This capstone packages the exact additive-defect and multiplicative-quotient period-coset
matroids into one theorem.  It also transfers quotient independence to the genuine rational
coordinate base `ℂ(z)`.  The natural elliptic-base rank theorem is stronger than a finite-family
statement: it holds for arbitrary index types and computes extended rank on every subfamily.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher
open HTGeometry

noncomputable section

local instance ellipticGammaTranslationCosetRankLawDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance ellipticGammaTranslationCosetRankLawComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance ellipticGammaTranslationCosetRankLawComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  meromorphicEllipticCompositumComplexAlgebraMero

local instance ellipticGammaTranslationCosetRankLawComplexDifferential : Differential ℂ where
  deriv := 0

local instance ellipticGammaTranslationCosetRankLawMeroDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance ellipticGammaTranslationCosetRankLawMeroCharZero :
    CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap ℂ (meroField Set.univ)).injective

local instance ellipticGammaTranslationCosetRankLawEllipticDifferential
    (sigma tau : ℂ) :
    Differential (meromorphicEllipticCompositum sigma tau) :=
  meromorphicEllipticCompositumDifferential sigma tau

local instance ellipticGammaTranslationCosetRankLawEllipticDifferentialAlgebra
    (sigma tau : ℂ) :
    DifferentialAlgebra (meromorphicEllipticCompositum sigma tau)
      (meroField Set.univ) :=
  ⟨fun x ↦ derivationClosedDifferential_apply
    (meromorphicEllipticCompositum sigma tau)
    (meromorphicEllipticCompositum_derivationClosed sigma tau) x⟩

local instance ellipticGammaTranslationCosetRankLawCoordinateDifferential :
    Differential meromorphicRationalCoordinateField :=
  derivationClosedDifferential _
    meromorphicRationalCoordinateField_derivationClosed

local instance ellipticGammaTranslationCosetRankLawCoordinateDifferentialAlgebra :
    DifferentialAlgebra meromorphicRationalCoordinateField
      (meroField Set.univ) :=
  ⟨fun x ↦ derivationClosedDifferential_apply
    meromorphicRationalCoordinateField
    meromorphicRationalCoordinateField_derivationClosed x⟩

/-- **Exact paper-facing translation-coset matroids.**  The genuine additive defects and
multiplicative elliptic-gamma shift quotients both represent the pointed collision matroid of
rank-three period classes.  The zero class is the loop class and every nonzero class is one
parallel class. -/
theorem ellipticGammaTranslationCoset_differentialMatroids
    {κ : Type*}
    (h : κ → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)) :
    differentialFamilyMatroid (F := meromorphicEllipticCompositum sigma tau)
        (ellipticGammaExternalDefectFamily h sigma tau hsigma htau) =
      affinePointedCollisionMatroid
        (ellipticGammaPeriodClass sigma tau ∘ h) 0 ∧
    differentialFamilyMatroid (F := meromorphicEllipticCompositum sigma tau)
        (ellipticGammaExternalQuotientFamily h sigma tau hsigma htau) =
      affinePointedCollisionMatroid
        (ellipticGammaPeriodClass sigma tau ∘ h) 0 := by
  exact ⟨
    ellipticGammaExternalDefectFamily_differentialMatroid_eq_periodCosetPartitionMatroid
      h sigma tau hsigma htau hindependent,
    ellipticGammaExternalQuotientFamily_differentialMatroid_eq_periodCosetPartitionMatroid
      h sigma tau hsigma htau hindependent⟩

/-- **Exact arbitrary-family translation-coset rank law.**  On every indexed subpacket, both
the additive and multiplicative differential ranks equal the number of distinct nonzero period
classes met by that subpacket. -/
theorem ellipticGammaTranslationCoset_eRk
    {κ : Type*}
    (h : κ → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (I : Set κ) :
    (differentialFamilyMatroid (F := meromorphicEllipticCompositum sigma tau)
      (ellipticGammaExternalDefectFamily h sigma tau hsigma htau)).eRk I =
        (((ellipticGammaPeriodClass sigma tau ∘ h) '' I) ∩
          {q | q ≠ 0}).encard ∧
    (differentialFamilyMatroid (F := meromorphicEllipticCompositum sigma tau)
      (ellipticGammaExternalQuotientFamily h sigma tau hsigma htau)).eRk I =
        (((ellipticGammaPeriodClass sigma tau ∘ h) '' I) ∩
          {q | q ≠ 0}).encard := by
  exact ⟨
    ellipticGammaExternalDefectFamily_eRk_eq_nonzeroPeriodClass_encard
      h sigma tau hsigma htau hindependent I,
    ellipticGammaExternalQuotientFamily_eRk_eq_nonzeroPeriodClass_encard
      h sigma tau hsigma htau hindependent I⟩

/-- Over the genuine rational coordinate base, replacing every nonzero elliptic-gamma quotient
by its logarithmic additive defect preserves the complete represented differential matroid. -/
theorem ellipticGammaExternalQuotientFamily_differentialMatroid_eq_defectFamily_rationalBase
    {κ : Type*} (h : κ → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (ellipticGammaExternalQuotientFamily h sigma tau hsigma htau) =
      differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (ellipticGammaExternalDefectFamily h sigma tau hsigma htau) := by
  calc
    differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (ellipticGammaExternalQuotientFamily h sigma tau hsigma htau) =
      differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (fun j ↦
          (ellipticGammaExternalQuotientFamily h sigma tau hsigma htau j)′ /
            ellipticGammaExternalQuotientFamily h sigma tau hsigma htau j) :=
      HTGeometry.differentialFamilyMatroid_deriv_div_self_eq _
    _ = differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (ellipticGammaExternalDefectFamily h sigma tau hsigma htau) := by
      congr 1
      funext j
      exact ellipticGammaExternalQuotientMero_logDeriv
        (h j) sigma tau hsigma htau

/-- Distinct nonzero period classes of genuine elliptic-gamma quotients form a free
differential matroid over the embedded rational function field `ℂ(z)`. -/
theorem ellipticGammaExternalQuotientFamily_differentialMatroid_eq_freeOn_rationalBase
    {κ : Type*}
    (h : κ → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (hnonres : ∀ j, ThetaTranslationNonresonant tau sigma (h j))
    (hsep : ∀ i j, j ≠ i →
      ThetaTranslationNonresonant tau sigma (h j - h i)) :
    differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (ellipticGammaExternalQuotientFamily h sigma tau hsigma htau) =
      Matroid.freeOn Set.univ := by
  rw [ellipticGammaExternalQuotientFamily_differentialMatroid_eq_defectFamily_rationalBase]
  exact ellipticGammaExternalDefectFamily_differentialMatroid_eq_freeOn_rationalBase
    h sigma tau hsigma htau hindependent hnonres hsep

/-- The rank-three elliptic-gamma source and its logarithmic derivative are simultaneously
hypertranscendental over the paired elliptic compositum. -/
theorem ellipticGammaSource_hypertranscendentalOver_ellipticCompositum
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)) :
    HypertranscendentalOver (meromorphicEllipticCompositum sigma tau)
        (ellipticGammaLogDerivMero sigma tau hsigma htau) ∧
      HypertranscendentalOver (meromorphicEllipticCompositum sigma tau)
        (ellipticGammaMero sigma tau hsigma htau) := by
  exact ⟨
    hypertranscendentalOver_ellipticGammaLogDerivMero_ellipticCompositum
      sigma tau hsigma htau hindependent,
    hypertranscendentalOver_ellipticGammaMero_ellipticCompositum
      sigma tau hsigma htau hindependent⟩

end

end GaloisForLFunctions
