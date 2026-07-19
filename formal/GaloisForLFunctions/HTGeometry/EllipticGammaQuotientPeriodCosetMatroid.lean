import GaloisForLFunctions.HTGeometry.CoordinatewiseDifferentialFamilyMatroid
import GaloisForLFunctions.HTGeometry.EllipticGammaPeriodCosetMatroid
import GaloisForLFunctions.HTGeometry.MultiplicativeTranslationCharacter

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

/-- Every genuine elliptic-gamma shift quotient is a nonzero meromorphic-field element. -/
theorem ellipticGammaExternalQuotientMero_ne_zero
    (h sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    ellipticGammaExternalQuotientMero h sigma tau hsigma htau ≠ 0 := by
  exact div_ne_zero
    ((addTranslationMeroEquiv h).map_ne_zero_iff.mpr
      (ellipticGammaMero_ne_zero sigma tau hsigma htau))
    (ellipticGammaMero_ne_zero sigma tau hsigma htau)

/-- **Multiplicative quotient reflection.** The quotient at the reflected shift is the inverse of
the original quotient translated back by that shift. -/
theorem ellipticGammaExternalQuotientMero_neg
    (h sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    ellipticGammaExternalQuotientMero (-h) sigma tau hsigma htau =
      (addTranslationMeroEquiv (-h)
        (ellipticGammaExternalQuotientMero h sigma tau hsigma htau))⁻¹ := by
  simpa [ellipticGammaExternalQuotientMero] using
    addTranslationMeroEquiv_div_self_neg h
      (ellipticGammaMero sigma tau hsigma htau)

/-- Genuine elliptic-gamma shift quotients instantiate the universal multiplicative translation
cocycle. -/
theorem ellipticGammaExternalQuotientMero_add
    (p q sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    ellipticGammaExternalQuotientMero (p + q) sigma tau hsigma htau =
      ellipticGammaExternalQuotientMero p sigma tau hsigma htau *
        addTranslationMeroEquiv p
          (ellipticGammaExternalQuotientMero q sigma tau hsigma htau) := by
  simpa [ellipticGammaExternalQuotientMero] using
    addTranslationMeroEquiv_div_self_add p q
      (ellipticGammaMero sigma tau hsigma htau)

/-- **Concrete elliptic-gamma cocycle character law.** Once a meromorphic-field automorphism
commutes with translations and scales the genuine quotient packet by translation-fixed units, its
scalars form a character. Nonvanishing and the cocycle hypotheses are discharged by the actual
elliptic-gamma quotient. -/
theorem ellipticGammaExternalQuotient_scalars_mul
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (gamma : meroField Set.univ ≃+* meroField Set.univ)
    (c : ℂ → (meroField Set.univ)ˣ)
    (hcomm : ∀ h x, gamma (addTranslationMeroEquiv h x) =
      addTranslationMeroEquiv h (gamma x))
    (hfixed : ∀ h k, addTranslationMeroEquiv h (c k : meroField Set.univ) = c k)
    (hscale : ∀ h, gamma
      (ellipticGammaExternalQuotientMero h sigma tau hsigma htau) =
        (c h : meroField Set.univ) *
          ellipticGammaExternalQuotientMero h sigma tau hsigma htau)
    (p q : ℂ) : c (p + q) = c p * c q := by
  exact multiplicativeTranslationCocycle_scalars_mul
    (fun h ↦ addTranslationMeroEquiv h)
    (fun h ↦ ellipticGammaExternalQuotientMero h sigma tau hsigma htau)
    gamma c
    (fun h ↦ ellipticGammaExternalQuotientMero_ne_zero
      h sigma tau hsigma htau)
    (fun a b ↦ ellipticGammaExternalQuotientMero_add
      a b sigma tau hsigma htau)
    hcomm hfixed hscale p q

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

/-- **Exact DA spectrum of the genuine multiplicative quotient.** Over the paired elliptic
compositum, an elliptic-gamma shift quotient is differentially algebraic exactly on the rank-three
integer period group. -/
theorem differentialAlgebraicOver_ellipticGammaExternalQuotientMero_iff_resonant
    (h sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)) :
    DifferentialAlgebraicOver (meromorphicEllipticCompositum sigma tau)
        (ellipticGammaExternalQuotientMero h sigma tau hsigma htau) ↔
      ∃ a b n : ℤ, h = a + b * tau + n * sigma := by
  rw [← differentialAlgebraicOver_deriv_div_self_iff]
  rw [ellipticGammaExternalQuotientMero_logDeriv]
  exact
    differentialAlgebraicOver_ellipticGammaExternalLogDerivDefectMero_iff_resonant
      h sigma tau hsigma htau hindependent

/-- Equivalently, every nonresonant genuine elliptic-gamma quotient is hypertranscendental over
the paired elliptic compositum. -/
theorem hypertranscendentalOver_ellipticGammaExternalQuotientMero_iff_nonresonant
    (h sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)) :
    HypertranscendentalOver (meromorphicEllipticCompositum sigma tau)
        (ellipticGammaExternalQuotientMero h sigma tau hsigma htau) ↔
      ThetaTranslationNonresonant tau sigma h := by
  simpa [HypertranscendentalOver, ThetaTranslationNonresonant] using
    not_congr
      (differentialAlgebraicOver_ellipticGammaExternalQuotientMero_iff_resonant
        h sigma tau hsigma htau hindependent)

/-- A family of genuine multiplicative elliptic-gamma shift quotients. -/
def ellipticGammaExternalQuotientFamily
    {κ : Type*} (h : κ → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    κ → meroField Set.univ := fun j ↦
  ellipticGammaExternalQuotientMero (h j) sigma tau hsigma htau

/-- The multiplicative quotient reflection law holds componentwise for every indexed packet. -/
theorem ellipticGammaExternalQuotientFamily_reflection
    {κ : Type*} (h : κ → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    ellipticGammaExternalQuotientFamily
        (fun j ↦ -h j) sigma tau hsigma htau =
      fun j ↦ (addTranslationMeroEquiv (-h j)
        (ellipticGammaExternalQuotientFamily h sigma tau hsigma htau j))⁻¹ := by
  funext j
  exact ellipticGammaExternalQuotientMero_neg
    (h j) sigma tau hsigma htau

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

/-- **Reflection invariance of the quotient-family matroid.** Every differential dependence among
genuine elliptic-gamma quotients is preserved when all shift parameters are negated. -/
theorem ellipticGammaExternalQuotientFamily_differentialMatroid_reflection
    {κ : Type*} [DecidableEq κ]
    (h : κ → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)) :
    differentialFamilyMatroid (F := meromorphicEllipticCompositum sigma tau)
        (ellipticGammaExternalQuotientFamily
          (fun j ↦ -h j) sigma tau hsigma htau) =
      differentialFamilyMatroid (F := meromorphicEllipticCompositum sigma tau)
        (ellipticGammaExternalQuotientFamily h sigma tau hsigma htau) := by
  rw [ellipticGammaExternalQuotientFamily_differentialMatroid_eq_defectFamily
      (fun j ↦ -h j) sigma tau hsigma htau,
    ellipticGammaExternalQuotientFamily_differentialMatroid_eq_defectFamily
      h sigma tau hsigma htau]
  exact ellipticGammaExternalDefectFamily_differentialMatroid_reflection
    h sigma tau hsigma htau hindependent

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
