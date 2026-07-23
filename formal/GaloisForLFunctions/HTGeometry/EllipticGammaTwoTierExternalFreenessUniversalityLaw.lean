import GaloisForLFunctions.HTGeometry.EllipticGammaExternalDefectFamilyDifferentialAtomic
import GaloisForLFunctions.HTGeometry.EllipticGammaTranslationCosetRankLaw

/-!
# Two-tier external freeness for elliptic Gamma

Separated external shifts of the actual elliptic-Gamma source have two simultaneous kinds of
freeness.  Over the rational coordinate field, their multiplicative quotients form the free
differential matroid.  After enlarging coefficients to elliptic fractions, no nonzero finite
constant-coefficient differential-operator combination of their additive defects can enter that
elliptic fraction field.  Thus rational-base nonlinear freeness and elliptic-base differential
atomicity are two layers of one translation-coset law.
-/

namespace GaloisForLFunctions

open Filter Set Topology Function Complex
open Bottcher HTGeometry
open scoped Differential

noncomputable section

local instance ellipticGammaTwoTierDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance ellipticGammaTwoTierComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance ellipticGammaTwoTierComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  meromorphicEllipticCompositumComplexAlgebraMero

local instance ellipticGammaTwoTierComplexDifferential : Differential ℂ where
  deriv := 0

local instance ellipticGammaTwoTierMeroDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance ellipticGammaTwoTierMeroCharZero :
    CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap ℂ (meroField Set.univ)).injective

local instance ellipticGammaTwoTierCoordinateDifferential :
    Differential meromorphicRationalCoordinateField :=
  derivationClosedDifferential _
    meromorphicRationalCoordinateField_derivationClosed

local instance ellipticGammaTwoTierCoordinateDifferentialAlgebra :
    DifferentialAlgebra meromorphicRationalCoordinateField
      (meroField Set.univ) :=
  ⟨fun x ↦ derivationClosedDifferential_apply
    meromorphicRationalCoordinateField
    meromorphicRationalCoordinateField_derivationClosed x⟩

/-- **Elliptic-Gamma two-tier external freeness universality law.**  Pairwise nonresonant shifts
are differentially free over `ℂ(z)`, while every nonzero finite `ℂ[∂]` defect combination
remains outside the elliptic fraction field. -/
theorem ellipticGamma_twoTierExternalFreenessUniversality
    {κ : Type*} [DecidableEq κ]
    (s : Finset κ) (h : κ → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (hnonres : ∀ j, ThetaTranslationNonresonant tau sigma (h j))
    (hsep : ∀ i j, j ≠ i →
      ThetaTranslationNonresonant tau sigma (h j - h i)) :
    differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (ellipticGammaExternalQuotientFamily h sigma tau hsigma htau) =
      Matroid.freeOn Set.univ ∧
    ∀ (L : κ → Polynomial ℂ),
      (∃ i ∈ s, L i ≠ 0) →
      ∀ {a b : analyticSubring (Set.univ : Set ℂ)}, b ≠ 0 →
      ∀ {f g : ℂ → ℂ}, AnalyticOnNhd ℂ f Set.univ →
      AnalyticOnNhd ℂ g Set.univ →
      Germ.coeRingHom (Filter.principal Set.univ) f =
        (a : Germ (Filter.principal Set.univ) ℂ) →
      Germ.coeRingHom (Filter.principal Set.univ) g =
        (b : Germ (Filter.principal Set.univ) ℂ) →
      Function.Periodic (fun z ↦ f z / g z) 1 →
      Function.Periodic (fun z ↦ f z / g z) tau →
      ellipticGammaExternalDifferentialFamilySum
          s L h sigma tau hsigma htau ≠
        algebraMap (analyticSubring Set.univ)
            (meroField Set.univ) a /
          algebraMap (analyticSubring Set.univ)
            (meroField Set.univ) b := by
  constructor
  · exact ellipticGammaExternalQuotientFamily_differentialMatroid_eq_freeOn_rationalBase
      h sigma tau hsigma htau hindependent hnonres hsep
  · intro L hnz a b hb f g hf hg hfa hgb hperiodOne hperiodTau
    exact ellipticGammaExternalDifferentialFamilySum_ne_ellipticFraction_of_nonzero
      hsigma htau
      (thetaTranslationNontorsion_of_ellipticGammaSourcePeriods_linearIndependent
        sigma tau hindependent)
      (fun j hj ↦ hnonres j)
      (fun i hi j hj hji ↦ hsep i j hji)
      hnz hb hf hg hfa hgb hperiodOne hperiodTau

end

end GaloisForLFunctions
