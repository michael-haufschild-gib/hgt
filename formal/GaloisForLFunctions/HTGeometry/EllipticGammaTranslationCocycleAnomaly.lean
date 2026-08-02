import GaloisForLFunctions.HTGeometry.EllipticGammaTranslationAnomalyRationalBase
import GaloisForLFunctions.HTGeometry.MeromorphicRankThreeSourceBoundary
import GaloisForLFunctions.HTGeometry.MultipleGammaTransverseDifference

/-!
# The elliptic-gamma translation cocycle is not a differentially algebraic coboundary

The shift quotients of the genuine elliptic gamma form a multiplicative translation cocycle whose
values are differentially algebraic on the whole rank-three period group, and which is visibly the
coboundary of the gamma function itself in the ambient meromorphic units.

It is not a coboundary inside the differentially algebraic units.  A differentially algebraic
trivializer would make the ratio of the gamma function by it fixed under all three source
generators, hence constant, hence would make the gamma function differentially algebraic — which
the exact period-rank dichotomy forbids.
-/

open Filter Set Topology Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

attribute [local instance] meromorphicEllipticCompositumComplexAlgebraMero

/-! ## The cocycle and its ambient trivialization -/

/-- The shift quotient is the ambient coboundary of the gamma function. -/
theorem ellipticGammaExternalQuotientMero_eq_coboundary
    (h sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    ellipticGammaExternalQuotientMero h sigma tau hsigma htau =
      addTranslationMeroEquiv h (ellipticGammaMero sigma tau hsigma htau) /
        ellipticGammaMero sigma tau hsigma htau := rfl

/-- A trivializer of the shift cocycle makes its ratio with the gamma function fixed by the given
translation. -/
theorem addTranslationMeroEquiv_div_eq_of_coboundary
    (h sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    {b : meroField (Set.univ : Set ℂ)} (hb : b ≠ 0)
    (hcob : ellipticGammaExternalQuotientMero h sigma tau hsigma htau =
      addTranslationMeroEquiv h b / b) :
    addTranslationMeroEquiv h (ellipticGammaMero sigma tau hsigma htau / b) =
      ellipticGammaMero sigma tau hsigma htau / b := by
  have hG : ellipticGammaMero sigma tau hsigma htau ≠ 0 :=
    ellipticGammaMero_ne_zero sigma tau hsigma htau
  have hbh : addTranslationMeroEquiv h b ≠ 0 :=
    (addTranslationMeroEquiv h).map_ne_zero_iff.mpr hb
  rw [ellipticGammaExternalQuotientMero_eq_coboundary] at hcob
  rw [map_div₀]
  rw [div_eq_div_iff hG hb] at hcob
  rw [div_eq_div_iff hbh hb]
  linear_combination (norm := ring_nf) hcob

/-! ## Nontriviality of the anomaly class -/

/-- **The translation cocycle is not a differentially algebraic coboundary.**  There is no nonzero
differentially algebraic germ whose translation coboundary reproduces the elliptic-gamma shift
quotients at the three source generators. -/
theorem ellipticGammaShiftCocycle_not_differentialAlgebraic_coboundary
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)) :
    ¬ ∃ b : meroField (Set.univ : Set ℂ), b ≠ 0 ∧
        DifferentialAlgebraicOver (RatFunc ℂ) b ∧
        ∀ i : Fin 3,
          ellipticGammaExternalQuotientMero
              (ellipticGammaSourcePeriods sigma tau i) sigma tau hsigma htau =
            addTranslationMeroEquiv (ellipticGammaSourcePeriods sigma tau i) b / b := by
  classical
  rintro ⟨b, hb, hbDA, hcob⟩
  have hG : ellipticGammaMero sigma tau hsigma htau ≠ 0 :=
    ellipticGammaMero_ne_zero sigma tau hsigma htau
  have hfixed : JointFixed
      (rankThreeGeneratorMeromorphicDifferenceDifferentialField
        (ellipticGammaSourcePeriods sigma tau))
      (ellipticGammaMero sigma tau hsigma htau / b) := by
    intro i
    exact addTranslationMeroEquiv_div_eq_of_coboundary _ sigma tau hsigma htau hb (hcob i)
  obtain ⟨c, hc⟩ :=
    (rankThree_generator_jointFixed_iff_constant _ hindependent _).mp hfixed
  have hceq : algebraMap ℂ (meroField (Set.univ : Set ℂ)) c =
      ellipticGammaMero sigma tau hsigma htau / b := hc
  have hGamma : ellipticGammaMero sigma tau hsigma htau =
      algebraMap ℂ (meroField (Set.univ : Set ℂ)) c * b := by
    rw [hceq, div_mul_cancel₀ _ hb]
  have hcDA : DifferentialAlgebraicOver (RatFunc ℂ)
      (algebraMap ℂ (meroField (Set.univ : Set ℂ)) c) :=
    differentialAlgebraicOver_algebraMap_complex c
  have hGDA : DifferentialAlgebraicOver (RatFunc ℂ)
      (ellipticGammaMero sigma tau hsigma htau) := by
    rw [hGamma]
    exact differentialAlgebraicOver_mul hcDA hbDA
  exact hypertranscendentalOver_ratFunc_ellipticGammaMero sigma tau hsigma htau hindependent hGDA

/-- **The exact anomaly phase.**  The shift cocycle takes differentially algebraic values on the
whole period group and is the ambient coboundary of the gamma function, yet it admits no
differentially algebraic trivializer. -/
theorem ellipticGamma_translationCocycle_anomaly
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)) :
    (∀ h : ℂ, (∃ a b n : ℤ, h = a + b * tau + n * sigma) →
        DifferentialAlgebraicOver (RatFunc ℂ)
          (ellipticGammaExternalQuotientMero h sigma tau hsigma htau)) ∧
      (∀ h : ℂ, ellipticGammaExternalQuotientMero h sigma tau hsigma htau =
        addTranslationMeroEquiv h (ellipticGammaMero sigma tau hsigma htau) /
          ellipticGammaMero sigma tau hsigma htau) ∧
      ¬ ∃ b : meroField (Set.univ : Set ℂ), b ≠ 0 ∧
        DifferentialAlgebraicOver (RatFunc ℂ) b ∧
        ∀ i : Fin 3,
          ellipticGammaExternalQuotientMero
              (ellipticGammaSourcePeriods sigma tau i) sigma tau hsigma htau =
            addTranslationMeroEquiv (ellipticGammaSourcePeriods sigma tau i) b / b :=
  ⟨fun h hres => (ellipticGamma_translationAnomaly sigma tau hsigma htau hindependent).1 h hres,
    fun h => ellipticGammaExternalQuotientMero_eq_coboundary h sigma tau hsigma htau,
    ellipticGammaShiftCocycle_not_differentialAlgebraic_coboundary
      sigma tau hsigma htau hindependent⟩

end

end GaloisForLFunctions
