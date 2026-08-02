import GaloisForLFunctions.HTGeometry.EllipticCompositumRationalBase
import GaloisForLFunctions.HTGeometry.EllipticGammaQuotientPeriodCosetMatroid

/-!
# The elliptic-gamma translation anomaly over the rational coordinate field

The paired elliptic compositum is differentially algebraic over `ℂ(z)`, so differential
algebraicity over `ℂ(z)` implies it over the compositum.  Combined with the exact compositum
spectrum this pins the natural-base statements:

* a multiplicative shift quotient of the genuine elliptic gamma is differentially algebraic over
  `ℂ(z)` exactly on the rank-three integer period group;
* the gamma function itself is hypertranscendental over `ℂ(z)`.

Together these say that the class of the gamma function modulo the differentially algebraic
sector is fixed by the whole period group while its connecting cocycle is nontrivial: the
translation anomaly is exact.
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

/-! ## Differential algebraicity descends to the compositum -/

/-- The paired elliptic compositum contains the constants, so differential algebraicity over
`ℂ(z)` implies it over the compositum. -/
theorem differentialAlgebraicOver_compositum_of_ratFunc {σ τ : ℂ}
    {x : meroField (Set.univ : Set ℂ)}
    (hx : DifferentialAlgebraicOver (RatFunc ℂ) x) :
    DifferentialAlgebraicOver (meromorphicEllipticCompositum σ τ) x :=
  differentialAlgebraicOver_mono
    (HTGeometry.differentialAlgebraicOver_complex_of_ratFunc hx)

/-! ## The exact natural-base spectrum -/

/-- **Exact DA spectrum over `ℂ(z)`.**  A genuine elliptic-gamma shift quotient is differentially
algebraic over the rational coordinate field exactly on the rank-three integer period group. -/
theorem differentialAlgebraicOver_ratFunc_ellipticGammaExternalQuotientMero_iff_resonant
    (h sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (ellipticGammaExternalQuotientMero h sigma tau hsigma htau) ↔
      ∃ a b n : ℤ, h = a + b * tau + n * sigma := by
  constructor
  · intro hDA
    exact (differentialAlgebraicOver_ellipticGammaExternalQuotientMero_iff_resonant
      h sigma tau hsigma htau hindependent).mp
      (differentialAlgebraicOver_compositum_of_ratFunc hDA)
  · intro hres
    exact differentialAlgebraicOver_ratFunc_ellipticGammaExternalQuotientMero_of_resonant
      h sigma tau hsigma htau hindependent hres

/-- Equivalently, every off-spectrum shift quotient is hypertranscendental over `ℂ(z)`. -/
theorem hypertranscendentalOver_ratFunc_ellipticGammaExternalQuotientMero_iff_nonresonant
    (h sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)) :
    HypertranscendentalOver (RatFunc ℂ)
        (ellipticGammaExternalQuotientMero h sigma tau hsigma htau) ↔
      ¬ ∃ a b n : ℤ, h = a + b * tau + n * sigma := by
  rw [HypertranscendentalOver,
    differentialAlgebraicOver_ratFunc_ellipticGammaExternalQuotientMero_iff_resonant
      h sigma tau hsigma htau hindependent]

/-- **Natural-base hypertranscendence of the gamma function.** -/
theorem hypertranscendentalOver_ratFunc_ellipticGammaMero
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)) :
    HypertranscendentalOver (RatFunc ℂ) (ellipticGammaMero sigma tau hsigma htau) := by
  intro hDA
  exact hypertranscendentalOver_ellipticGammaMero_ellipticCompositum
    sigma tau hsigma htau hindependent
    (differentialAlgebraicOver_compositum_of_ratFunc hDA)

/-! ## The translation anomaly -/

/-- **The elliptic-gamma translation anomaly.**  Over the rational coordinate field the class of
the genuine elliptic gamma modulo the differentially algebraic sector is fixed by the whole
rank-three period group, while the gamma function itself is not differentially algebraic, so the
connecting cocycle of that class is nontrivial. -/
theorem ellipticGamma_translationAnomaly
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)) :
    (∀ h : ℂ, (∃ a b n : ℤ, h = a + b * tau + n * sigma) →
        DifferentialAlgebraicOver (RatFunc ℂ)
          (ellipticGammaExternalQuotientMero h sigma tau hsigma htau)) ∧
      (∀ h : ℂ, ¬ (∃ a b n : ℤ, h = a + b * tau + n * sigma) →
        HypertranscendentalOver (RatFunc ℂ)
          (ellipticGammaExternalQuotientMero h sigma tau hsigma htau)) ∧
      ¬ DifferentialAlgebraicOver (RatFunc ℂ) (ellipticGammaMero sigma tau hsigma htau) := by
  refine ⟨fun h hres => ?_, fun h hnon => ?_, ?_⟩
  · exact (differentialAlgebraicOver_ratFunc_ellipticGammaExternalQuotientMero_iff_resonant
      h sigma tau hsigma htau hindependent).mpr hres
  · exact (hypertranscendentalOver_ratFunc_ellipticGammaExternalQuotientMero_iff_nonresonant
      h sigma tau hsigma htau hindependent).mpr hnon
  · exact hypertranscendentalOver_ratFunc_ellipticGammaMero sigma tau hsigma htau hindependent

end

end GaloisForLFunctions
