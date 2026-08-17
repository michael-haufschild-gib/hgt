import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaPeriodRankDichotomy

/-!
# Rational rank at most two makes multiple elliptic Gamma differentially algebraic

The exact rank dichotomy states that the multiple elliptic Gamma function of a finite
upper-half-plane period family is differentially algebraic precisely when the rational span of the
periods together with the unit period has rank two.  Since that rank is always at least two, the
"rank at most two" hypothesis of Kato's rational-period theorem is exactly the differentially
algebraic phase, for the raw function and for its logarithmic derivative alike.
-/


namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Rational-rank-two differential algebraicity.**  A finite upper-half-plane period family whose
rational span together with the unit period has rank at most two makes the multiple elliptic Gamma
function differentially algebraic over the rational function field. -/
theorem differentialAlgebraicOver_multipleEllipticGammaMero_of_augmentedPeriodRank_le_two
    [Nonempty ι] (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hrank : multipleEllipticGammaAugmentedPeriodRank τ ≤ 2) :
    DifferentialAlgebraicOver (RatFunc ℂ) (multipleEllipticGammaMero τ hτ) := by
  rw [differentialAlgebraicOver_multipleEllipticGammaMero_iff_augmentedPeriodRank_eq_two τ hτ]
  exact le_antisymm hrank (two_le_augmentedPeriodRank τ hτ)

/-- The logarithmic derivative inherits differential algebraicity at rational rank two. -/
theorem differentialAlgebraicOver_multipleEllipticGammaLogDerivMero_of_augmentedPeriodRank_le_two
    [Nonempty ι] (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hrank : multipleEllipticGammaAugmentedPeriodRank τ ≤ 2) :
    DifferentialAlgebraicOver (RatFunc ℂ) (multipleEllipticGammaLogDerivMero τ hτ) := by
  rw [differentialAlgebraicOver_multipleEllipticGammaLogDerivMero_iff_augmentedPeriodRank_eq_two
    τ hτ]
  exact le_antisymm hrank (two_le_augmentedPeriodRank τ hτ)

end

end GaloisForLFunctions
