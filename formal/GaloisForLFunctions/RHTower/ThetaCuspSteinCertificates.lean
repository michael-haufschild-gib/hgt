import GaloisForLFunctions.RHTower.ThetaGibbsSteinSourceMinor
import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureBalance
import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor
import GaloisForLFunctions.RHTower.PrimeArchHankelDeterminantCriterion
import GaloisForLFunctions.RHTower.PrimeArchThetaLikelihoodOrderedTailTransfer
import GaloisForLFunctions.RHTower.PrimeArchThetaSourceAtomDomination
import GaloisForLFunctions.RHTower.PrimeArchThetaBornWittenRobinSteinWard
import GaloisForLFunctions.RHTower.PrimeArchThetaThermalSusceptibility
import GaloisForLFunctions.RHTower.XiShiftedHankelCassiniCentralCumulantGerm
import GaloisForLFunctions.RHTower.PrimeArchThetaLiouvilleWard
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionEighthBoundaryKreinFirstCrossing
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionEighthGlobal

/-!
# Theta-cusp moment certificates from the Stein ratio bounds

`thetaCuspFirstAtomWardMoment_stein_ratio_bounds` gives the two first-atom ratio inequalities
`14 (r w₂)² ≤ 9 w₁ w₃` and `16 (r w₀)(r w₂) ≤ 45 w₁²` (`r = 3005/2997`, `wⱼ` the Ward moments), and
`forall_primeArchSourceTraceHankel_linear_nonneg_stein` the resulting positivity of every linear
source Hankel test.  The corpus records a family of equivalent or weaker forms of these facts as
named certificates, each reached only through a conditional implication or an `↔`.  This module
states them outright:

* via the linear Hankel positivity: the sixth-moment Hankel inequality, the three-temperature mean
  balance, the first normalized moment minor, the `2 × 2` Hankel determinant, the Gaussian aperture
  balance at `0`, the raw cubic moment form and the central cumulant discriminant;
* via the second Stein bound and `atom = 2π · Ward`: the relaxed fourth-moment concentration and its
  Born–Witten and size-biased-susceptibility forms;
* via the first Stein bound (`r ≥ 1` absorbs one factor of `r`): the upper adjacent ratio separation.

Separately, global positivity of the eighth full-reflection Hankel curvature gives the
boundary-crossing form on `(0, 137/2000)`.
-/

open Polynomial

namespace RHTower

noncomputable section

/-! ## Linear source Hankel positivity and its equivalent certificates -/

/-- The sixth-moment Hankel inequality of the theta-cusp source. -/
theorem thetaCuspSixthMomentHankelInequality_holds : ThetaCuspSixthMomentHankelInequality :=
  forall_primeArchSourceTraceHankel_linear_nonneg_iff_thetaCuspSixthMomentHankelInequality.mp
    forall_primeArchSourceTraceHankel_linear_nonneg_stein

/-- The three-temperature mean balance of the theta-cusp source. -/
theorem thetaCuspThreeTemperatureMeanBalance_holds : ThetaCuspThreeTemperatureMeanBalance :=
  forall_primeArchSourceTraceHankel_linear_nonneg_iff_threeTemperatureMeanBalance.mp
    forall_primeArchSourceTraceHankel_linear_nonneg_stein

/-- The first normalized prime–archimedean moment minor is nonnegative: `m₀ m₂ ≥ m₁²`. -/
theorem normalizedPrimeArchMoment_firstMinor_nonneg :
    0 ≤ normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 -
      normalizedPrimeArchMoment 1 ^ 2 :=
  forall_primeArchSourceTraceHankel_linear_nonneg_iff_firstMinor.mp
    forall_primeArchSourceTraceHankel_linear_nonneg_stein

/-- The `2 × 2` source moment Hankel determinant is nonnegative. -/
theorem det_primeArchSourceMomentHankelMatrix_two_nonneg :
    0 ≤ (primeArchSourceMomentHankelMatrix 2).det :=
  det_primeArchSourceMomentHankelMatrix_two_nonneg_iff_thetaCusp.mpr
    thetaCuspSixthMomentHankelInequality_holds

/-- The Gaussian aperture balance of the theta-cusp source is nonnegative at aperture `0`. -/
theorem thetaCuspGaussianApertureBalance_zero_nonneg :
    0 ≤ thetaCuspGaussianApertureBalance 0 :=
  thetaCuspGaussianApertureBalance_zero_nonneg_iff.mpr thetaCuspThreeTemperatureMeanBalance_holds

/-- The raw cubic moment form `3 μ₀ μ₁ μ₃ + 15 μ₁² μ₂ − 10 μ₀ μ₂² ≥ 0`. -/
theorem thetaCusp_raw_cubic_nonneg :
    0 ≤ 3 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 1 *
          thetaCuspRawEvenMoment 3 +
        15 * thetaCuspRawEvenMoment 1 ^ 2 * thetaCuspRawEvenMoment 2 -
        10 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2 ^ 2 :=
  thetaCuspThreeTemperatureMeanBalance_iff_raw_cubic_nonneg.mp
    thetaCuspThreeTemperatureMeanBalance_holds

/-- The central cumulant discriminant of the theta-cusp source is nonnegative. -/
theorem thetaCuspCentralCumulantDiscriminant_nonneg :
    0 ≤ thetaCuspCentralCumulantDiscriminant :=
  thetaCuspCentralCumulantDiscriminant_nonneg_iff_apertureBalance_zero_nonneg.mpr
    thetaCuspGaussianApertureBalance_zero_nonneg

/-! ## The second Stein bound: relaxed fourth-moment concentration -/

/-- **Relaxed fourth-moment concentration**, from `16 (r w₀)(r w₂) ≤ 45 w₁²` scaled by `(2π)²`. -/
theorem thetaCuspRelaxedFourthMomentConcentration_holds :
    ThetaCuspRelaxedFourthMomentConcentration := by
  apply thetaCuspRelaxedFourthMomentConcentration_of_first_atom
  rw [thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment 0,
    thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment 1,
    thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment 2]
  have hscaled := mul_le_mul_of_nonneg_left
    thetaCuspFirstAtomWardMoment_stein_ratio_bounds.2 (sq_nonneg (2 * Real.pi))
  linear_combination hscaled

/-- The relaxed concentration in Born–Witten superpotential moments. -/
theorem thetaCuspFullBornWittenSuperpotentialMoment_relaxed :
    16 * thetaCuspFullBornWittenSuperpotentialMoment 0 *
        thetaCuspFullBornWittenSuperpotentialMoment 2 ≤
      25 * thetaCuspFullBornWittenSuperpotentialMoment 1 ^ (2 : ℕ) :=
  thetaCuspRelaxedFourthMomentConcentration_iff_fullBornWittenSuperpotentialMoment.mp
    thetaCuspRelaxedFourthMomentConcentration_holds

/-- The relaxed concentration as an upper bound on the size-biased susceptibility. -/
theorem thetaCuspSizeBiasedSusceptibility_zero_upper :
    16 * thetaCuspSizeBiasedSusceptibility 0 ≤ 29 * thetaCuspSizeBiasedMean 0 ^ (2 : ℕ) :=
  thetaCuspRelaxedFourthMomentConcentration_iff_susceptibility_upper.mp
    thetaCuspRelaxedFourthMomentConcentration_holds

/-! ## The first Stein bound: upper adjacent ratio separation -/

/-- **Upper adjacent ratio separation**, from `14 (r w₂)² ≤ 9 w₁ w₃`: since `r ≥ 1`, the
single-loss form `14 r a₂² ≤ 9 a₁ a₃` follows after scaling `aⱼ = 2π wⱼ`. -/
theorem thetaCuspUpperAdjacentRatioSeparation_holds : ThetaCuspUpperAdjacentRatioSeparation := by
  apply thetaCuspUpperAdjacentRatioSeparation_of_first_atom_singleLoss
  rw [thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment 1,
    thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment 2,
    thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment 3]
  have hstein := thetaCuspFirstAtomWardMoment_stein_ratio_bounds.1
  set w₂ := thetaCuspFirstAtomWardMoment 2
  -- `r w₂² ≤ (r w₂)²` because `r = 3005/2997 ≥ 1`
  have hr : 14 * (3005 / 2997 : ℝ) * w₂ ^ 2 ≤ 14 * ((3005 / 2997 : ℝ) * w₂) ^ 2 := by
    nlinarith [sq_nonneg w₂]
  have hpi := sq_nonneg (2 * Real.pi)
  have hscaled := mul_le_mul_of_nonneg_left (hr.trans hstein) hpi
  linear_combination hscaled

/-! ## The eighth full-reflection Hankel curvature -/

/-- At every interior zero of the eighth source-reflection Hankel curvature in `(0, 137/2000)`, the
boundary crossing is positive. -/
theorem thetaCuspFullSourceReflectionEighthBoundaryCrossing_pos :
    ∀ x : ℝ, 0 < x → x < (137 / 2000 : ℝ) →
      thetaCuspFullSourceReflectionEighthHankelCurvature x = 0 →
      0 < thetaCuspFullSourceReflectionEighthBoundaryCrossing x :=
  thetaCuspFullReflectionEighthHankelCurvature_pos_iff_boundaryCrossing.mp
    thetaCuspFullReflectionEighthHankelCurvature_pos_on_nonnegative

end

end RHTower
