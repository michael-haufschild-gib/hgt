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
import GaloisForLFunctions.RHTower.XiPrimeMarkedFiniteSixthHeadBudget
import GaloisForLFunctions.RHTower.PrimeArchThetaSingleGibbsCertificateReduction
import GaloisForLFunctions.RHTower.PrimeArchThetaLikelihoodSteinSingleLoss
import GaloisForLFunctions.RHTower.ThetaSingleGibbsLikelihoodSingleLossClosure

/-!
# Theta-cusp moment certificates from the Stein ratio bounds

`thetaCuspFirstAtomWardMoment_stein_ratio_bounds` gives the two first-atom ratio inequalities
`14 (r w₂)² ≤ 9 w₁ w₃` and `16 (r w₀)(r w₂) ≤ 45 w₁²` (`r = 3005/2997`, `wⱼ` the Ward moments), and
`forall_primeArchSourceTraceHankel_linear_nonneg_stein` the resulting positivity of every linear
source Hankel test; `normalizedPrimeArch_firstHankelMinor_pos_from_stein` makes the first minor
strict.  The corpus records a family of equivalent or weaker forms of these facts as named
certificates, each reached only through a conditional implication or an `↔`.  This module
states them outright:

* via the linear Hankel positivity: the sixth-moment Hankel inequality and the three-temperature
  mean balance;
* via the strict first minor: strict positivity of the raw cubic moment form, of the Gaussian
  aperture balance at `0` and of the central cumulant discriminant;
* via the second Stein bound and `atom = 2π · Ward`: the relaxed fourth-moment concentration and its
  Born–Witten and size-biased-susceptibility forms;
* via the first Stein bound (`r ≥ 1` absorbs one factor of `r`): the upper adjacent ratio separation,
  its susceptibility form, and the susceptibility, Pearson and mean-lift windows;
* via `BW_{j,0,1} = wⱼ` and `BW_{j,1,1} = w_{j+1}`: the two radial Born–Witten ratio bounds, their
  single-loss forms, the single-Gibbs relaxed certificate and the single-loss first-atom bounds.

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

/-! ## The strict first minor and its equivalent certificates -/

/-- The raw cubic moment form `3 μ₀ μ₁ μ₃ + 15 μ₁² μ₂ − 10 μ₀ μ₂² > 0`: it is `360 μ₀³` times the
strict first normalized minor. -/
theorem thetaCusp_raw_cubic_pos :
    0 < 3 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 1 *
          thetaCuspRawEvenMoment 3 +
        15 * thetaCuspRawEvenMoment 1 ^ 2 * thetaCuspRawEvenMoment 2 -
        10 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2 ^ 2 := by
  have hs := normalizedPrimeArch_firstHankelMinor_scaled_eq_thetaCuspMoments
  rw [thetaCusp_normalized_cubic_eq_raw_div] at hs
  have hq := hs ▸ mul_pos (by norm_num : (0 : ℝ) < 360)
    normalizedPrimeArch_firstHankelMinor_pos_from_stein
  exact (div_pos_iff_of_pos_right (pow_pos (thetaCuspRawEvenMoment_pos 0) 3)).mp hq

/-- The Gaussian aperture balance of the theta-cusp source is strictly positive at aperture `0`. -/
theorem thetaCuspGaussianApertureBalance_zero_pos :
    0 < thetaCuspGaussianApertureBalance 0 := by
  rw [thetaCuspGaussianApertureBalance_zero]
  have h := thetaCusp_raw_cubic_pos
  rw [thetaCusp_raw_cubic_eq_threeTemperatureMeanBalance] at h
  exact (mul_pos_iff_of_pos_left (mul_pos (mul_pos (thetaCuspRawEvenMoment_pos 0)
    (thetaCuspRawEvenMoment_pos 1)) (thetaCuspRawEvenMoment_pos 2))).mp h

/-- The central cumulant discriminant of the theta-cusp source is strictly positive. -/
theorem thetaCuspCentralCumulantDiscriminant_pos :
    0 < thetaCuspCentralCumulantDiscriminant :=
  thetaCuspCentralCumulantDiscriminant_pos_iff_apertureBalance_zero_pos.mpr
    thetaCuspGaussianApertureBalance_zero_pos

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

/-- The upper adjacent ratio separation as a lower size-biased susceptibility bound. -/
theorem thetaCuspSizeBiasedSusceptibility_one_lower :
    5 * thetaCuspSizeBiasedMean 1 ^ (2 : ℕ) ≤ 9 * thetaCuspSizeBiasedSusceptibility 1 :=
  thetaCuspUpperAdjacentRatioSeparation_iff_susceptibility_lower.mp
    thetaCuspUpperAdjacentRatioSeparation_holds

/-- The fluctuation-response window of the two low theta gates. -/
theorem thetaCuspSizeBiasedSusceptibilityWindow_holds : ThetaCuspSizeBiasedSusceptibilityWindow :=
  thetaCuspSizeBiasedSusceptibilityWindow_iff_ratioSplit.mpr
    ⟨thetaCuspUpperAdjacentRatioSeparation_holds, thetaCuspRelaxedFourthMomentConcentration_holds⟩

/-- The Pearson chi-square window of the two low theta gates. -/
theorem thetaCuspSizeBiasPearsonWindow_holds : ThetaCuspSizeBiasPearsonWindow :=
  thetaCuspSizeBiasPearsonWindow_iff_susceptibilityWindow.mpr
    thetaCuspSizeBiasedSusceptibilityWindow_holds

/-- The linear size-bias mean-lift window of the two low theta gates. -/
theorem thetaCuspSizeBiasMeanLiftWindow_holds : ThetaCuspSizeBiasMeanLiftWindow :=
  thetaCuspSizeBiasMeanLiftWindow_iff_susceptibilityWindow.mpr
    thetaCuspSizeBiasedSusceptibilityWindow_holds

/-! ## Radial Born–Witten forms of the Stein bounds -/

/-- `BW_{j,1,1} = w_{j+1}`: the `k = 1` radial Born–Witten moments are shifted Ward moments. -/
theorem thetaCuspBornWittenRadialRawMoment_one_eq_firstAtomWardMoment (j : ℕ) :
    thetaCuspBornWittenRadialRawMoment j 1 1 = thetaCuspFirstAtomWardMoment (j + 1) :=
  mul_left_cancel₀ (by positivity : (2 * Real.pi) ≠ 0)
    ((thetaCuspAtomRawEvenMoment_eq_radialBornWittenRawMoment j 1 1).symm.trans
      (thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment (j + 1)))

/-- Radial relaxed ratio bound `16 (r BW₀)(r BW₂) ≤ 45 BW₁²` on the `k = 0` fiber. -/
theorem thetaCuspFirstRadial_relaxed :
    16 * ((3005 / 2997 : ℝ) * thetaCuspBornWittenRadialRawMoment 0 0 1) *
        ((3005 / 2997 : ℝ) * thetaCuspBornWittenRadialRawMoment 2 0 1) ≤
      45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ (2 : ℕ) := by
  rw [thetaCuspBornWittenRadialRawMoment_zero_eq_firstAtomWardMoment 0,
    thetaCuspBornWittenRadialRawMoment_zero_eq_firstAtomWardMoment 1,
    thetaCuspBornWittenRadialRawMoment_zero_eq_firstAtomWardMoment 2]
  exact thetaCuspFirstAtomWardMoment_stein_ratio_bounds.2

/-- Radial upper ratio bound `14 (r BW₁)² ≤ 9 BW₀ BW₂` on the `k = 1` fiber. -/
theorem thetaCuspFirstRadial_upper :
    14 * ((3005 / 2997 : ℝ) * thetaCuspBornWittenRadialRawMoment 1 1 1) ^ (2 : ℕ) ≤
      9 * thetaCuspBornWittenRadialRawMoment 0 1 1 *
        thetaCuspBornWittenRadialRawMoment 2 1 1 := by
  rw [thetaCuspBornWittenRadialRawMoment_one_eq_firstAtomWardMoment 0,
    thetaCuspBornWittenRadialRawMoment_one_eq_firstAtomWardMoment 1,
    thetaCuspBornWittenRadialRawMoment_one_eq_firstAtomWardMoment 2]
  exact thetaCuspFirstAtomWardMoment_stein_ratio_bounds.1

/-- The single-Gibbs relaxed certificate. -/
theorem thetaCuspFirstAtomSingleGibbsRelaxedCertificate_holds :
    ThetaCuspFirstAtomSingleGibbsRelaxedCertificate :=
  thetaCuspFirstAtomSingleGibbsRelaxedCertificate_iff.mpr thetaCuspFirstRadial_relaxed

/-- Relaxed radial bound with a single factor of `r`. -/
theorem thetaCuspFirstRadial_relaxedSingleFactor :
    16 * (3005 / 2997 : ℝ) * thetaCuspBornWittenRadialRawMoment 0 0 1 *
        thetaCuspBornWittenRadialRawMoment 2 0 1 ≤
      45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ (2 : ℕ) :=
  thetaCuspFirstRadial_relaxedSingleFactor_of_squaredFactor (by norm_num)
    thetaCuspFirstRadial_relaxed

/-- Single-loss relaxed first-atom bound `16 r a₀ a₂ ≤ 45 a₁²`. -/
theorem thetaCusp_firstAtom_relaxed_singleLoss :
    16 * (3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 0 1 * thetaCuspAtomRawEvenMoment 2 1 ≤
      45 * thetaCuspAtomRawEvenMoment 1 1 ^ 2 :=
  thetaCusp_firstAtom_relaxed_singleLoss_of_radial thetaCuspFirstRadial_relaxedSingleFactor

/-- Single-loss upper first-atom bound `14 r a₂² ≤ 9 a₁ a₃`; `r ≥ 1` absorbs one factor. -/
theorem thetaCusp_firstAtom_upper_singleLoss :
    14 * (3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 2 1 ^ 2 ≤
      9 * thetaCuspAtomRawEvenMoment 1 1 * thetaCuspAtomRawEvenMoment 3 1 := by
  apply thetaCusp_firstAtom_upper_singleLoss_of_radial
  have h := thetaCuspFirstRadial_upper
  nlinarith [sq_nonneg (thetaCuspBornWittenRadialRawMoment 1 1 1)]

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
