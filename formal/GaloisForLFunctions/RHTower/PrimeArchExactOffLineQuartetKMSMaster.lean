import GaloisForLFunctions.RHTower.XiThermalOffLineChargeSelfCubicBound
import GaloisForLFunctions.RHTower.XiOffLineQuartetThermalOrientationBound
import GaloisForLFunctions.RHTower.XiThermalPrimeSquareEnergySpectrum
import GaloisForLFunctions.RHTower.XiThermalProjectiveCofinalSection
import GaloisForLFunctions.RHTower.PrimeArchFiniteKMSLocalMomentClosure
import GaloisForLFunctions.RHTower.PrimeArchHausdorffBernsteinKMSRH
import GaloisForLFunctions.RHTower.PrimeArchCountablePassiveResponseEquivalence
import GaloisForLFunctions.RHTower.PrimeArchThetaMorseFisherExponentialEnvelope
import GaloisForLFunctions.RHTower.PrimeArchThetaSingleGibbsCertificateReduction
import GaloisForLFunctions.RHTower.PrimeArchThetaSingleGibbsGammaCoordinate

/-!
# Exact quartet Connes--Born/Witten--KMS ultraviolet--infrared master law

This is the single quantitative master theorem for the continued prime--archimedean route.  The
endpoint source has a certified curvature budget below `93 / 2000`.  Functional-equation and
Schwarz symmetry force an off-line zero to spend that budget in four equal charges, producing the
strict squared-height gap `7907 / 93`.  Hence every exact quartet-admissible central frequency band
is zero-free and the continued source response is unconditionally anti-Herglotz there.

The same quartet budget suppresses the transverse thermal defect cubically in the completed
endpoint charge.  In particular the absolute source gap is below `1 / 150000`, independently of
RH.

The only remaining response condition is the one-sided positive-frequency tail.  It is equivalent
to vanishing of the thermal orientation energy, saturation of the explicit theta Born--Witten
source value, selection of that value by the KMS limit, Connes reflection positivity, a
self-adjoint vacuum realization, boundedness of the faithful cold partition, one uniform bound on
all sufficiently cold finite thermal systems, and RH.  The rational radius `218 / 25` is
admissible.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

/-- **Exact quartet ultraviolet--infrared master theorem.**

The clauses before the equivalence chain are unconditional consequences of the endpoint source.
The chain identifies the sole remaining ultraviolet orientation datum in response, thermal,
thermodynamic-limit, reflection-positive, spectral, and divisor language. -/
theorem primeArchExactQuartetConnesBornWittenKMSMaster
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R) :
    xiEndpointCompletedCurvature < 93 / 2000 ∧
    0 ≤ xiEndpointOffLineCharge ∧
    xiEndpointOffLineCharge ≤ xiEndpointCompletedCurvature ∧
    (∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 →
      4 ≤ xiEndpointOffLineCharge * ((q.1 : ℂ).im ^ (2 : ℕ) + 1) ∧
      4 ≤ xiEndpointCompletedCurvature * ((q.1 : ℂ).im ^ (2 : ℕ) + 1) ∧
      7907 / 93 < (q.1 : ℂ).im ^ (2 : ℕ)) ∧
    (∀ z : ℂ, 0 < z.im → |z.re| ≤ R → XiC z ≠ 0) ∧
    (∀ z : ℂ, 0 < z.im → z.im < 1 / 2 → |z.re| ≤ R →
      (continuedPrimeArchSourceRelativeTrace z).im ≤ 0) ∧
    (∀ z : ℂ, 0 < z.im →
      closure (Set.range fun N =>
        (HTGeometry.finiteTransitionPassiveResponse
          (HTGeometry.finiteKMSWightmanTransitionIntensity 0
            (HTGeometry.universalOneStateKMSEnergy N)
            (HTGeometry.universalOneStateKMSAmplitude N))
          (HTGeometry.universalOneStateKMSEnergy N) z).im) = Set.Iic 0) ∧
    Tendsto (fun N => xiThermalTruncation N 0) atTop
      (nhds (normalizedPrimeArchMoment 0)) ∧
    xiThermalProjectiveColdPartition 0 = normalizedPrimeArchMoment 0 ∧
    (∀ N, FiniteKMSWightmanMomentSequence
      (xiThermalProjectiveTruncation N)) ∧
    Tendsto xiThermalProjectiveTruncation atTop
      (nhds xiThermalProjectiveMoment) ∧
    Tendsto xiThermalProjectiveColdTruncation atTop
      (nhds xiThermalProjectiveColdPartition) ∧
    0 < xiThermalCubicReciprocalMass ∧
    xiThermalSecondMoment - normalizedPrimeArchMoment 1 ≤
      4 * xiRightTransverseSup ^ (2 : ℕ) * xiThermalCubicReciprocalMass ∧
    (Nonempty XiRightZeroCopy →
      (((1 + Real.sqrt
          ((xiThermalSecondMoment - normalizedPrimeArchMoment 1) /
            xiThermalCubicReciprocalMass) : ℝ) : EReal)) ≤
        LSeries.abscissaOfAbsConv
          squarePrimeWindowPositiveExcessDirichletCoefficient ∧
      (((1 + 2 * Real.sqrt
          ((xiThermalSecondMoment - normalizedPrimeArchMoment 1) /
            xiThermalCubicReciprocalMass) : ℝ) : EReal)) ≤
        LSeries.abscissaOfAbsConv
          squarePrimeWindowPositiveExcessSquareDirichletCoefficient) ∧
    xiThermalQuartetRelativeOrientationFactor < 1 / 84 ∧
    xiThermalOrientationEnergy ≤
      xiThermalQuartetRelativeOrientationFactor * xiThermalSecondMoment ∧
    xiThermalOrientationEnergy <
      (1 / 84 : ℝ) * xiThermalSecondMoment ∧
    xiThermalOrientationEnergy ≤ xiThermalOffLineChargeCubicBudget ∧
    xiThermalOffLineChargeCubicBudget ≤ xiThermalExactCubicEndpointBudget ∧
    xiThermalOrientationEnergy ≤ xiThermalExactCubicEndpointBudget ∧
    xiThermalExactCubicEndpointBudget < xiThermalCubicEndpointBudget ∧
    xiThermalCubicEndpointBudget < 1 / 150000 ∧
    xiThermalOrientationEnergy < 1 / 150000 ∧
    (0 ≤ xiThermalSecondMoment - normalizedPrimeArchMoment 1 ∧
      xiThermalSecondMoment - normalizedPrimeArchMoment 1 < 1 / 150000) ∧
    (83 / 84 : ℝ) * xiThermalSecondMoment <
      thetaCuspBornWittenQuadraticSource ∧
    xiThermalSecondMoment <
      (84 / 83 : ℝ) * thetaCuspBornWittenQuadraticSource ∧
    xiThermalSecondMoment - xiThermalOrientationEnergy =
      thetaCuspBornWittenQuadraticSource ∧
    thetaCuspBornWittenQuadraticSource ≤ xiThermalSecondMoment ∧
    (ContinuedPrimeArchPositiveFrequencyAbove R ↔
      xiThermalOrientationEnergy = 0) ∧
    (xiEndpointOffLineCharge = 0 ↔
      xiThermalOrientationEnergy = 0) ∧
    (xiThermalOrientationEnergy = 0 ↔
      xiThermalSecondMoment = thetaCuspBornWittenQuadraticSource) ∧
    (xiThermalSecondMoment = thetaCuspBornWittenQuadraticSource ↔
      Tendsto (fun N => xiThermalTruncation N 1) atTop
        (nhds thetaCuspBornWittenQuadraticSource)) ∧
    (Tendsto (fun N => xiThermalTruncation N 1) atTop
        (nhds thetaCuspBornWittenQuadraticSource) ↔
      PrimeArchComplexReflectionPositiveGram) ∧
    (PrimeArchComplexReflectionPositiveGram ↔
      PrimeArchSelfAdjointVacuumRealization) ∧
    (PrimeArchSelfAdjointVacuumRealization ↔
      ∃ C : ℝ, ∀ᶠ k : ℕ in atTop,
        xiThermalProjectiveColdPartition k ≤ C) ∧
    ((∃ C : ℝ, ∀ᶠ k : ℕ in atTop,
        xiThermalProjectiveColdPartition k ≤ C) ↔
      ∃ C : ℝ, ∀ᶠ k : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        xiThermalProjectiveColdTruncation N k ≤ C) ∧
    ((∃ C : ℝ, ∀ᶠ k : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        xiThermalProjectiveColdTruncation N k ≤ C) ↔
      RiemannHypothesis) ∧
    (PrimeArchFinitePositiveAtomicLocalMomentClosure ↔
      PrimeArchFiniteKMSWightmanLocalMomentClosure) ∧
    (PrimeArchFiniteKMSWightmanLocalMomentClosure ↔
      RiemannHypothesis) ∧
    (PrimeArchHausdorffMomentDifferencesNonnegative ↔
      RiemannHypothesis) ∧
    ThetaCuspFirstAtomMorseFisherExponentialEnvelopeMaster ∧
    ThetaCuspFirstAtomSingleGibbsCertificateMaster ∧
    (∀ m : ℕ,
      thetaCuspLiouvilleGibbsMoment m 1 =
        (1 / (2 : ℝ) ^ (m + 1)) *
          ∫ t : ℝ in Set.Ioi 1,
            thetaCuspFirstAtomSingleGibbsGammaIntegrand m t) ∧
    (PrimeArchGaussianRatFiniteKMSPassiveClosureAbove R ↔
      RiemannHypothesis) ∧
    (Tendsto (fun j : ℕ => xiThermalProjectiveColdTruncation j j)
      atTop atTop ↔ ¬RiemannHypothesis) ∧
    ((∃ C : ℝ, ∃ᶠ j : ℕ in atTop,
        xiThermalProjectiveColdTruncation j j ≤ C) ↔
      RiemannHypothesis) := by
  have hhigh : ContinuedPrimeArchPositiveFrequencyAbove R ↔ RiemannHypothesis :=
    continuedPrimeArchPositiveFrequencyAbove_iff_rh_of_exactOffLineQuartetBand
      R hband
  have henergy : xiThermalOrientationEnergy = 0 ↔ RiemannHypothesis :=
    xiThermalOrientationEnergy_eq_zero_iff_rh
  have hsource :
      xiThermalSecondMoment = thetaCuspBornWittenQuadraticSource ↔
        RiemannHypothesis :=
    xiThermalSecondMoment_eq_bornWittenSource_iff_rh
  have hlimit :
      Tendsto (fun N => xiThermalTruncation N 1) atTop
          (nhds thetaCuspBornWittenQuadraticSource) ↔ RiemannHypothesis :=
    tendsto_xiThermalTruncation_one_bornWittenSource_iff_rh
  have hgram : PrimeArchComplexReflectionPositiveGram ↔ RiemannHypothesis :=
    primeArchComplexReflectionPositiveGram_iff_riemannHypothesis
  have hvacuum : PrimeArchSelfAdjointVacuumRealization ↔ RiemannHypothesis :=
    primeArchSelfAdjointVacuumRealization_iff_riemannHypothesis
  have hcold : RiemannHypothesis ↔
      ∃ C : ℝ, ∀ᶠ k : ℕ in atTop,
        xiThermalProjectiveColdPartition k ≤ C :=
    riemannHypothesis_iff_exists_eventually_bounded_thermalProjectiveColdPartition
  have hfiniteCold : RiemannHypothesis ↔
      ∃ C : ℝ, ∀ᶠ k : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        xiThermalProjectiveColdTruncation N k ≤ C :=
    riemannHypothesis_iff_exists_eventually_cold_eventually_thermodynamic_bound
  refine ⟨xiEndpointCompletedCurvature_lt_ninetyThree_over_twoThousand,
    xiEndpointOffLineCharge_nonneg, xiEndpointOffLineCharge_le_curvature,
    ?_, ?_, ?_,
    (fun z hz => HTGeometry.closure_range_universalOneStateKMSPassiveResponse_im hz),
    tendsto_xiThermalTruncation_zero_source,
    xiThermalProjectiveColdPartition_zero_eq_source,
    finiteKMSWightmanMomentSequence_xiThermalProjectiveTruncation,
    tendsto_xiThermalProjectiveTruncation,
    tendsto_xiThermalProjectiveColdTruncation,
    xiThermalCubicReciprocalMass_pos,
    xiThermalSourceGap_le_intrinsicTransverseCubicBudget, ?_,
    xiThermalQuartetRelativeOrientationFactor_lt_one_eightyFourth,
    xiThermalOrientationEnergy_le_quartetRelativeFactor_secondMoment,
    xiThermalOrientationEnergy_lt_one_eightyFourth_secondMoment,
    xiThermalOrientationEnergy_le_offLineChargeCubicBudget,
    xiThermalOffLineChargeCubicBudget_le_exactCubicEndpointBudget,
    xiThermalOrientationEnergy_le_exactCubicEndpointBudget,
    xiThermalExactCubicEndpointBudget_lt_cubicEndpointBudget,
    xiThermalCubicEndpointBudget_lt_one_over_oneHundredFiftyThousand,
    xiThermalOrientationEnergy_lt_one_over_oneHundredFiftyThousand,
    xiThermalSecondMoment_source_absoluteGap,
    eightyThree_over_eightyFour_thermalSecondMoment_lt_bornWittenSource,
    xiThermalSecondMoment_lt_eightyFour_over_eightyThree_bornWittenSource,
    xiThermalSecondMoment_sub_orientationEnergy_eq_bornWittenSource,
    thetaCuspBornWittenQuadraticSource_le_thermalSecondMoment,
    hhigh.trans henergy.symm,
    xiEndpointOffLineCharge_eq_zero_iff_rh.trans henergy.symm,
    henergy.trans hsource.symm,
    hsource.trans hlimit.symm, hlimit.trans hgram.symm,
    hgram.trans hvacuum.symm, hvacuum.trans hcold,
    hcold.symm.trans hfiniteCold, hfiniteCold.symm,
    primeArchFinitePositiveAtomicLocalMomentClosure_iff_finiteKMSLocalMomentClosure,
    primeArchFiniteKMSWightmanLocalMomentClosure_iff_riemannHypothesis,
    primeArchHausdorffMomentDifferencesNonnegative_iff_riemannHypothesis,
    thetaCuspFirstAtomMorseFisherExponentialEnvelopeMaster,
    thetaCuspFirstAtomSingleGibbsCertificateMaster,
    thetaCuspLiouvilleGibbsMoment_eq_singleGammaIntegral,
    primeArchGaussianRatFiniteKMSPassiveClosureAbove_iff_riemannHypothesis R hband,
    thermalProjectiveCofinalSection_tendsto_atTop_iff_not_riemannHypothesis
      id id tendsto_id tendsto_id,
    riemannHypothesis_iff_exists_frequently_bounded_thermalProjectiveDiagonal.symm⟩
  · intro q hoff
    exact ⟨four_le_offLineCharge_mul_one_add_im_sq q hoff,
      four_le_endpointCurvature_mul_one_add_im_sq_of_offLine q hoff,
      xiZeroCopy_offLine_sevenThousandNineHundredSeven_over_ninetyThree_lt_im_sq
        q hoff⟩
  · intro z hzIm hzRe
    exact XiC_ne_zero_of_upperHalf_exactOffLineQuartetBand
      R hband z hzIm hzRe
  · intro z hzIm hzHalf hzRe
    exact
      continuedPrimeArchSourceRelativeTrace_im_nonpos_exactOffLineQuartetBand
        R hband z hzIm hzHalf hzRe
  · intro hne
    exact ⟨
      one_add_sqrt_normalized_xiThermalSourceGap_le_squarePrimeWindowPositiveExcess_abscissa
        hne,
      one_add_two_mul_sqrt_normalized_xiThermalSourceGap_le_squarePrimeWindowPositiveExcessSquare_abscissa
        hne⟩

/-- **Explicit master theorem at the certified rational radius.**  The central band
`|Re z| ≤ 218 / 25` and all quantitative clauses are unconditional; the sole remaining response
condition is the positive-frequency tail above `218 / 25`. -/
theorem primeArchExactQuartetConnesBornWittenKMSMaster_twoHundredEighteen_twentyFifths :
    xiEndpointCompletedCurvature < 93 / 2000 ∧
    0 ≤ xiEndpointOffLineCharge ∧
    xiEndpointOffLineCharge ≤ xiEndpointCompletedCurvature ∧
    (∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 →
      4 ≤ xiEndpointOffLineCharge * ((q.1 : ℂ).im ^ (2 : ℕ) + 1) ∧
      4 ≤ xiEndpointCompletedCurvature * ((q.1 : ℂ).im ^ (2 : ℕ) + 1) ∧
      7907 / 93 < (q.1 : ℂ).im ^ (2 : ℕ)) ∧
    (∀ z : ℂ, 0 < z.im → |z.re| ≤ 218 / 25 → XiC z ≠ 0) ∧
    (∀ z : ℂ, 0 < z.im → z.im < 1 / 2 → |z.re| ≤ 218 / 25 →
      (continuedPrimeArchSourceRelativeTrace z).im ≤ 0) ∧
    (∀ z : ℂ, 0 < z.im →
      closure (Set.range fun N =>
        (HTGeometry.finiteTransitionPassiveResponse
          (HTGeometry.finiteKMSWightmanTransitionIntensity 0
            (HTGeometry.universalOneStateKMSEnergy N)
            (HTGeometry.universalOneStateKMSAmplitude N))
          (HTGeometry.universalOneStateKMSEnergy N) z).im) = Set.Iic 0) ∧
    Tendsto (fun N => xiThermalTruncation N 0) atTop
      (nhds (normalizedPrimeArchMoment 0)) ∧
    xiThermalProjectiveColdPartition 0 = normalizedPrimeArchMoment 0 ∧
    (∀ N, FiniteKMSWightmanMomentSequence
      (xiThermalProjectiveTruncation N)) ∧
    Tendsto xiThermalProjectiveTruncation atTop
      (nhds xiThermalProjectiveMoment) ∧
    Tendsto xiThermalProjectiveColdTruncation atTop
      (nhds xiThermalProjectiveColdPartition) ∧
    0 < xiThermalCubicReciprocalMass ∧
    xiThermalSecondMoment - normalizedPrimeArchMoment 1 ≤
      4 * xiRightTransverseSup ^ (2 : ℕ) * xiThermalCubicReciprocalMass ∧
    (Nonempty XiRightZeroCopy →
      (((1 + Real.sqrt
          ((xiThermalSecondMoment - normalizedPrimeArchMoment 1) /
            xiThermalCubicReciprocalMass) : ℝ) : EReal)) ≤
        LSeries.abscissaOfAbsConv
          squarePrimeWindowPositiveExcessDirichletCoefficient ∧
      (((1 + 2 * Real.sqrt
          ((xiThermalSecondMoment - normalizedPrimeArchMoment 1) /
            xiThermalCubicReciprocalMass) : ℝ) : EReal)) ≤
        LSeries.abscissaOfAbsConv
          squarePrimeWindowPositiveExcessSquareDirichletCoefficient) ∧
    xiThermalQuartetRelativeOrientationFactor < 1 / 84 ∧
    xiThermalOrientationEnergy ≤
      xiThermalQuartetRelativeOrientationFactor * xiThermalSecondMoment ∧
    xiThermalOrientationEnergy <
      (1 / 84 : ℝ) * xiThermalSecondMoment ∧
    xiThermalOrientationEnergy ≤ xiThermalOffLineChargeCubicBudget ∧
    xiThermalOffLineChargeCubicBudget ≤ xiThermalExactCubicEndpointBudget ∧
    xiThermalOrientationEnergy ≤ xiThermalExactCubicEndpointBudget ∧
    xiThermalExactCubicEndpointBudget < xiThermalCubicEndpointBudget ∧
    xiThermalCubicEndpointBudget < 1 / 150000 ∧
    xiThermalOrientationEnergy < 1 / 150000 ∧
    (0 ≤ xiThermalSecondMoment - normalizedPrimeArchMoment 1 ∧
      xiThermalSecondMoment - normalizedPrimeArchMoment 1 < 1 / 150000) ∧
    (83 / 84 : ℝ) * xiThermalSecondMoment <
      thetaCuspBornWittenQuadraticSource ∧
    xiThermalSecondMoment <
      (84 / 83 : ℝ) * thetaCuspBornWittenQuadraticSource ∧
    xiThermalSecondMoment - xiThermalOrientationEnergy =
      thetaCuspBornWittenQuadraticSource ∧
    thetaCuspBornWittenQuadraticSource ≤ xiThermalSecondMoment ∧
    (ContinuedPrimeArchPositiveFrequencyAbove (218 / 25) ↔
      xiThermalOrientationEnergy = 0) ∧
    (xiEndpointOffLineCharge = 0 ↔
      xiThermalOrientationEnergy = 0) ∧
    (xiThermalOrientationEnergy = 0 ↔
      xiThermalSecondMoment = thetaCuspBornWittenQuadraticSource) ∧
    (xiThermalSecondMoment = thetaCuspBornWittenQuadraticSource ↔
      Tendsto (fun N => xiThermalTruncation N 1) atTop
        (nhds thetaCuspBornWittenQuadraticSource)) ∧
    (Tendsto (fun N => xiThermalTruncation N 1) atTop
        (nhds thetaCuspBornWittenQuadraticSource) ↔
      PrimeArchComplexReflectionPositiveGram) ∧
    (PrimeArchComplexReflectionPositiveGram ↔
      PrimeArchSelfAdjointVacuumRealization) ∧
    (PrimeArchSelfAdjointVacuumRealization ↔
      ∃ C : ℝ, ∀ᶠ k : ℕ in atTop,
        xiThermalProjectiveColdPartition k ≤ C) ∧
    ((∃ C : ℝ, ∀ᶠ k : ℕ in atTop,
        xiThermalProjectiveColdPartition k ≤ C) ↔
      ∃ C : ℝ, ∀ᶠ k : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        xiThermalProjectiveColdTruncation N k ≤ C) ∧
    ((∃ C : ℝ, ∀ᶠ k : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        xiThermalProjectiveColdTruncation N k ≤ C) ↔
      RiemannHypothesis) ∧
    (PrimeArchFinitePositiveAtomicLocalMomentClosure ↔
      PrimeArchFiniteKMSWightmanLocalMomentClosure) ∧
    (PrimeArchFiniteKMSWightmanLocalMomentClosure ↔
      RiemannHypothesis) ∧
    (PrimeArchHausdorffMomentDifferencesNonnegative ↔
      RiemannHypothesis) ∧
    ThetaCuspFirstAtomMorseFisherExponentialEnvelopeMaster ∧
    ThetaCuspFirstAtomSingleGibbsCertificateMaster ∧
    (∀ m : ℕ,
      thetaCuspLiouvilleGibbsMoment m 1 =
        (1 / (2 : ℝ) ^ (m + 1)) *
          ∫ t : ℝ in Set.Ioi 1,
            thetaCuspFirstAtomSingleGibbsGammaIntegrand m t) ∧
    (PrimeArchGaussianRatFiniteKMSPassiveClosure ↔
      RiemannHypothesis) ∧
    (Tendsto (fun j : ℕ => xiThermalProjectiveColdTruncation j j)
      atTop atTop ↔ ¬RiemannHypothesis) ∧
    ((∃ C : ℝ, ∃ᶠ j : ℕ in atTop,
        xiThermalProjectiveColdTruncation j j ≤ C) ↔
      RiemannHypothesis) :=
  primeArchExactQuartetConnesBornWittenKMSMaster
    (218 / 25) xiOffLineQuartetAccretiveBand_twoHundredEighteen_twentyFifths

end

end RHTower
