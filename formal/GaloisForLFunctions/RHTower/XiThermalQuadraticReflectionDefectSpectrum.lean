import GaloisForLFunctions.RHTower.PrimeArchThermalKrylovEquivalence
import GaloisForLFunctions.RHTower.PrimeArchConnesReflectionMain
import GaloisForLFunctions.RHTower.XiProjectiveReflectionSourceTemperatureSpectrum
import GaloisForLFunctions.RHTower.XiThermalSourceRelativeGapBound

/-!
# Projective--thermal quadratic reflection master spectrum

The projective source--temperature spectrum and the explicit finite KMS construction meet at one
critical master theorem.  Finite KMS realizability, convergence to the canonical positive thermal
second moment, and the source lower bound are unconditional.  At the zero fibre, the fixed-window
prime--Gamma abscissa, projective and Born radii, endpoint defect energy, reciprocal-square
reflection energy, quadratic thermal/source equality, its reverse inequality, the one-coordinate
thermodynamic source limit, and RH are equivalent.

The exact reciprocal-square reflection energy is four times the transverse orientation energy.
Thus the single missing RH-bearing estimate is the reverse of the unconditional source lower bound.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Squared conjugation defect of the reciprocal-square Xi spectrum. -/
def xiThermalSquareReflectionDefectEnergy : ℝ :=
  ∑' q : XiZeroCopy,
    ‖xiZeroCopyReciprocalSquare q -
      (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q)‖ ^ 2

/-- Pointwise conversion from conjugation distance to imaginary-square mass. -/
lemma norm_sub_conj_sq_eq_four_im_sq (z : ℂ) :
    ‖z - (starRingEnd ℂ) z‖ ^ 2 = 4 * z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.conj_re, Complex.conj_im]
  ring

/-- The reciprocal-square reflection energy is summable. -/
theorem summable_xiThermalSquareReflectionDefectEnergy :
    Summable (fun q : XiZeroCopy =>
      ‖xiZeroCopyReciprocalSquare q -
        (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q)‖ ^ 2) := by
  apply summable_xiThermalOrientationTerm.mul_left 4 |>.congr
  intro q
  exact (norm_sub_conj_sq_eq_four_im_sq _).symm

/-- The reciprocal-square reflection energy is exactly four times the transverse thermal
orientation energy. -/
theorem xiThermalSquareReflectionDefectEnergy_eq_four_mul_orientationEnergy :
    xiThermalSquareReflectionDefectEnergy = 4 * xiThermalOrientationEnergy := by
  rw [xiThermalSquareReflectionDefectEnergy, xiThermalOrientationEnergy]
  simp_rw [norm_sub_conj_sq_eq_four_im_sq]
  exact tsum_mul_left

/-- Vanishing of the reciprocal-square reflection energy is exactly RH. -/
theorem xiThermalSquareReflectionDefectEnergy_eq_zero_iff_rh :
    xiThermalSquareReflectionDefectEnergy = 0 ↔ RiemannHypothesis := by
  rw [xiThermalSquareReflectionDefectEnergy_eq_four_mul_orientationEnergy]
  constructor
  · intro h
    have henergy : xiThermalOrientationEnergy = 0 := by nlinarith
    exact xiThermalOrientationEnergy_eq_zero_iff_rh.mp henergy
  · intro hRH
    rw [xiThermalOrientationEnergy_eq_zero_iff_rh.mpr hRH]
    norm_num

/-- The anti-Hermitian part of the squared reciprocal kernel is the diagonal reciprocal-square
reflection defect. -/
theorem xiReciprocalSquareKernel_sub_adjoint_eq_diagMul :
    HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1 -
        HilbertSchmidt.hsAdjoint
          (HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1) =
      HilbertSchmidt.diagMul (fun q : XiZeroCopy =>
        xiZeroCopyReciprocalSquare q -
          (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q)) := by
  rw [xiReciprocalDiagonalKernel, HilbertSchmidt.hsPow_diagMul]
  funext p
  rcases p with ⟨q, r⟩
  by_cases h : q = r
  · subst r
    simp only [Pi.sub_apply, HilbertSchmidt.hsAdjoint,
      HilbertSchmidt.diagMul, if_pos]
    rw [xiZeroCopyReciprocalSquare]
  · have h' : r ≠ q := Ne.symm h
    simp [HilbertSchmidt.hsAdjoint, HilbertSchmidt.diagMul, h, h']

/-- The reciprocal-square reflection energy is exactly the Hilbert--Schmidt energy of the
anti-Hermitian part of the squared reciprocal kernel. -/
theorem xiReciprocalSquareKernel_adjointDefect_hsNormSq_eq_reflectionEnergy :
    HilbertSchmidt.hsNormSq
        (HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1 -
          HilbertSchmidt.hsAdjoint
            (HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1)) =
      xiThermalSquareReflectionDefectEnergy := by
  rw [xiReciprocalSquareKernel_sub_adjoint_eq_diagMul,
    HilbertSchmidt.hsNormSq_diagMul_infinite,
    xiThermalSquareReflectionDefectEnergy]

/-- **Quantitative static operator reflection law.**  The Hilbert--Schmidt/holomorphic-trace
excess is exactly one half of the Hilbert--Schmidt energy of the squared kernel's anti-Hermitian
part. -/
theorem xiReciprocalKernel_normTraceGap_eq_half_adjointDefect :
    HilbertSchmidt.hsNormSq
          (HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1) -
        (∑' q : XiZeroCopy,
          HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 3 (q, q)).re =
      (1 / 2 : ℝ) *
        HilbertSchmidt.hsNormSq
          (HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1 -
            HilbertSchmidt.hsAdjoint
              (HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1)) := by
  rw [xiReciprocalSquareKernel_adjointDefect_hsNormSq_eq_reflectionEnergy,
    xiThermalSquareReflectionDefectEnergy_eq_four_mul_orientationEnergy]
  have hgap :=
    xiReciprocalKernel_hsNormSq_sub_reTrace_four_eq_two_orientationEnergy
  linarith

/-- **Projective--thermal source master spectrum.**

The scale-resolved clauses identify the fixed-window source abscissa, projective radius, Born
temperature radius, and Xi half-plane bound, and transport that radius into the endpoint-energy
budget.  The next clauses are unconditional: every finite truncation is a KMS/Wightman moment
system, its second moment converges to the canonical positive thermal value, the continued
prime--Gamma source moment is a lower bound, and the operator norm--trace excess is one half of
the anti-Hermitian Hilbert--Schmidt energy.  The final clauses say that all displayed critical
conditions have one common zero fibre.

In particular, the only additional scalar estimate required for RH is the reverse of either
unconditional value inequality: `xiThermalSecondMoment ≤ normalizedPrimeArchMoment 1`, or the
equivalent Hilbert--Schmidt norm versus real fourth-trace inequality. -/
theorem xiProjectiveThermalSourceMasterSpectrum
    {L alpha : ℝ} (hL : 0 < L) (halpha : 0 ≤ alpha)
    (halphaHalf : alpha ≤ 1 / 2) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    let sourceBound :=
      LSeries.abscissaOfAbsConv
          (xiRectangularPrimeGammaTailNegativeDirichletCoefficient L N) ≤
        ((1 + alpha : ℝ) : EReal)
    let sourceCritical :=
      LSeries.abscissaOfAbsConv
          (xiRectangularPrimeGammaTailNegativeDirichletCoefficient L N) ≤
        ((1 : ℝ) : EReal)
    (sourceBound ↔ xiProjectiveReflectionRadius ≤ alpha) ∧
    (sourceBound ↔ xiBornReflectionRadius ≤ alpha) ∧
    (sourceBound ↔ XiZeroHalfPlaneBound alpha) ∧
    (sourceBound →
      xiEndpointReflectionDefectEnergy ≤ xiProjectiveEndpointBudget alpha) ∧
    xiEndpointReflectionDefectEnergy ≤
      xiProjectiveEndpointBudget xiProjectiveReflectionRadius ∧
    xiEndpointReflectionDefectEnergy <
      (xiEndpointCompletedCurvature /
        (1 - xiEndpointCompletedCurvature)) *
          xiEndpointCompletedCurvature ∧
    xiRawReciprocalHermitianMass <
      ((2 - xiEndpointCompletedCurvature) /
        (2 * (1 - xiEndpointCompletedCurvature))) *
          xiEndpointCompletedCurvature ∧
    (∀ M, FiniteKMSWightmanMomentSequence (xiThermalTruncation M)) ∧
    Tendsto (fun M => xiThermalTruncation M 1) atTop
      (nhds xiThermalSecondMoment) ∧
    normalizedPrimeArchMoment 1 ≤ xiThermalSecondMoment ∧
    normalizedPrimeArchMoment 1 = thetaCuspBornWittenQuadraticSource ∧
    0 < thetaCuspBornWittenQuadraticSource ∧
    xiEndpointCompletedCurvature < 2 / 43 ∧
    xiThermalRelativeOrientationFactor < 1 / 20 ∧
    xiThermalRelativeOrientationFactor < 32 / 49 ∧
    xiThermalOrientationEnergy ≤
      xiThermalRelativeOrientationFactor * xiThermalSecondMoment ∧
    xiThermalOrientationEnergy <
      (1 / 20 : ℝ) * xiThermalSecondMoment ∧
    (1 - xiThermalRelativeOrientationFactor) * xiThermalSecondMoment ≤
      thetaCuspBornWittenQuadraticSource ∧
    (19 / 20 : ℝ) * xiThermalSecondMoment <
      thetaCuspBornWittenQuadraticSource ∧
    xiThermalSecondMoment ≤
      thetaCuspBornWittenQuadraticSource /
        (1 - xiThermalRelativeOrientationFactor) ∧
    thetaCuspBornWittenQuadraticSource /
        (1 - xiThermalRelativeOrientationFactor) <
      (20 / 19 : ℝ) * thetaCuspBornWittenQuadraticSource ∧
    xiThermalSecondMoment <
      (20 / 19 : ℝ) * thetaCuspBornWittenQuadraticSource ∧
    HilbertSchmidt.hsNormSq
          (HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1) -
        (∑' q : XiZeroCopy,
          HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 3 (q, q)).re =
      (1 / 2 : ℝ) *
        HilbertSchmidt.hsNormSq
          (HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1 -
            HilbertSchmidt.hsAdjoint
              (HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1)) ∧
    (sourceCritical ↔ xiProjectiveReflectionRadius = 0) ∧
    (sourceCritical ↔ xiBornReflectionRadius = 0) ∧
    (sourceCritical ↔ xiEndpointReflectionDefectEnergy = 0) ∧
    (sourceCritical ↔ xiThermalOrientationEnergy = 0) ∧
    (sourceCritical ↔ xiThermalSquareReflectionDefectEnergy = 0) ∧
    (sourceCritical ↔
      xiReciprocalSquareHermitianMass = normalizedPrimeArchMoment 1) ∧
    (sourceCritical ↔
      xiReciprocalSquareHermitianMass ≤ normalizedPrimeArchMoment 1) ∧
    (sourceCritical ↔
      ContinuousLinearMap.hsNormSq xiReciprocalSquareOperator =
        normalizedPrimeArchMoment 1) ∧
    (sourceCritical ↔
      ContinuousLinearMap.hsNormSq xiReciprocalSquareOperator ≤
        normalizedPrimeArchMoment 1) ∧
    (sourceCritical ↔
      HilbertSchmidt.hsNormSq
          (HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1) ≤
        (∑' q : XiZeroCopy,
          HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 3 (q, q)).re) ∧
    (sourceCritical ↔
      HilbertSchmidt.hsNormSq
          (HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1) =
        (∑' q : XiZeroCopy,
          HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 3 (q, q)).re) ∧
    (sourceCritical ↔
      xiThermalSecondMoment = normalizedPrimeArchMoment 1) ∧
    (sourceCritical ↔
      xiThermalSecondMoment ≤ normalizedPrimeArchMoment 1) ∧
    (sourceCritical ↔
      Tendsto (fun M => xiThermalTruncation M 1) atTop
        (nhds (normalizedPrimeArchMoment 1))) ∧
    (sourceCritical ↔ PrimeArchEndpointSaturation) ∧
    (sourceCritical ↔ PrimeArchSourceTraceHankelIntNonnegative) ∧
    (sourceCritical ↔ PrimeArchComplexReflectionPositiveGram) ∧
    (sourceCritical ↔ PrimeArchSelfAdjointVacuumRealization) ∧
    (sourceCritical ↔ RiemannHypothesis) := by
  have hscale := xiProjectiveSourceTemperatureMasterSpectrum
    hL halpha halphaHalf hN
  dsimp only at hscale
  obtain ⟨hsourceProjective, hprojectiveBorn, hprojectiveDivisor,
    hbudget, hintrinsic⟩ := hscale
  dsimp only
  have hsourceRH :
      (LSeries.abscissaOfAbsConv
          (xiRectangularPrimeGammaTailNegativeDirichletCoefficient L N) ≤
        ((1 : ℝ) : EReal)) ↔ RiemannHypothesis :=
    (riemannHypothesis_iff_primeGammaTailNegativePart_abscissa_le_one
      hL hN).symm
  have hborn : xiBornReflectionRadius = 0 ↔ RiemannHypothesis := by
    rw [xiBornReflectionRadius_eq_projectiveReflectionRadius]
    exact xiProjectiveReflectionRadius_eq_zero_iff_rh
  refine ⟨hsourceProjective,
    hsourceProjective.trans hprojectiveBorn,
    hsourceProjective.trans hprojectiveDivisor,
    hbudget, hintrinsic,
    xiEndpointDefectEnergy_lt_unconditional_source_factor,
    xiRawMass_lt_unconditional_source_only_factor,
    finiteKMSWightmanMomentSequence_xiThermalTruncation,
    tendsto_xiThermalTruncation_one,
    normalizedPrimeArchMoment_one_le_xiThermalSecondMoment,
    normalizedPrimeArchMoment_one_eq_bornWittenQuadraticSource,
    thetaCuspBornWittenQuadraticSource_pos,
    xiEndpointCompletedCurvature_lt_two_over_fortyThree,
    xiThermalRelativeOrientationFactor_lt_one_twentieth,
    xiThermalRelativeOrientationFactor_lt_thirtyTwo_over_fortyNine,
    xiThermalOrientationEnergy_le_relativeFactor_secondMoment,
    xiThermalOrientationEnergy_lt_one_twentieth_secondMoment,
    relativeFactor_complement_mul_thermalSecondMoment_le_bornWittenSource,
    nineteen_over_twenty_thermalSecondMoment_lt_bornWittenSource,
    xiThermalSecondMoment_le_bornWittenSource_div_relativeFactorComplement,
    bornWittenSource_div_relativeFactorComplement_lt_twenty_over_nineteen,
    xiThermalSecondMoment_lt_twenty_over_nineteen_bornWittenSource,
    xiReciprocalKernel_normTraceGap_eq_half_adjointDefect,
    hsourceRH.trans xiProjectiveReflectionRadius_eq_zero_iff_rh.symm,
    hsourceRH.trans hborn.symm,
    hsourceRH.trans xiEndpointReflectionDefectEnergy_eq_zero_iff_rh.symm,
    hsourceRH.trans xiThermalOrientationEnergy_eq_zero_iff_rh.symm,
    hsourceRH.trans xiThermalSquareReflectionDefectEnergy_eq_zero_iff_rh.symm,
    hsourceRH.trans xiReciprocalSquareHermitianMass_eq_source_iff_rh.symm,
    hsourceRH.trans xiReciprocalSquareHermitianMass_le_source_iff_rh.symm,
    hsourceRH.trans xiReciprocalSquareOperator_hsNormSq_eq_source_iff_rh.symm,
    hsourceRH.trans xiReciprocalSquareOperator_hsNormSq_le_source_iff_rh.symm,
    hsourceRH.trans xiReciprocalKernel_hsNormSq_le_reTrace_four_iff_rh.symm,
    hsourceRH.trans xiReciprocalKernel_hsNormSq_eq_reTrace_four_iff_rh.symm,
    hsourceRH.trans xiThermalSecondMoment_eq_source_iff_rh.symm,
    hsourceRH.trans xiThermalSecondMoment_le_source_iff_rh.symm,
    hsourceRH.trans tendsto_xiThermalTruncation_one_iff_rh.symm,
    hsourceRH.trans primeArchEndpointSaturation_iff_riemannHypothesis.symm,
    hsourceRH.trans primeArchSourceTraceHankelIntNonnegative_iff_riemannHypothesis.symm,
    hsourceRH.trans primeArchComplexReflectionPositiveGram_iff_riemannHypothesis.symm,
    hsourceRH.trans primeArchSelfAdjointVacuumRealization_iff_riemannHypothesis.symm,
    hsourceRH⟩

end

end RHTower
