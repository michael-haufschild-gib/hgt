import GaloisForLFunctions.RHTower.GammaValuationSchurCofinalReducedWeakKernel
import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCriticalInformationCarrierNoGo

/-!
# Cofinal scalar reduction cannot match completed seam moments

P-G88 shows that adjacent-prime Schur depletion must precede inverse incidence to recover the
global weak Gamma covariance.  This file tests the strongest scalar spectral interpretation of
that result: multiply every information-depleted prime-power atom by the cofinal residual factor.

Bertrand control gives a quantitative residual floor.  The resulting first prime-two atom alone
then exceeds the whole completed first moment.  Thus covariance-level inverse incidence is exact,
but its cofinal scalar cannot be transported unchanged to the compact spectral carrier.  Any
surviving transfer must depend on the reciprocal-gap node (or equivalently on prime and depth).
-/

open Real Set Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower.HedenmalmThetaSource

private theorem criticalAdjacent_log_upper_le_two_lower_quantitative (n : ℕ) :
    Real.log (gammaSewnCriticalAdjacentPrime_upper n : ℝ) ≤
      2 * Real.log (gammaSewnCriticalAdjacentPrime_lower n : ℝ) := by
  simpa [gammaSewnCriticalAdjacentPrime_lower,
    gammaSewnCriticalAdjacentPrime_upper, RHTower.xiMassNthPrimeLogHeight] using
      RHTower.xiMassNthPrimeLogHeight_succ_le_two_mul n

theorem gammaSewnCriticalAdjacentPrime_complementaryFisher_le_four_fifths_total
    (e n : ℕ) (s : Fin 6) :
    RHTower.gammaSewnFourRateComplementaryFisher
        (gammaSewnOrderedPrimeDepthPlucker_cell e
          (gammaSewnCriticalAdjacentPrime_lower n)
          (gammaSewnCriticalAdjacentPrime_upper n)) s ≤
      (4 / 5 : ℝ) * gammaSewnCriticalAdjacentPrime_Total e n := by
  let L := Real.log (gammaSewnCriticalAdjacentPrime_lower n : ℝ)
  let U := Real.log (gammaSewnCriticalAdjacentPrime_upper n : ℝ)
  have hL : 0 < L := Real.log_pos (by
    exact_mod_cast (gammaSewnCriticalAdjacentPrime_lower n).2.one_lt)
  have hU : 0 < U := Real.log_pos (by
    exact_mod_cast (gammaSewnCriticalAdjacentPrime_upper n).2.one_lt)
  have hLU : L < U := by
    exact Real.strictMonoOn_log
      (by
        show (0 : ℝ) < (gammaSewnCriticalAdjacentPrime_lower n : ℝ)
        exact_mod_cast (gammaSewnCriticalAdjacentPrime_lower n).2.pos)
      (by
        show (0 : ℝ) < (gammaSewnCriticalAdjacentPrime_upper n : ℝ)
        exact_mod_cast (gammaSewnCriticalAdjacentPrime_upper n).2.pos)
      (by exact_mod_cast gammaSewnCriticalAdjacentPrime_order n)
  have hUL : U ≤ 2 * L := criticalAdjacent_log_upper_le_two_lower_quantitative n
  have hsq : U ^ 2 ≤ 4 * L ^ 2 := by nlinarith
  have hsqLower : L ^ 2 < U ^ 2 := by nlinarith
  fin_cases s <;>
    simp [RHTower.gammaSewnFourRateComplementaryFisher,
      RHTower.fourRateComplementarySum, RHTower.fourRatePairComplementLeft,
      RHTower.fourRatePairComplementRight, gammaSewnOrderedPrimeDepthPlucker_cell,
      gammaSewnCriticalAdjacentPrime_Total, gammaSewnCriticalPrimeDepthPacket_Total,
      RHTower.gammaSewnFourRateTotalFisher, RHTower.fourRateTotalSum,
      RHTower.gammaSewnMobiusApertureBoundaryFisherClock] <;>
    dsimp [L, U] at hsq hsqLower ⊢ <;> nlinarith

theorem gammaSewnCriticalAdjacentPrime_Mean_le_four_fifths_total (e n : ℕ) :
    gammaSewnCriticalAdjacentPrime_Mean e n ≤
      (4 / 5 : ℝ) * gammaSewnCriticalAdjacentPrime_Total e n := by
  have hprob (s : Fin 6) :
      0 ≤ gammaSewnOrderedPrimeDepthPlucker_probability
        gammaSewnCriticalAdjacentPrime_aperture e
        (gammaSewnCriticalAdjacentPrime_lower n)
        (gammaSewnCriticalAdjacentPrime_upper n) s :=
    gammaSewnOrderedPrimeDepthPlucker_probability_nonneg
      gammaSewnCriticalPlucker_hostileHarmonicAperture_pos
      (gammaSewnCriticalAdjacentPrime_order n)
      (gammaSewnCriticalFinitePacket_aperture_admissible e
        (gammaSewnCriticalAdjacentPrime_lower n)) s
  have hsum :
      ∑ s, gammaSewnOrderedPrimeDepthPlucker_probability
        gammaSewnCriticalAdjacentPrime_aperture e
        (gammaSewnCriticalAdjacentPrime_lower n)
        (gammaSewnCriticalAdjacentPrime_upper n) s = 1 := by
    exact RHTower.sum_gammaSewnFourRateBoundaryPairProbability
      (gammaSewnCriticalAdjacentPrime_Partition_pos e n).ne'
  unfold gammaSewnCriticalAdjacentPrime_Mean gammaSewnCriticalPrimeDepthPacket_Mean
    RHTower.complementaryFisherMean
  calc
    ∑ s, gammaSewnOrderedPrimeDepthPlucker_probability
          gammaSewnCriticalAdjacentPrime_aperture e
          (gammaSewnCriticalAdjacentPrime_lower n)
          (gammaSewnCriticalAdjacentPrime_upper n) s *
        RHTower.gammaSewnFourRateComplementaryFisher
          (gammaSewnOrderedPrimeDepthPlucker_cell e
            (gammaSewnCriticalAdjacentPrime_lower n)
            (gammaSewnCriticalAdjacentPrime_upper n)) s ≤
      ∑ s, gammaSewnOrderedPrimeDepthPlucker_probability
          gammaSewnCriticalAdjacentPrime_aperture e
          (gammaSewnCriticalAdjacentPrime_lower n)
          (gammaSewnCriticalAdjacentPrime_upper n) s *
        ((4 / 5 : ℝ) * gammaSewnCriticalAdjacentPrime_Total e n) := by
          apply Finset.sum_le_sum
          intro s _hs
          exact mul_le_mul_of_nonneg_left
            (gammaSewnCriticalAdjacentPrime_complementaryFisher_le_four_fifths_total e n s)
            (hprob s)
    _ = (4 / 5 : ℝ) * gammaSewnCriticalAdjacentPrime_Total e n := by
      rw [← Finset.sum_mul, hsum, one_mul]

theorem gammaSewnCriticalAdjacentPrime_NumeratorTerm_le_four_fifths_denominator
    (z : ℕ × ℕ) :
    gammaSewnCriticalAdjacentPrime_NumeratorTerm z ≤
      (4 / 5 : ℝ) * gammaSewnCriticalAdjacentPrime_DenominatorTerm z := by
  unfold gammaSewnCriticalAdjacentPrime_NumeratorTerm
    gammaSewnCriticalAdjacentPrime_DenominatorTerm
  have hpart := (gammaSewnCriticalAdjacentPrime_Partition_pos z.1 z.2).le
  have hmean := gammaSewnCriticalAdjacentPrime_Mean_le_four_fifths_total z.1 z.2
  nlinarith [mul_nonneg hpart
    (sub_nonneg.mpr hmean)]

theorem gammaSewnCriticalAdjacentPrime_CofinalNumerator_le_four_fifths_denominator :
    gammaSewnCriticalAdjacentPrime_CofinalNumerator ≤
      (4 / 5 : ℝ) * gammaSewnCriticalAdjacentPrime_CofinalDenominator := by
  unfold gammaSewnCriticalAdjacentPrime_CofinalNumerator
    gammaSewnCriticalAdjacentPrime_CofinalDenominator
  calc
    ∑' z : ℕ × ℕ, gammaSewnCriticalAdjacentPrime_NumeratorTerm z ≤
        ∑' z : ℕ × ℕ,
          (4 / 5 : ℝ) * gammaSewnCriticalAdjacentPrime_DenominatorTerm z := by
      exact Summable.tsum_le_tsum
        gammaSewnCriticalAdjacentPrime_NumeratorTerm_le_four_fifths_denominator
        summable_gammaSewnCriticalAdjacentPrime_NumeratorTerm
        (summable_gammaSewnCriticalAdjacentPrime_DenominatorTerm.mul_left (4 / 5 : ℝ))
    _ = (4 / 5 : ℝ) *
        ∑' z : ℕ × ℕ, gammaSewnCriticalAdjacentPrime_DenominatorTerm z := by
      rw [tsum_mul_left]

theorem gammaSewnCriticalAdjacentPrime_CofinalFraction_le_four_fifths :
    gammaSewnCriticalAdjacentPrime_CofinalFraction ≤ (4 / 5 : ℝ) := by
  have hden := gammaSewnCriticalAdjacentPrime_CofinalDenominator_pos
  unfold gammaSewnCriticalAdjacentPrime_CofinalFraction
  rw [div_le_iff₀ hden]
  simpa [mul_comm] using
    gammaSewnCriticalAdjacentPrime_CofinalNumerator_le_four_fifths_denominator

/-- Quantitative survivor of adjacent-prime geometry: at least one fifth of every information
atom remains after the cofinal physical Schur reduction. -/
theorem gammaSewnCriticalCofinalResidualFactor_ge_one_fifth :
    (1 / 5 : ℝ) ≤ gammaSewnCriticalCofinalResidualFactor := by
  unfold gammaSewnCriticalCofinalResidualFactor
  linarith [gammaSewnCriticalAdjacentPrime_CofinalFraction_le_four_fifths]

private theorem cofinalCriticalPrimeTwoHalfNode_bounds :
    let r := RHTower.xiMobiusContinuousApertureDiskNode (1 / 2)
      RHTower.gammaSewnMobiusApertureStokesPrimeTwo
    (7 / 10 : ℝ) < r ∧ r < 71 / 100 := by
  let r := RHTower.xiMobiusContinuousApertureDiskNode (1 / 2)
    RHTower.gammaSewnMobiusApertureStokesPrimeTwo
  have hr0 : 0 < r := RHTower.xiMobiusContinuousApertureDiskNode_pos _ _
  have hr2 : r ^ 2 = 1 / 2 := by
    simpa [r, RHTower.xiTransversePrimeApertureDiskNode_one_eq_inv] using
      RHTower.xiMobiusContinuousApertureDiskNode_half_sq
        RHTower.gammaSewnMobiusApertureStokesPrimeTwo
  constructor <;> by_contra h
  · have hr : r ≤ 7 / 10 := le_of_not_gt h
    nlinarith [mul_nonneg (sub_nonneg.mpr hr)
      (add_nonneg hr0.le (by norm_num : (0 : ℝ) ≤ 7 / 10))]
  · have hr : 71 / 100 ≤ r := le_of_not_gt h
    nlinarith [mul_nonneg (sub_nonneg.mpr hr)
      (add_nonneg hr0.le (by norm_num : (0 : ℝ) ≤ 71 / 100))]

private theorem cofinal_nineteen_twentieths_lt_criticalPrimeTwoContraction :
    (19 / 20 : ℝ) <
      RHTower.gammaSewnMobiusValuationContractionMultiplier (1 / 2)
        RHTower.gammaSewnMobiusApertureStokesPrimeTwo := by
  let p := RHTower.gammaSewnMobiusApertureStokesPrimeTwo
  let r := RHTower.xiMobiusContinuousApertureDiskNode (1 / 2) p
  let c := RHTower.gammaSewnMobiusValuationContractionMultiplier (1 / 2) p
  have hr : (7 / 10 : ℝ) < r ∧ r < 71 / 100 := by
    simpa only [r, p] using cofinalCriticalPrimeTwoHalfNode_bounds
  have hr0 : 0 < r := RHTower.xiMobiusContinuousApertureDiskNode_pos _ _
  have hc0 : 0 < c := RHTower.gammaSewnMobiusValuationContractionMultiplier_pos _ _
  have hden : 0 < 8 * (1 + r ^ 4) := by positivity
  have hnum : (17 / 10 : ℝ) ^ 4 < (1 + r) ^ 4 :=
    pow_lt_pow_left₀ (by linarith [hr.1]) (by norm_num) (by norm_num)
  have hr57 : r < (5 / 7 : ℝ) := by linarith [hr.2]
  have hr4 : r ^ 4 < (5 / 7 : ℝ) ^ 4 :=
    pow_lt_pow_left₀ hr57 hr0.le (by norm_num)
  have hc4 : (19 / 20 : ℝ) ^ 4 < c ^ 4 := by
    rw [RHTower.gammaSewnMobiusValuationContractionMultiplier_pow_four]
    change (19 / 20 : ℝ) ^ 4 < (1 + r) ^ 4 / (8 * (1 + r ^ 4))
    rw [lt_div_iff₀ hden]
    norm_num at hnum hr4 ⊢
    nlinarith
  by_contra h
  have hc : c ≤ 19 / 20 := le_of_not_gt h
  have hc2 : c ^ 2 ≤ (19 / 20 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc)
      (add_nonneg hc0.le (by norm_num : (0 : ℝ) ≤ 19 / 20))]
  have hc4le : c ^ 4 ≤ (19 / 20 : ℝ) ^ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc2)
      (add_nonneg (sq_nonneg c) (sq_nonneg (19 / 20 : ℝ)))]
  linarith

theorem gammaSewnCriticalPrimeTwoDepthZero_weight_gt_thirtyThree_thousandths :
    (33 / 1000 : ℝ) <
      RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
        (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0) := by
  let p := RHTower.gammaSewnMobiusApertureStokesPrimeTwo
  let r := RHTower.xiMobiusContinuousApertureDiskNode (1 / 2) p
  let c := RHTower.gammaSewnMobiusValuationContractionMultiplier (1 / 2) p
  have hr : (7 / 10 : ℝ) < r ∧ r < 71 / 100 := by
    simpa only [r, p] using cofinalCriticalPrimeTwoHalfNode_bounds
  have hc : (19 / 20 : ℝ) < c :=
    cofinal_nineteen_twentieths_lt_criticalPrimeTwoContraction
  have hc2 : (361 / 400 : ℝ) < c ^ 2 := by
    nlinarith [sq_nonneg (c - 19 / 20)]
  have hgap : (29 / 100 : ℝ) ^ 2 < (1 - r) ^ 2 := by
    nlinarith [sq_nonneg (r - 71 / 100)]
  have hprod : (303601 / 4000000 : ℝ) < c ^ 2 * (1 - r) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hc2) (sub_pos.mpr hgap)]
  have hdenpos : 0 < Real.log 2 * r :=
    mul_pos (Real.log_pos (by norm_num)) (lt_trans (by norm_num) hr.1)
  have hden : Real.log 2 * r < 497 / 1000 := by
    calc
      Real.log 2 * r < (7 / 10 : ℝ) * r := by
        exact mul_lt_mul_of_pos_right
          (Real.log_two_lt_d9.trans (by norm_num)) (lt_trans (by norm_num) hr.1)
      _ < (7 / 10 : ℝ) * (71 / 100) := by
        gcongr
        nlinarith [hr.2]
      _ = 497 / 1000 := by norm_num
  rw [RHTower.gammaSewnMobiusApertureStokesSquaredWeight,
    gammaSewnMobiusApertureStokesReflectedWeight_eq_source (by norm_num)]
  simp only [RHTower.gammaSewnMobiusApertureStokesPrimeTwo,
    RHTower.xiTransversePrimeApertureDiskNode_one_eq_inv]
  norm_num only [Nat.cast_ofNat, invOf_eq_inv, pow_zero, mul_one, Nat.reduceAdd,
    Nat.cast_one, one_pow]
  change (33 / 1000 : ℝ) <
    2 * (c ^ 2 * (1 / 9) * (1 - r) ^ 2 / (1 * Real.log 2 * r))
  norm_num only [one_mul]
  rw [show 2 * (c ^ 2 * (1 / 9) * (1 - r) ^ 2 / (Real.log 2 * r)) =
    (2 * c ^ 2 * (1 / 9) * (1 - r) ^ 2) / (Real.log 2 * r) by ring]
  rw [lt_div_iff₀ hdenpos]
  nlinarith

theorem gammaSewnCriticalPrimeTwoDepthZero_gap_lt_eleven_halves :
    RHTower.gammaSewnMobiusApertureStokesGap (1 / 2)
        (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0) < 11 / 2 := by
  let p := RHTower.gammaSewnMobiusApertureStokesPrimeTwo
  let r := RHTower.xiMobiusContinuousApertureDiskNode (1 / 2) p
  let c := RHTower.gammaSewnMobiusValuationContractionMultiplier (1 / 2) p
  have hr : (7 / 10 : ℝ) < r ∧ r < 71 / 100 := by
    simpa only [r, p] using cofinalCriticalPrimeTwoHalfNode_bounds
  have hc : (19 / 20 : ℝ) < c :=
    cofinal_nineteen_twentieths_lt_criticalPrimeTwoContraction
  have hrgap : (29 / 100 : ℝ) < 1 - r := by nlinarith [hr.2]
  have hdenLower : (551 / 2000 : ℝ) < c * (1 - r) := by
    nlinarith [mul_pos (sub_pos.mpr hc) (sub_pos.mpr hrgap)]
  have hsourceDen : (551 / 6000 : ℝ) < c * (1 / 3) * (1 - r) := by
    nlinarith
  have hdenpos : 0 < c * (1 / 3) * (1 - r) := by linarith
  have hnum : Real.log 2 * r < 497 / 1000 := by
    calc
      Real.log 2 * r < (7 / 10 : ℝ) * r := by
        exact mul_lt_mul_of_pos_right
          (Real.log_two_lt_d9.trans (by norm_num)) (lt_trans (by norm_num) hr.1)
      _ < (7 / 10 : ℝ) * (71 / 100) := by
        gcongr
        nlinarith [hr.2]
      _ = 497 / 1000 := by norm_num
  rw [RHTower.gammaSewnMobiusApertureStokesGap,
    RHTower.gammaSewnMobiusApertureStokesInverseTilt]
  simp only [RHTower.gammaSewnMobiusApertureStokesPrimeTwo,
    RHTower.xiTransversePrimeApertureDiskNode_one_eq_inv]
  norm_num only [Nat.cast_ofNat, invOf_eq_inv, Nat.reduceAdd, Nat.cast_one,
    one_mul]
  change Real.log 2 * r / (c * (1 / 3) * (1 - r)) < 11 / 2
  rw [div_lt_iff₀ hdenpos]
  nlinarith

theorem gammaSewnCriticalPrimeTwoDepthZero_node_gt_four_over_oneTwentyOne :
    (4 / 121 : ℝ) <
      RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2)
        (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0) := by
  let g := RHTower.gammaSewnMobiusApertureStokesGap (1 / 2)
    (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0)
  have hg0 : 0 < g := RHTower.gammaSewnMobiusApertureStokesGap_pos (by norm_num) _
  have hg : g < 11 / 2 := gammaSewnCriticalPrimeTwoDepthZero_gap_lt_eleven_halves
  have hinv : (2 / 11 : ℝ) < g⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ hg0]
    nlinarith [mul_lt_mul_of_pos_left hg (by norm_num : (0 : ℝ) < 2 / 11)]
  rw [RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode,
    RHTower.gammaSewnMobiusApertureStokesReciprocalGapNode]
  nlinarith [sq_nonneg (g⁻¹ - 2 / 11)]

theorem summable_gammaSewnCriticalAdjacentPrime_CofinalReducedWeight :
    Summable gammaSewnCriticalAdjacentPrime_CofinalReducedWeight := by
  apply Summable.of_nonneg_of_le
    (fun pk => (gammaSewnCriticalAdjacentPrime_CofinalReducedWeight_mem pk).1.le)
    (fun pk => (gammaSewnCriticalAdjacentPrime_CofinalReducedWeight_mem pk).2.le)
    (summable_gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight.mul_left
      (1 / 2 : ℝ))

/-- Literal compact atomic carrier obtained by applying P-G84's cofinal scalar reduction to every
information-depleted Stokes atom. -/
def gammaSewnCriticalCofinalReducedCarrier : MeasureTheory.Measure ℝ :=
  MeasureTheory.Measure.sum fun pk : Nat.Primes × ℕ =>
    ENNReal.ofReal (gammaSewnCriticalAdjacentPrime_CofinalReducedWeight pk) •
      MeasureTheory.Measure.dirac
        (RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2) pk)

theorem integrable_one_gammaSewnCriticalCofinalReducedCarrier :
    MeasureTheory.Integrable (fun _ : ℝ => (1 : ℝ))
      gammaSewnCriticalCofinalReducedCarrier := by
  rw [gammaSewnCriticalCofinalReducedCarrier]
  apply MeasureTheory.integrable_sum_dirac
    (fun pk => by simp [ENNReal.ofReal_ne_top])
  apply summable_gammaSewnCriticalAdjacentPrime_CofinalReducedWeight.congr
  intro pk
  rw [ENNReal.toReal_ofReal
    (gammaSewnCriticalAdjacentPrime_CofinalReducedWeight_mem pk).1.le]
  simp

theorem gammaSewnCriticalCofinalReducedCarrier_finite :
    MeasureTheory.IsFiniteMeasure gammaSewnCriticalCofinalReducedCarrier := by
  exact (MeasureTheory.integrable_const_iff_isFiniteMeasure one_ne_zero).mp
    integrable_one_gammaSewnCriticalCofinalReducedCarrier

theorem ae_gammaSewnCriticalCofinalReducedCarrier_mem_compact :
    ∀ᵐ y : ℝ ∂gammaSewnCriticalCofinalReducedCarrier,
      0 ≤ y ∧ |y| ≤ ((Real.log 2)⁻¹) ^ 2 := by
  rw [gammaSewnCriticalCofinalReducedCarrier, MeasureTheory.Measure.ae_sum_iff]
  intro pk
  apply MeasureTheory.Measure.ae_smul_measure
  exact (MeasureTheory.ae_dirac_iff
    (measurableSet_Ici.inter
      (measurableSet_le measurable_id.abs measurable_const))).2
    ⟨(RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_pos
        (by norm_num) pk).le,
      by
        change |RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode
          (1 / 2) pk| ≤ ((Real.log 2)⁻¹) ^ 2
        rw [abs_of_pos
          (RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_pos
            (by norm_num) pk)]
        exact RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_le
          (by norm_num) (by norm_num) pk⟩

theorem integral_pow_gammaSewnCriticalCofinalReducedCarrier_eq_tsum (n : ℕ) :
    ∫ y : ℝ, y ^ n ∂gammaSewnCriticalCofinalReducedCarrier =
      ∑' pk : Nat.Primes × ℕ,
        gammaSewnCriticalAdjacentPrime_CofinalReducedWeight pk *
          RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode
            (1 / 2) pk ^ n := by
  rw [gammaSewnCriticalCofinalReducedCarrier,
    MeasureTheory.integral_sum_dirac
      (fun pk => by simp [ENNReal.ofReal_ne_top])]
  apply tsum_congr
  intro pk
  rw [ENNReal.toReal_ofReal
    (gammaSewnCriticalAdjacentPrime_CofinalReducedWeight_mem pk).1.le]
  simp only [smul_eq_mul]

private theorem cofinalCriticalInformationFactor_two_zero_lt :
    gammaSewnMobiusApertureStokesCriticalInformationFactor
        (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0) < 3 / 10 := by
  have h := gammaSewnMobiusApertureStokesCriticalInformationFactor_le_cubic
    RHTower.gammaSewnMobiusApertureStokesPrimeTwo 0
  have hlog : Real.log 2 < 7 / 10 := Real.log_two_lt_d9.trans (by norm_num)
  have hu0 : 0 ≤ Real.log 2 / 2 := by positivity
  have hu : Real.log 2 / 2 < 7 / 20 := by linarith
  have hexp : Real.exp (-(Real.log 2 / 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  norm_num only [Nat.cast_zero, zero_add, Nat.cast_one, one_mul, mul_one] at h
  calc
    gammaSewnMobiusApertureStokesCriticalInformationFactor
        (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0) ≤
      4 / 3 * ((Real.log 2 / 2) ^ 3 * Real.exp (-(Real.log 2 / 2))) := h
    _ < 4 / 3 * ((7 / 20 : ℝ) ^ 3 * Real.exp (-(Real.log 2 / 2))) := by gcongr
    _ ≤ 4 / 3 * ((7 / 20 : ℝ) ^ 3 * 1) := by gcongr
    _ < 3 / 10 := by norm_num

theorem gammaSewnCriticalCofinalReducedPrimeTwoDepthZero_firstMoment_lower :
    (9 / 50000 : ℝ) <
      gammaSewnCriticalAdjacentPrime_CofinalReducedWeight
          (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0) *
        RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2)
          (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0) := by
  let pk : Nat.Primes × ℕ :=
    (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0)
  let raw := RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2) pk
  let depleted := gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight pk
  let reduced := gammaSewnCriticalAdjacentPrime_CofinalReducedWeight pk
  let node := RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2) pk
  have hraw : (33 / 1000 : ℝ) < raw := by
    simpa only [raw, pk] using
      gammaSewnCriticalPrimeTwoDepthZero_weight_gt_thirtyThree_thousandths
  have hk := cofinalCriticalInformationFactor_two_zero_lt
  have href : 0 < RHTower.gammaSewnMobiusApertureStokesReflectedWeight (1 / 2) pk :=
    RHTower.gammaSewnMobiusApertureStokesReflectedWeight_pos (by norm_num) pk
  have hdepRaw : (17 / 20 : ℝ) * raw < depleted := by
    dsimp only [depleted, raw]
    rw [
      gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight,
      RHTower.gammaSewnMobiusApertureStokesSquaredWeight]
    simpa only [pk] using
      (show (17 / 20 : ℝ) *
          (2 * RHTower.gammaSewnMobiusApertureStokesReflectedWeight (1 / 2) pk) <
        (2 - gammaSewnMobiusApertureStokesCriticalInformationFactor pk) *
          RHTower.gammaSewnMobiusApertureStokesReflectedWeight (1 / 2) pk by
        nlinarith [mul_pos (sub_pos.mpr hk) href])
  have hdep : (561 / 20000 : ℝ) < depleted := by nlinarith
  have hres := gammaSewnCriticalCofinalResidualFactor_ge_one_fifth
  have hred : (561 / 100000 : ℝ) < reduced := by
    have hfirst : (1 / 5 : ℝ) * (561 / 20000 : ℝ) <
        (1 / 5 : ℝ) * depleted := mul_lt_mul_of_pos_left hdep (by norm_num)
    have hsecond : (1 / 5 : ℝ) * depleted ≤
        gammaSewnCriticalCofinalResidualFactor * depleted :=
      mul_le_mul_of_nonneg_right hres
        (gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight_pos pk).le
    change (1 / 5 : ℝ) * depleted ≤ reduced at hsecond
    change (561 / 100000 : ℝ) < reduced
    norm_num at hfirst
    exact hfirst.trans_le hsecond
  have hnode : (4 / 121 : ℝ) < node := by
    simpa only [node, pk] using
      gammaSewnCriticalPrimeTwoDepthZero_node_gt_four_over_oneTwentyOne
  have hprod : (561 / 100000 : ℝ) * (4 / 121 : ℝ) < reduced * node :=
    (mul_lt_mul_of_pos_right hred (by norm_num)).trans
      (mul_lt_mul_of_pos_left hnode
        (lt_trans (by norm_num) hred))
  have hprod' : (51 / 275000 : ℝ) < reduced * node := by
    norm_num at hprod ⊢
    exact hprod
  have hnumeric : (9 / 50000 : ℝ) < (51 / 275000 : ℝ) := by norm_num
  have := hnumeric.trans hprod'
  simpa only [reduced, node, pk] using this

theorem normalizedPrimeArchMoment_one_lt_integral_gammaSewnCriticalCofinalReducedCarrier :
    RHTower.normalizedPrimeArchMoment 1 <
      ∫ y : ℝ, y ^ 1 ∂gammaSewnCriticalCofinalReducedCarrier := by
  rw [integral_pow_gammaSewnCriticalCofinalReducedCarrier_eq_tsum]
  simp only [pow_one]
  let f := fun pk : Nat.Primes × ℕ =>
    gammaSewnCriticalAdjacentPrime_CofinalReducedWeight pk *
      RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2) pk
  have hfnonneg : ∀ pk, 0 ≤ f pk := fun pk => mul_nonneg
    (gammaSewnCriticalAdjacentPrime_CofinalReducedWeight_mem pk).1.le
    (RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_pos
      (by norm_num) pk).le
  have hfsum : Summable f := by
    refine Summable.of_nonneg_of_le hfnonneg (fun pk => ?_)
      (summable_gammaSewnCriticalAdjacentPrime_CofinalReducedWeight.mul_left
        (((Real.log 2)⁻¹) ^ 2))
    have hw := (gammaSewnCriticalAdjacentPrime_CofinalReducedWeight_mem pk).1.le
    have hn := RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_le
      (s := (1 / 2 : ℝ)) (by norm_num) (by norm_num) pk
    dsimp only [f]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hn hw
  have hselected :
      f (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0) ≤ ∑' pk, f pk := by
    have hle := hfsum.sum_le_tsum
      ({(RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0)} :
        Finset (Nat.Primes × ℕ))
      (fun pk _ => hfnonneg pk)
    simpa only [Finset.sum_singleton] using hle
  exact RHTower.normalizedPrimeArchMoment_one_lt_nine_over_fiftyThousand.trans
    (gammaSewnCriticalCofinalReducedPrimeTwoDepthZero_firstMoment_lower.trans_le
      hselected)

def GammaSewnCriticalCofinalReducedMomentIdentification : Prop :=
  RHTower.completedSeamMomentGerm =ᶠ[nhds 0]
    RHTower.compactMarkovTransform gammaSewnCriticalCofinalReducedCarrier

/-- **P-G89 no-go.** The covariance-correct cofinal scalar carrier cannot be the completed seam
carrier. Its first prime-two atom already carries more first moment than the entire completed
source. -/
theorem not_gammaSewnCriticalCofinalReducedMomentIdentification :
    ¬ GammaSewnCriticalCofinalReducedMomentIdentification := by
  intro hgerm
  let B : ℝ := ((Real.log 2)⁻¹) ^ 2
  letI : MeasureTheory.IsFiniteMeasure gammaSewnCriticalCofinalReducedCarrier :=
    gammaSewnCriticalCofinalReducedCarrier_finite
  have hB : 0 < B := by
    dsimp [B]
    exact sq_pos_of_pos (inv_pos.mpr (Real.log_pos (by norm_num)))
  have hbound : ∀ᵐ x : ℝ ∂gammaSewnCriticalCofinalReducedCarrier, |x| ≤ B :=
    ae_gammaSewnCriticalCofinalReducedCarrier_mem_compact.mono fun _ hx => hx.2
  have hder := hgerm.iteratedDeriv_eq 1
  rw [RHTower.iteratedDeriv_completedSeamMomentGerm,
    RHTower.iteratedDeriv_compactMarkovTransform
      gammaSewnCriticalCofinalReducedCarrier hB hbound 1
      (by simpa using (show (0 : ℝ) < 1 / (2 * B) by positivity)),
    RHTower.compactMarkovKernelMoment_zero_node] at hder
  have hintc :
      (∫ x : ℝ, (x : ℂ) ∂gammaSewnCriticalCofinalReducedCarrier) =
        ((∫ x : ℝ, x ∂gammaSewnCriticalCofinalReducedCarrier : ℝ) : ℂ) := by
    exact integral_ofReal
      (X := ℝ) (μ := gammaSewnCriticalCofinalReducedCarrier) (𝕜 := ℂ)
      (f := fun x : ℝ => x)
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, one_mul] at hder
  rw [hintc] at hder
  norm_num at hder
  have heq : RHTower.normalizedPrimeArchMoment 1 =
      ∫ x : ℝ, x ^ 1 ∂gammaSewnCriticalCofinalReducedCarrier := by
    simpa only [pow_one] using hder
  linarith [normalizedPrimeArchMoment_one_lt_integral_gammaSewnCriticalCofinalReducedCarrier]

end RHTower.HedenmalmThetaSource
