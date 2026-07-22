import GaloisForLFunctions.RHTower.PrimeArchBernsteinPurityDivergence
import GaloisForLFunctions.RHTower.PrimeArchCofinalHausdorffDiagonalRH
import GaloisForLFunctions.RHTower.PrimeArchFiniteKMSLocalMomentClosure
import GaloisForLFunctions.RHTower.PrimeArchHausdorffBernsteinKMSRH
import GaloisForLFunctions.RHTower.XiThermalEndpointResolventGap
import GaloisForLFunctions.RHTower.XiThermalProjectiveFreeEnergyRadius
import GaloisForLFunctions.RHTower.XiThermalSourceRelativeGapBound

/-!
# Xi prime--archimedean thermal endpoint universality

The terminal critical-abscissa classifiers in the calibrated Hausdorff, Bernstein, finite-KMS,
orientation, resolvent, projective thermal, and Born--Witten charts all carry exactly the RH
endpoint datum.  This module packages their maximal common closure.
-/

open Filter Topology
open HTGeometry

namespace RHTower

noncomputable section

/-- Simultaneous realization of the critical prime--polar abscissa in every currently formalized
Hausdorff, Bernstein, finite-KMS, orientation, resolvent, projective, and Born--Witten chart. -/
def XiPrimeArchThermalEndpointUniversalCertificate : Prop :=
  ScaledHausdorffMomentDifferencesNonnegative primeArchEndpointHausdorffRadius
    normalizedPrimeArchMoment ∧
  PrimeArchHausdorffMomentDifferencesNonnegative ∧
  CofinalScaledHausdorffQuadrantNonnegative primeArchEndpointHausdorffRadius
    normalizedPrimeArchMoment ∧
  CofinalScaledHausdorffDiagonalsNonnegative primeArchEndpointHausdorffRadius
    normalizedPrimeArchMoment ∧
  CofinalHausdorffBernsteinNegativeMassVanishing primeArchEndpointHausdorffRadius
    normalizedPrimeArchMoment ∧
  PrimeArchBernsteinNegativeMassSubexponential ∧
  PrimeArchBernsteinNegativeMassBounded ∧
  PrimeArchBernsteinNegativeMassCofinallyBounded ∧
  PrimeArchEndpointBernsteinPurityCofinallyBounded ∧
  PrimeArchFiniteKMSWightmanLocalMomentClosure ∧
  PrimeArchFinitePositiveAtomicLocalMomentClosure ∧
  PrimeArchFinitePositiveAtomicDiagonalApproximation ∧
  (∀ k r : ℕ, 13 < k ∨ 43 < r →
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment k r) ∧
  (∀ k r : ℕ, 40 < 3 * k + r →
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment k r) ∧
  (∃ d M : ℕ → ℕ, Tendsto d atTop atTop ∧
    ∀ j : ℕ,
      bernsteinCoefficientSquareDiscrepancyAtDefectDegree
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment)
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius
          (xiThermalTruncation (M j))) (d j) ≤ 1) ∧
  xiThermalOrientationEnergy = 0 ∧
  xiThermalSecondMoment ≤ normalizedPrimeArchMoment 1 ∧
  Tendsto (fun M => xiThermalTruncation M 1) atTop
    (nhds (normalizedPrimeArchMoment 1)) ∧
  xiThermalEndpointResolventValue = xiEndpointCompletedCurvature ∧
  Tendsto xiThermalEndpointResolventTruncation atTop
    (nhds xiEndpointCompletedCurvature) ∧
  (∀ q : XiZeroCopy, xiThermalEndpointScatteringPhase q = 1) ∧
  (∃ C : ℝ, ∀ᶠ j : ℕ in atTop,
    xiThermalProjectiveColdTruncation j j ≤ C) ∧
  (∃ C : ℝ, ∃ᶠ j : ℕ in atTop,
    xiThermalProjectiveColdTruncation j j ≤ C) ∧
  (∀ alpha : ℝ, 0 < alpha →
    ∃ C : ℝ, ∀ᶠ m : ℕ in atTop,
      xiThermalProjectiveMoment m ≤ C * alpha ^ m) ∧
  (∃ C : ℝ, ∀ᶠ k : ℕ in atTop,
    xiThermalProjectiveColdPartition k ≤ C) ∧
  (∃ C : ℝ, ∀ᶠ k : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
    xiThermalProjectiveColdTruncation N k ≤ C) ∧
  xiThermalProjectiveMoment 1 = 0 ∧
  Tendsto
    (fun j : ℕ =>
      Real.log (xiThermalProjectiveColdTruncation j j) / (j : ℝ))
    atTop (nhds 0) ∧
  xiThermalSecondMoment = thetaCuspBornWittenQuadraticSource ∧
  xiThermalSecondMoment ≤ thetaCuspBornWittenQuadraticSource ∧
  Tendsto (fun N => xiThermalTruncation N 1) atTop
    (nhds thetaCuspBornWittenQuadraticSource)

/-- **Xi prime--archimedean thermal endpoint universality law.**  For every positive rectangular
window and admissible tail, the critical prime--polar negative-source abscissa bound is equivalent
to simultaneous realization in thirty-one Hausdorff, Bernstein, finite-KMS, orientation,
resolvent, projective thermal, and Born--Witten charts. -/
theorem rectangularPrimePolarSource_negativeAbscissa_le_one_iff_endpointUniversalCertificate
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    LSeries.abscissaOfAbsConv
        (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
      ((1 : ℝ) : EReal) ↔
      XiPrimeArchThermalEndpointUniversalCertificate := by
  have hbase : RiemannHypothesis ↔
      LSeries.abscissaOfAbsConv
          (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
        ((1 : ℝ) : EReal) :=
    riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one hL hN
  constructor
  · intro habscissa
    have hRH : RiemannHypothesis := hbase.2 habscissa
    exact ⟨
      scaledPrimeArchHausdorffMomentDifferencesNonnegative_iff_riemannHypothesis.2 hRH,
      primeArchHausdorffMomentDifferencesNonnegative_iff_riemannHypothesis.2 hRH,
      cofinalScaledPrimeArchHausdorffQuadrantNonnegative_iff_riemannHypothesis.2 hRH,
      cofinalScaledPrimeArchHausdorffDiagonalsNonnegative_iff_riemannHypothesis.2 hRH,
      cofinalPrimeArchHausdorffBernsteinNegativeMassVanishing_iff_riemannHypothesis.2 hRH,
      riemannHypothesis_iff_primeArchBernsteinNegativeMassSubexponential.1 hRH,
      riemannHypothesis_iff_primeArchBernsteinNegativeMassBounded.1 hRH,
      riemannHypothesis_iff_primeArchBernsteinNegativeMassCofinallyBounded.1 hRH,
      riemannHypothesis_iff_primeArchEndpointBernsteinPurity_cofinallyBounded.1 hRH,
      primeArchFiniteKMSWightmanLocalMomentClosure_iff_riemannHypothesis.2 hRH,
      primeArchFinitePositiveAtomicLocalMomentClosure_iff_riemannHypothesis.2 hRH,
      primeArchFinitePositiveAtomicDiagonalApproximation_iff_riemannHypothesis.2 hRH,
      (rectangularPrimePolarSource_negativeAbscissa_le_one_iff_rectangleHausdorffTailNonnegative
        hL hN).1 habscissa,
      (rectangularPrimePolarSource_negativeAbscissa_le_one_iff_weightedHausdorffTailNonnegative
        hL hN).1 habscissa,
      (rectangularPrimePolarSource_negativeAbscissa_le_one_iff_exists_cofinal_xiThermalTruncation_bernsteinSquareDiscrepancy_le_one
        hL hN).1 habscissa,
      xiThermalOrientationEnergy_eq_zero_iff_rh.2 hRH,
      xiThermalSecondMoment_le_source_iff_rh.2 hRH,
      tendsto_xiThermalTruncation_one_iff_rh.2 hRH,
      xiThermalEndpointResolventValue_eq_endpointCompletedCurvature_iff_rh.2 hRH,
      tendsto_xiThermalEndpointResolventTruncation_endpointCurvature_iff_rh.2 hRH,
      forall_xiThermalEndpointScatteringPhase_eq_one_iff_rh.2 hRH,
      riemannHypothesis_iff_exists_eventually_bounded_thermalProjectiveDiagonal.1 hRH,
      riemannHypothesis_iff_exists_frequently_bounded_thermalProjectiveDiagonal.1 hRH,
      riemannHypothesis_iff_forall_pos_exists_eventually_thermalProjectiveMoment_le.1 hRH,
      riemannHypothesis_iff_exists_eventually_bounded_thermalProjectiveColdPartition.1 hRH,
      riemannHypothesis_iff_exists_eventually_cold_eventually_thermodynamic_bound.1 hRH,
      xiThermalProjectiveMoment_one_eq_zero_iff_rh.2 hRH,
      riemannHypothesis_iff_tendsto_thermalProjectiveDiagonalFreeEnergy_zero.1 hRH,
      xiThermalSecondMoment_eq_bornWittenSource_iff_rh.2 hRH,
      xiThermalSecondMoment_le_bornWittenSource_iff_rh.2 hRH,
      tendsto_xiThermalTruncation_one_bornWittenSource_iff_rh.2 hRH⟩
  · intro hcertificate
    exact (rectangularPrimePolarSource_negativeAbscissa_le_one_iff_scaledPrimeArchHausdorffMomentDifferencesNonnegative
      hL hN).2 hcertificate.1

end

end RHTower
