import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualSecondStokesIntegral

/-!
# Actual balanced spin-two coefficient extraction

The literal actual completed-Poincare balanced `++-` source is already known pointwise to differ
from the Bochner coefficient times the scalar triple density by exactly the first and second
Stokes defects.  Both defects are separately known to be genuine standard-measure integrals on
the same truncated modular domain and to equal their paired cusp-top currents.

This module closes the missing integral seam.  It constructs the actual scalar and balanced
truncated hyperbolic moments, proves their compact-domain integrability, integrates the exhaustive
pointwise decomposition, and substitutes both literal Green--Stokes theorems.  For every
truncation height `Y >= 1`,

```text
balancedMoment(Y) - bochnerCoefficient * scalarMoment(Y)
  = secondPairedCuspTop(Y) + (gradientShift + 1) * firstPairedCuspTop(Y).
```

Thus the two already-classified cusp currents are the complete finite-height obstruction to the
actual balanced coefficient.  No noncusp, Fubini, tensor-normalization, regularity, or boundary
premise remains.

`[NEW] [ACTUAL COEFFICIENT EXTRACTION] [PAPER-PROVED] [LEAN-PROVED] [HC94]`
-/

open Complex Real Set MeasureTheory

namespace RHTower

noncomputable section

/-- Actual scalar triple density with hyperbolic measure factor on pair coordinates. -/
def d4BMActualScalarTripleHyperbolicDensityAt
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (w : ℝ × ℝ) : ℂ :=
  d4BMActualFirstStokesScalarDensity (d4BMStokesPairCoordinate w) P Q /
    (w.2 : ℂ) ^ (2 : ℕ)

/-- Actual balanced `++-` density with hyperbolic measure factor on pair coordinates. -/
def d4BMActualBalancedSpinTwoHyperbolicDensityAt
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (w : ℝ × ℝ) : ℂ :=
  d4BMActualBalancedSpinTwoDensity (d4BMStokesPairCoordinate w) P Q /
    (w.2 : ℂ) ^ (2 : ℕ)

theorem continuousOn_d4BMActualScalarTripleHyperbolicDensityAt_stokesCompactCell
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn (d4BMActualScalarTripleHyperbolicDensityAt P Q)
      (d4BMStokesCompactCell Y) := by
  have hF := continuousOn_d4BMCompletedEisensteinPoincareSeries_stokesCompactCell
    P (Y := Y)
  have hG := continuousOn_d4BMCompletedEisensteinPoincareSeries_stokesCompactCell
    Q (Y := Y)
  intro w hw
  have hy : w.2 ≠ 0 := by
    have := hw.2.1
    positivity
  have hyc : ContinuousWithinAt (fun w : ℝ × ℝ => (w.2 : ℂ))
      (d4BMStokesCompactCell Y) w :=
    (Complex.continuous_ofReal.comp continuous_snd).continuousAt.continuousWithinAt
  unfold d4BMActualScalarTripleHyperbolicDensityAt
    d4BMActualFirstStokesScalarDensity
  apply ContinuousWithinAt.div
  · exact ((hF w hw).pow 2).mul (hG w hw)
  · exact hyc.pow 2
  · exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hy)

theorem continuousOn_d4BMActualBalancedSpinTwoHyperbolicDensityAt_stokesCompactCell
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn (d4BMActualBalancedSpinTwoHyperbolicDensityAt P Q)
      (d4BMStokesCompactCell Y) := by
  have hG := continuousOn_d4BMCompletedEisensteinPoincareSeries_stokesCompactCell
    Q (Y := Y)
  have hFx := continuousOn_d4BMCompletedPoincareHorizontalFirstJet_stokesCompactCell
    P (Y := Y)
  have hFy := continuousOn_d4BMCompletedPoincareVerticalFirstJet_stokesCompactCell
    P (Y := Y)
  have hFxx := continuousOn_d4BMCompletedPoincareHorizontalSecondJet_stokesCompactCell
    P (Y := Y)
  have hFxy := continuousOn_d4BMCompletedPoincareMixedSecondJet_stokesCompactCell
    P (Y := Y)
  have hFyy := continuousOn_d4BMCompletedPoincareVerticalSecondJet_stokesCompactCell
    P (Y := Y)
  intro w hw
  have hy : w.2 ≠ 0 := by
    have := hw.2.1
    positivity
  have hyc : ContinuousWithinAt (fun w : ℝ × ℝ => (w.2 : ℂ))
      (d4BMStokesCompactCell Y) w :=
    (Complex.continuous_ofReal.comp continuous_snd).continuousAt.continuousWithinAt
  have hcoordc : ContinuousWithinAt
      (fun w : ℝ × ℝ => ((d4BMStokesPairCoordinate w).y : ℂ))
      (d4BMStokesCompactCell Y) w := by
    unfold d4BMStokesPairCoordinate d4BMStokesCoordinate
    fun_prop
  have hR : ContinuousWithinAt
      (fun w : ℝ × ℝ =>
        ((d4BMStokesPairCoordinate w).y : ℂ) ^ (2 : ℕ) *
            (d4BMCompletedPoincareVerticalSecondJet (d4BMStokesPairCoordinate w) P -
              d4BMCompletedPoincareHorizontalSecondJet (d4BMStokesPairCoordinate w) P +
              2 * Complex.I *
                d4BMCompletedPoincareMixedSecondJet (d4BMStokesPairCoordinate w) P) +
          2 * ((d4BMStokesPairCoordinate w).y : ℂ) *
            (d4BMCompletedPoincareVerticalFirstJet (d4BMStokesPairCoordinate w) P +
              Complex.I *
                d4BMCompletedPoincareHorizontalFirstJet (d4BMStokesPairCoordinate w) P))
        (d4BMStokesCompactCell Y) w := by
    exact (hcoordc.pow 2).mul
        (((hFyy w hw).sub (hFxx w hw)).add
          ((hFxy w hw).const_mul (2 * Complex.I))) |>.add
      ((hcoordc.const_mul 2).mul
        ((hFy w hw).add ((hFx w hw).const_mul Complex.I)))
  have hL : ContinuousWithinAt
      (fun w : ℝ × ℝ =>
        ((d4BMStokesPairCoordinate w).y : ℂ) ^ (2 : ℕ) *
            (d4BMCompletedPoincareVerticalSecondJet (d4BMStokesPairCoordinate w) P -
              d4BMCompletedPoincareHorizontalSecondJet (d4BMStokesPairCoordinate w) P -
              2 * Complex.I *
                d4BMCompletedPoincareMixedSecondJet (d4BMStokesPairCoordinate w) P) +
          2 * ((d4BMStokesPairCoordinate w).y : ℂ) *
            (d4BMCompletedPoincareVerticalFirstJet (d4BMStokesPairCoordinate w) P -
              Complex.I *
                d4BMCompletedPoincareHorizontalFirstJet (d4BMStokesPairCoordinate w) P))
        (d4BMStokesCompactCell Y) w := by
    exact (hcoordc.pow 2).mul
        (((hFyy w hw).sub (hFxx w hw)).sub
          ((hFxy w hw).const_mul (2 * Complex.I))) |>.add
      ((hcoordc.const_mul 2).mul
        ((hFy w hw).sub ((hFx w hw).const_mul Complex.I)))
  have hcont : ContinuousWithinAt
      (fun w : ℝ × ℝ =>
        ((((d4BMStokesPairCoordinate w).y : ℂ) ^ (2 : ℕ) *
              (d4BMCompletedPoincareVerticalSecondJet (d4BMStokesPairCoordinate w) P -
                d4BMCompletedPoincareHorizontalSecondJet (d4BMStokesPairCoordinate w) P +
                2 * Complex.I *
                  d4BMCompletedPoincareMixedSecondJet (d4BMStokesPairCoordinate w) P) +
            2 * ((d4BMStokesPairCoordinate w).y : ℂ) *
              (d4BMCompletedPoincareVerticalFirstJet (d4BMStokesPairCoordinate w) P +
                Complex.I *
                  d4BMCompletedPoincareHorizontalFirstJet (d4BMStokesPairCoordinate w) P)) *
          (((d4BMStokesPairCoordinate w).y : ℂ) ^ (2 : ℕ) *
              (d4BMCompletedPoincareVerticalSecondJet (d4BMStokesPairCoordinate w) P -
                d4BMCompletedPoincareHorizontalSecondJet (d4BMStokesPairCoordinate w) P -
                2 * Complex.I *
                  d4BMCompletedPoincareMixedSecondJet (d4BMStokesPairCoordinate w) P) +
            2 * ((d4BMStokesPairCoordinate w).y : ℂ) *
              (d4BMCompletedPoincareVerticalFirstJet (d4BMStokesPairCoordinate w) P -
                Complex.I *
                  d4BMCompletedPoincareHorizontalFirstJet (d4BMStokesPairCoordinate w) P)) *
          d4BMCompletedEisensteinPoincareSeries (d4BMStokesPairCoordinate w) Q) /
            (w.2 : ℂ) ^ (2 : ℕ))
        (d4BMStokesCompactCell Y) w :=
    ((hR.mul hL).mul (hG w hw)).div (hyc.pow 2)
      (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hy))
  rw [show d4BMActualBalancedSpinTwoHyperbolicDensityAt P Q =
      (fun w : ℝ × ℝ =>
        ((((d4BMStokesPairCoordinate w).y : ℂ) ^ (2 : ℕ) *
              (d4BMCompletedPoincareVerticalSecondJet (d4BMStokesPairCoordinate w) P -
                d4BMCompletedPoincareHorizontalSecondJet (d4BMStokesPairCoordinate w) P +
                2 * Complex.I *
                  d4BMCompletedPoincareMixedSecondJet (d4BMStokesPairCoordinate w) P) +
            2 * ((d4BMStokesPairCoordinate w).y : ℂ) *
              (d4BMCompletedPoincareVerticalFirstJet (d4BMStokesPairCoordinate w) P +
                Complex.I *
                  d4BMCompletedPoincareHorizontalFirstJet (d4BMStokesPairCoordinate w) P)) *
          (((d4BMStokesPairCoordinate w).y : ℂ) ^ (2 : ℕ) *
              (d4BMCompletedPoincareVerticalSecondJet (d4BMStokesPairCoordinate w) P -
                d4BMCompletedPoincareHorizontalSecondJet (d4BMStokesPairCoordinate w) P -
                2 * Complex.I *
                  d4BMCompletedPoincareMixedSecondJet (d4BMStokesPairCoordinate w) P) +
            2 * ((d4BMStokesPairCoordinate w).y : ℂ) *
              (d4BMCompletedPoincareVerticalFirstJet (d4BMStokesPairCoordinate w) P -
                Complex.I *
                  d4BMCompletedPoincareHorizontalFirstJet (d4BMStokesPairCoordinate w) P)) *
          d4BMCompletedEisensteinPoincareSeries (d4BMStokesPairCoordinate w) Q) /
            (w.2 : ℂ) ^ (2 : ℕ)) by
      funext v
      unfold d4BMActualBalancedSpinTwoHyperbolicDensityAt
        d4BMActualBalancedSpinTwoDensity
      rw [d4BM_actualCompletedPoincareRaiseLeg_eq,
        d4BM_actualCompletedPoincareLowerLeg_eq]]
  exact hcont

/-- Actual scalar triple moment on the standard truncated modular domain. -/
def d4BMActualScalarTripleTruncatedMoment
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (Y : ℝ) : ℂ :=
  ∫ w in d4BMTruncatedModularDomain Y,
    d4BMActualScalarTripleHyperbolicDensityAt P Q w

/-- Actual balanced `++-` spin-two moment on the standard truncated modular domain. -/
def d4BMActualBalancedSpinTwoTruncatedMoment
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (Y : ℝ) : ℂ :=
  ∫ w in d4BMTruncatedModularDomain Y,
    d4BMActualBalancedSpinTwoHyperbolicDensityAt P Q w

theorem integrableOn_d4BMActualScalarTripleHyperbolicDensityAt_truncatedDomain
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (Y : ℝ) :
    IntegrableOn (d4BMActualScalarTripleHyperbolicDensityAt P Q)
      (d4BMTruncatedModularDomain Y) := by
  apply ContinuousOn.integrableOn_compact (isCompact_d4BMTruncatedModularDomain Y)
  exact
    (continuousOn_d4BMActualScalarTripleHyperbolicDensityAt_stokesCompactCell
      P Q (Y := Y)).mono
    (d4BMTruncatedModularDomain_subset_stokesCompactCell Y)

theorem integrableOn_d4BMActualBalancedSpinTwoHyperbolicDensityAt_truncatedDomain
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (Y : ℝ) :
    IntegrableOn (d4BMActualBalancedSpinTwoHyperbolicDensityAt P Q)
      (d4BMTruncatedModularDomain Y) := by
  apply ContinuousOn.integrableOn_compact (isCompact_d4BMTruncatedModularDomain Y)
  exact
    (continuousOn_d4BMActualBalancedSpinTwoHyperbolicDensityAt_stokesCompactCell
      P Q (Y := Y)).mono
    (d4BMTruncatedModularDomain_subset_stokesCompactCell Y)

/-- **C-A.9u integrated exhaustive decomposition.**  The literal balanced moment differs from
the Bochner coefficient times the literal scalar moment by exactly the two already-constructed
standard-measure defect moments. -/
theorem d4BM_actualBalancedSpinTwoTruncatedMoment_defect_decomposition_of_one_le
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} (hY : 1 ≤ Y) :
    d4BMActualBalancedSpinTwoTruncatedMoment P Q Y -
        d4BMHyperbolicBalancedSpinTwoBochnerCoefficient
          (P.s * (P.s - 1)) (Q.s * (Q.s - 1)) *
          d4BMActualScalarTripleTruncatedMoment P Q Y =
      d4BMActualSecondStokesTruncatedDefectMoment P Q Y +
        (d4BMHyperbolicDiagonalGradientShift
          (P.s * (P.s - 1)) (Q.s * (Q.s - 1)) + 1) *
          d4BMActualFirstStokesTruncatedDefectMoment P Q Y := by
  let c := d4BMHyperbolicBalancedSpinTwoBochnerCoefficient
    (P.s * (P.s - 1)) (Q.s * (Q.s - 1))
  let d := d4BMHyperbolicDiagonalGradientShift
    (P.s * (P.s - 1)) (Q.s * (Q.s - 1))
  have hB :=
    integrableOn_d4BMActualBalancedSpinTwoHyperbolicDensityAt_truncatedDomain P Q Y
  have hS := integrableOn_d4BMActualScalarTripleHyperbolicDensityAt_truncatedDomain P Q Y
  have hD2 :=
    integrableOn_d4BMActualSecondStokesTotalDivergence_truncatedDomain P Q Y
  have hD1 :=
    integrableOn_d4BMActualFirstStokesTotalDivergence_truncatedDomain P Q Y
  rw [show d4BMActualSecondStokesTruncatedDefectMoment P Q Y =
      ∫ w in d4BMTruncatedModularDomain Y,
        d4BMActualSecondStokesTotalDivergenceAt P Q w by
      exact d4BM_actualSecondStokesTruncatedDefectMoment_eq_totalDivergence P Q hY,
    show d4BMActualFirstStokesTruncatedDefectMoment P Q Y =
      ∫ w in d4BMTruncatedModularDomain Y,
        d4BMActualFirstStokesTotalDivergenceAt P Q w by
      exact d4BM_actualFirstStokesTruncatedDefectMoment_eq_totalDivergence P Q hY]
  unfold d4BMActualBalancedSpinTwoTruncatedMoment
    d4BMActualScalarTripleTruncatedMoment
  rw [← MeasureTheory.integral_const_mul,
    ← MeasureTheory.integral_sub hB (hS.const_mul c),
    ← MeasureTheory.integral_const_mul,
    ← MeasureTheory.integral_add hD2 (hD1.const_mul (d + 1))]
  apply MeasureTheory.setIntegral_congr_fun
    (isCompact_d4BMTruncatedModularDomain Y).measurableSet
  intro w hw
  have hwcell := (d4BMTruncatedModularDomain_subset_stokesCompactCell Y) hw
  have hy : (1 / 2 : ℝ) ≤ w.2 := hwcell.2.1
  have hD1eq := d4BM_actualFirstStokesDefectDensity_div_heightSq_eq_divergenceAt
    P Q w.1 w.2 hy
  have hD2eq := d4BM_actualSecondStokesDefectDensity_div_heightSq_eq_divergenceAt
    P Q w.1 w.2 hy
  have hpoint := d4BM_actualBalancedSpinTwoDensity_exhaustiveDefectDecomposition
    (d4BMStokesPairCoordinate w) P Q
  dsimp [d4BMActualBalancedSpinTwoHyperbolicDensityAt,
    d4BMActualScalarTripleHyperbolicDensityAt, c, d]
  unfold d4BMActualSecondStokesTotalDivergenceAt
    d4BMActualFirstStokesTotalDivergenceAt
  rw [← hD1eq, ← hD2eq]
  calc
    d4BMActualBalancedSpinTwoDensity (d4BMStokesPairCoordinate w) P Q /
          (w.2 : ℂ) ^ (2 : ℕ) -
        d4BMHyperbolicBalancedSpinTwoBochnerCoefficient
          (P.s * (P.s - 1)) (Q.s * (Q.s - 1)) *
          (d4BMActualFirstStokesScalarDensity (d4BMStokesPairCoordinate w) P Q /
            (w.2 : ℂ) ^ (2 : ℕ)) =
      (d4BMActualBalancedSpinTwoDensity (d4BMStokesPairCoordinate w) P Q -
        d4BMHyperbolicBalancedSpinTwoBochnerCoefficient
          (P.s * (P.s - 1)) (Q.s * (Q.s - 1)) *
          d4BMActualFirstStokesScalarDensity (d4BMStokesPairCoordinate w) P Q) /
            (w.2 : ℂ) ^ (2 : ℕ) := by ring
    _ = (2 *
          d4BMActualSecondStokesDefectDensity (d4BMStokesPairCoordinate w) P Q +
        2 * (d4BMHyperbolicDiagonalGradientShift
          (P.s * (P.s - 1)) (Q.s * (Q.s - 1)) + 1) *
          d4BMActualFirstStokesDefectDensity (d4BMStokesPairCoordinate w) P Q) /
            (w.2 : ℂ) ^ (2 : ℕ) := by rw [hpoint]
    _ = 2 * d4BMActualSecondStokesDefectDensity
            (d4BMStokesPairCoordinate w) P Q / (w.2 : ℂ) ^ (2 : ℕ) +
        (d4BMHyperbolicDiagonalGradientShift
          (P.s * (P.s - 1)) (Q.s * (Q.s - 1)) + 1) *
          (2 * d4BMActualFirstStokesDefectDensity
            (d4BMStokesPairCoordinate w) P Q / (w.2 : ℂ) ^ (2 : ℕ)) := by ring

/-- Premise-free subtype form of the integrated exhaustive decomposition. -/
theorem d4BM_actualBalancedSpinTwoTruncatedMoment_defect_decomposition
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    (Y : {Y : ℝ // 1 ≤ Y}) :
    d4BMActualBalancedSpinTwoTruncatedMoment P Q Y -
        d4BMHyperbolicBalancedSpinTwoBochnerCoefficient
          (P.s * (P.s - 1)) (Q.s * (Q.s - 1)) *
          d4BMActualScalarTripleTruncatedMoment P Q Y =
      d4BMActualSecondStokesTruncatedDefectMoment P Q Y +
        (d4BMHyperbolicDiagonalGradientShift
          (P.s * (P.s - 1)) (Q.s * (Q.s - 1)) + 1) *
          d4BMActualFirstStokesTruncatedDefectMoment P Q Y :=
  d4BM_actualBalancedSpinTwoTruncatedMoment_defect_decomposition_of_one_le
    P Q Y.property

/-- **C-A.9u actual coefficient extraction.**  The complete finite-height failure of the actual
balanced coefficient is exactly the two physical paired cusp-top currents.  All other possible
analytic and tensor remainders have been eliminated. -/
theorem d4BM_actualBalancedSpinTwoTruncatedMoment_eq_pairedCuspTop
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    (Y : {Y : ℝ // 1 ≤ Y}) :
    d4BMActualBalancedSpinTwoTruncatedMoment P Q Y -
        d4BMHyperbolicBalancedSpinTwoBochnerCoefficient
          (P.s * (P.s - 1)) (Q.s * (Q.s - 1)) *
          d4BMActualScalarTripleTruncatedMoment P Q Y =
      d4BMActualSecondStokesPairedCuspTop P Q Y +
        (d4BMHyperbolicDiagonalGradientShift
          (P.s * (P.s - 1)) (Q.s * (Q.s - 1)) + 1) *
          d4BMActualFirstStokesPairedCuspTop P Q Y := by
  rw [d4BM_actualBalancedSpinTwoTruncatedMoment_defect_decomposition P Q Y,
    d4BM_actualSecondStokesTruncatedDefectMoment_eq_pairedCuspTop P Q Y.property,
    d4BM_actualFirstStokesTruncatedDefectMoment_eq_pairedCuspTop P Q Y.property]

/-- Equivalent literal-coordinate version of C-A.9u. -/
theorem d4BM_actualBalancedSpinTwoTruncatedMoment_eq_pairedTruncatedBulk
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    (Y : {Y : ℝ // 1 ≤ Y}) :
    d4BMActualBalancedSpinTwoTruncatedMoment P Q Y -
        d4BMHyperbolicBalancedSpinTwoBochnerCoefficient
          (P.s * (P.s - 1)) (Q.s * (Q.s - 1)) *
          d4BMActualScalarTripleTruncatedMoment P Q Y =
      d4BMActualSecondStokesPairedTruncatedBulk P Q Y +
        (d4BMHyperbolicDiagonalGradientShift
          (P.s * (P.s - 1)) (Q.s * (Q.s - 1)) + 1) *
          d4BMActualFirstStokesPairedTruncatedBulk P Q Y := by
  rw [d4BM_actualBalancedSpinTwoTruncatedMoment_defect_decomposition P Q Y,
    d4BM_actualSecondStokesTruncatedDefectMoment_eq_pairedTruncatedBulk P Q Y.property,
    d4BM_actualFirstStokesTruncatedDefectMoment_eq_pairedTruncatedBulk P Q Y.property]

end
end RHTower
