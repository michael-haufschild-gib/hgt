import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantilePolarParabolicOrientationLedger

/-!
# Global variance balance for the literal matched--quantile source

The all-pair parabolic source current has a forced quadratic displacement debt.  That debt is
not a separate error term: after retaining its oriented all-pair credit, it is exactly absorbed
into the difference between the weighted centroid variances of the literal matched cells and
their equal-mass quantile cells.  This is a finite, source-faithful identity.  It supplies no
sign or cofinal bound; any such bound must control this collective variance defect itself.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Barycentre of one equal-mass quantile polar cell in physical mass coordinate. -/
def ccmActualHeadQuantilePolarCentroid (n : ℕ) : ℝ :=
  (ccmActualHeadQuantilePolarCoordinate n +
    ccmActualHeadQuantilePolarCoordinate (n + 1)) / 2

/-- Unnormalised weighted centroid variance of the finite physical head. -/
def ccmActualHeadParabolicCentroidVariance (K : ℕ) (c : ℕ → ℝ) : ℝ :=
  ccmActualHeadParabolicMass K *
      (∑ n ∈ Finset.range (K + 1),
        criticalMellinAtomWeight (n + 2) * c (n + 2) ^ (2 : ℕ)) -
    (∑ n ∈ Finset.range (K + 1),
      criticalMellinAtomWeight (n + 2) * c (n + 2)) ^ (2 : ℕ)

/-- Common cubic-width contribution to a parabolic aggregate form.  It cancels between the
literal matched and equal-mass quantile heads. -/
def ccmActualHeadParabolicCubicWidthCorrection (K : ℕ) : ℝ :=
  ccmActualHeadParabolicMass K *
    (∑ n ∈ Finset.range (K + 1),
      criticalMellinAtomWeight (n + 2) ^ (3 : ℕ)) / 12

theorem ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement (n : ℕ) :
    ccmActualHeadQuantilePolarCentroid n =
      ccmActualHeadMatchedPolarCentroid n +
        ccmActualHeadMatchedQuantilePolarDisplacement n := by
  unfold ccmActualHeadQuantilePolarCentroid ccmActualHeadMatchedPolarCentroid
  rw [ccmActualHeadMatchedQuantilePolar_lower_eq_lower_add_displacement,
    ccmActualHeadMatchedQuantilePolar_upper_eq_upper_add_displacement]
  ring

private theorem ccmParabolicMoment_two_eq_centroid_sq_add_cubic
    (a b : ℝ) :
    ccmParabolicMoment a b 2 =
      (b - a) * ((a + b) / 2) ^ (2 : ℕ) / 2 + (b - a) ^ (3 : ℕ) / 24 := by
  simp [ccmParabolicMoment]
  ring

private theorem ccmActualHeadMatchedParabolicMoment_two_eq_centroid_sq_add_cubic
    (n : ℕ) :
    ccmActualHeadMatchedParabolicMoment n 2 =
      criticalMellinAtomWeight n * ccmActualHeadMatchedPolarCentroid n ^ (2 : ℕ) / 2 +
        criticalMellinAtomWeight n ^ (3 : ℕ) / 24 := by
  rw [ccmActualHeadMatchedParabolicMoment,
    ccmParabolicMoment_two_eq_centroid_sq_add_cubic,
    ccmActualHeadMatchedPolarUpper_sub_lower_eq_atomWeight]
  rfl

private theorem ccmActualHeadQuantileParabolicMoment_one_eq_weight_mul_centroid
    (n : ℕ) :
    ccmActualHeadQuantileParabolicMoment n 1 =
      criticalMellinAtomWeight n * ccmActualHeadQuantilePolarCentroid n := by
  change (ccmActualHeadQuantilePolarCoordinate (n + 1) ^ (2 : ℕ) -
      ccmActualHeadQuantilePolarCoordinate n ^ (2 : ℕ)) / 2 =
    criticalMellinAtomWeight n *
      ((ccmActualHeadQuantilePolarCoordinate n +
        ccmActualHeadQuantilePolarCoordinate (n + 1)) / 2)
  rw [← ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight]
  ring

private theorem ccmActualHeadQuantileParabolicMoment_two_eq_centroid_sq_add_cubic
    (n : ℕ) :
    ccmActualHeadQuantileParabolicMoment n 2 =
      criticalMellinAtomWeight n * ccmActualHeadQuantilePolarCentroid n ^ (2 : ℕ) / 2 +
        criticalMellinAtomWeight n ^ (3 : ℕ) / 24 := by
  rw [ccmActualHeadQuantileParabolicMoment,
    ccmParabolicMoment_two_eq_centroid_sq_add_cubic]
  rw [show ccmActualHeadQuantilePolarCoordinate (n + 1) -
      ccmActualHeadQuantilePolarCoordinate n = criticalMellinAtomWeight n by
        rw [ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight]]
  rfl

private theorem ccmActualHeadMatchedParabolicAggregate_one (K : ℕ) :
    ccmActualHeadMatchedParabolicAggregate K 1 =
      ∑ n ∈ Finset.range (K + 1),
        criticalMellinAtomWeight (n + 2) * ccmActualHeadMatchedPolarCentroid (n + 2) := by
  simp only [ccmActualHeadMatchedParabolicAggregate, Finset.sum_apply]
  simp_rw [ccmActualHeadMatchedParabolicMoment_one_eq_weight_mul_centroid]

private theorem ccmActualHeadMatchedParabolicAggregate_two (K : ℕ) :
    ccmActualHeadMatchedParabolicAggregate K 2 =
      ∑ n ∈ Finset.range (K + 1),
        (criticalMellinAtomWeight (n + 2) * ccmActualHeadMatchedPolarCentroid (n + 2) ^ (2 : ℕ) / 2 +
          criticalMellinAtomWeight (n + 2) ^ (3 : ℕ) / 24) := by
  simp only [ccmActualHeadMatchedParabolicAggregate, Finset.sum_apply]
  simp_rw [ccmActualHeadMatchedParabolicMoment_two_eq_centroid_sq_add_cubic]

private theorem ccmActualHeadQuantileParabolicAggregate_one (K : ℕ) :
    ccmActualHeadQuantileParabolicAggregate K 1 =
      ∑ n ∈ Finset.range (K + 1),
        criticalMellinAtomWeight (n + 2) * ccmActualHeadQuantilePolarCentroid (n + 2) := by
  simp only [ccmActualHeadQuantileParabolicAggregate, Finset.sum_apply]
  simp_rw [ccmActualHeadQuantileParabolicMoment_one_eq_weight_mul_centroid]

private theorem ccmActualHeadQuantileParabolicAggregate_two (K : ℕ) :
    ccmActualHeadQuantileParabolicAggregate K 2 =
      ∑ n ∈ Finset.range (K + 1),
        (criticalMellinAtomWeight (n + 2) * ccmActualHeadQuantilePolarCentroid (n + 2) ^ (2 : ℕ) / 2 +
          criticalMellinAtomWeight (n + 2) ^ (3 : ℕ) / 24) := by
  simp only [ccmActualHeadQuantileParabolicAggregate, Finset.sum_apply]
  simp_rw [ccmActualHeadQuantileParabolicMoment_two_eq_centroid_sq_add_cubic]

private theorem sum_weight_centroid_sq_add_cubic
    (K : ℕ) (c : ℕ → ℝ) :
    2 * ccmActualHeadParabolicMass K *
        (∑ n ∈ Finset.range (K + 1),
          (criticalMellinAtomWeight (n + 2) * c (n + 2) ^ (2 : ℕ) / 2 +
            criticalMellinAtomWeight (n + 2) ^ (3 : ℕ) / 24)) =
      ccmActualHeadParabolicMass K *
        (∑ n ∈ Finset.range (K + 1),
          criticalMellinAtomWeight (n + 2) * c (n + 2) ^ (2 : ℕ)) +
      ccmActualHeadParabolicCubicWidthCorrection K := by
  rw [Finset.sum_add_distrib]
  rw [← Finset.sum_div, ← Finset.sum_div]
  unfold ccmActualHeadParabolicCubicWidthCorrection
  ring

theorem ccmActualHeadMatchedParabolicAggregate_form_eq_centroidVariance_add_cubic
    (K : ℕ) :
    ccmParabolicForm (ccmActualHeadMatchedParabolicAggregate K) =
      ccmActualHeadParabolicCentroidVariance K ccmActualHeadMatchedPolarCentroid +
        ccmActualHeadParabolicCubicWidthCorrection K := by
  rw [ccmParabolicForm,
    ccmActualHeadMatchedParabolicAggregate_zero,
    ccmActualHeadMatchedParabolicAggregate_one,
    ccmActualHeadMatchedParabolicAggregate_two,
    sum_weight_centroid_sq_add_cubic]
  unfold ccmActualHeadParabolicCentroidVariance
  ring

theorem ccmActualHeadQuantileParabolicAggregate_form_eq_centroidVariance_add_cubic
    (K : ℕ) :
    ccmParabolicForm (ccmActualHeadQuantileParabolicAggregate K) =
      ccmActualHeadParabolicCentroidVariance K ccmActualHeadQuantilePolarCentroid +
        ccmActualHeadParabolicCubicWidthCorrection K := by
  rw [ccmParabolicForm,
    ccmActualHeadQuantileParabolicAggregate_zero,
    ccmActualHeadQuantileParabolicAggregate_one,
    ccmActualHeadQuantileParabolicAggregate_two,
    sum_weight_centroid_sq_add_cubic]
  unfold ccmActualHeadParabolicCentroidVariance
  ring

/-- **Global variance balance.** The literal source-boundary codiagonal is exactly the difference
between matched and equal-mass-quantile weighted centroid variances.  The full squared
displacement debt is retained inside the quantile variance; it has not been bounded or discarded.
-/
theorem ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_centroidVariance
    (K : ℕ) :
    ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
        (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) =
      ccmActualHeadParabolicCentroidVariance K ccmActualHeadMatchedPolarCentroid -
        ccmActualHeadParabolicCentroidVariance K ccmActualHeadQuantilePolarCentroid := by
  rw [ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary,
    ccmActualHeadMatchedParabolicAggregate_form_eq_centroidVariance_add_cubic,
    ccmActualHeadQuantileParabolicAggregate_form_eq_centroidVariance_add_cubic]
  ring

/-- **Debt cancellation law.** The signed orientation ledger and every squared displacement debt
combine into one exact physical variance defect.  A valid global producer must therefore control
this variance difference, rather than attempting a local sign for either summand. -/
theorem ccmActualHeadMatchedQuantileParabolicOrientationDebt_eq_centroidVarianceDifference
    (K : ℕ) :
    -ccmActualHeadMatchedQuantileParabolicOrientationLedgerSum K -
        ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum K =
      ccmActualHeadParabolicCentroidVariance K ccmActualHeadMatchedPolarCentroid -
        ccmActualHeadParabolicCentroidVariance K ccmActualHeadQuantilePolarCentroid := by
  rw [← ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_centroidVariance,
    ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_neg_orientationLedger_sub_debt]

end RHTower
