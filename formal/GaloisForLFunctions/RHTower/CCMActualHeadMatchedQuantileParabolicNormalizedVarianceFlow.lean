import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarParabolicVarianceBalance
import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarParabolicCenteredBoundary

/-!
# Cutoff flow of the literal matched--quantile variance defect

The finite actual-head cutoff is a physical source coordinate, not a disposable approximation.
After normalizing the exact matched-minus-quantile variance defect by the literal head mass, its
one-step update is an explicit globally centred Lorentz flux.  Zero von-Mangoldt admissions have
zero flux, while prime-power admissions retain both their signed orientation and their full
quadratic displacement debt.

This module gives the source-flow identity only.  It supplies neither an Archimedean compensator
nor a cofinal signed bound.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Weighted centroid mean in the literal finite physical head. -/
def ccmActualHeadParabolicCentroidMean (K : ℕ) (c : ℕ → ℝ) : ℝ :=
  (∑ n ∈ Finset.range (K + 1),
    criticalMellinAtomWeight (n + 2) * c (n + 2)) /
      ccmActualHeadParabolicMass K

/-- Mass-normalized weighted centroid variance of a literal finite physical head. -/
def ccmActualHeadParabolicNormalizedCentroidVariance (K : ℕ) (c : ℕ → ℝ) : ℝ :=
  ccmActualHeadParabolicCentroidVariance K c / ccmActualHeadParabolicMass K

/-- The normalized literal strict-cross source: matched centroid variance minus equal-mass
quantile centroid variance. -/
def ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect (K : ℕ) : ℝ :=
  ccmActualHeadParabolicNormalizedCentroidVariance K ccmActualHeadMatchedPolarCentroid -
    ccmActualHeadParabolicNormalizedCentroidVariance K ccmActualHeadQuantilePolarCentroid

/-- One newly admitted prime-power source flux in the cutoff flow.  The old total mass remains
in the coefficient, so this is a genuinely history-weighted flux rather than a local cell term. -/
def ccmActualHeadMatchedQuantileParabolicNormalizedVarianceFlux (K : ℕ) : ℝ :=
  criticalMellinAtomWeight (K + 3) * ccmActualHeadParabolicMass K /
      ccmActualHeadParabolicMass (K + 1) *
    ((ccmActualHeadMatchedPolarCentroid (K + 3) -
        ccmActualHeadParabolicCentroidMean K ccmActualHeadMatchedPolarCentroid) ^ (2 : ℕ) -
      (ccmActualHeadQuantilePolarCentroid (K + 3) -
        ccmActualHeadParabolicCentroidMean K ccmActualHeadQuantilePolarCentroid) ^ (2 : ℕ))

/-- New matched centroid relative to the barycentre of the preceding literal head. -/
def ccmActualHeadMatchedQuantileParabolicCenteredMatchedOffset (K : ℕ) : ℝ :=
  ccmActualHeadMatchedPolarCentroid (K + 3) -
    ccmActualHeadParabolicCentroidMean K ccmActualHeadMatchedPolarCentroid

/-- New matched-to-quantile displacement relative to the corresponding preceding-head mean
displacement. -/
def ccmActualHeadMatchedQuantileParabolicCenteredDisplacement (K : ℕ) : ℝ :=
  ccmActualHeadMatchedQuantilePolarDisplacement (K + 3) -
    (ccmActualHeadParabolicCentroidMean K ccmActualHeadQuantilePolarCentroid -
      ccmActualHeadParabolicCentroidMean K ccmActualHeadMatchedPolarCentroid)

private lemma ccmActualHeadParabolicMass_succ (K : ℕ) :
    ccmActualHeadParabolicMass (K + 1) =
      ccmActualHeadParabolicMass K + criticalMellinAtomWeight (K + 3) := by
  unfold ccmActualHeadParabolicMass
  rw [Finset.sum_range_succ]

private lemma ccmActualHeadParabolicWeightedCentroidSum_succ (K : ℕ) (c : ℕ → ℝ) :
    (∑ n ∈ Finset.range (K + 2),
      criticalMellinAtomWeight (n + 2) * c (n + 2)) =
      (∑ n ∈ Finset.range (K + 1),
        criticalMellinAtomWeight (n + 2) * c (n + 2)) +
        criticalMellinAtomWeight (K + 3) * c (K + 3) := by
  rw [Finset.sum_range_succ]

private lemma ccmActualHeadParabolicWeightedCentroidSqSum_succ (K : ℕ) (c : ℕ → ℝ) :
    (∑ n ∈ Finset.range (K + 2),
      criticalMellinAtomWeight (n + 2) * c (n + 2) ^ (2 : ℕ)) =
      (∑ n ∈ Finset.range (K + 1),
        criticalMellinAtomWeight (n + 2) * c (n + 2) ^ (2 : ℕ)) +
        criticalMellinAtomWeight (K + 3) * c (K + 3) ^ (2 : ℕ) := by
  rw [Finset.sum_range_succ]

private lemma ccmActualHeadParabolicNormalizedCentroidVariance_succ_sub
    (K : ℕ) (c : ℕ → ℝ) :
    ccmActualHeadParabolicNormalizedCentroidVariance (K + 1) c -
        ccmActualHeadParabolicNormalizedCentroidVariance K c =
      criticalMellinAtomWeight (K + 3) * ccmActualHeadParabolicMass K /
          ccmActualHeadParabolicMass (K + 1) *
        (c (K + 3) - ccmActualHeadParabolicCentroidMean K c) ^ (2 : ℕ) := by
  have hM : 0 < ccmActualHeadParabolicMass K := ccmActualHeadParabolicMass_pos K
  have hM' : 0 < ccmActualHeadParabolicMass (K + 1) :=
    ccmActualHeadParabolicMass_pos (K + 1)
  have hMsum : ccmActualHeadParabolicMass K + criticalMellinAtomWeight (K + 3) ≠ 0 := by
    rw [← ccmActualHeadParabolicMass_succ]
    exact hM'.ne'
  rw [ccmActualHeadParabolicNormalizedCentroidVariance,
    ccmActualHeadParabolicNormalizedCentroidVariance,
    ccmActualHeadParabolicCentroidVariance,
    ccmActualHeadParabolicCentroidVariance,
    ccmActualHeadParabolicMass_succ,
    ccmActualHeadParabolicWeightedCentroidSum_succ,
    ccmActualHeadParabolicWeightedCentroidSqSum_succ]
  unfold ccmActualHeadParabolicCentroidMean
  field_simp [hM.ne', hMsum]
  ring

/-- **Exact normalized cutoff-flow law.**  Passing from one literal finite head to the next
changes the mass-normalized strict-cross source by precisely the globally centred flux of the
newly admitted atom. -/
theorem ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect_succ_sub_eq_flux
    (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect (K + 1) -
        ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect K =
      ccmActualHeadMatchedQuantileParabolicNormalizedVarianceFlux K := by
  unfold ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect
    ccmActualHeadMatchedQuantileParabolicNormalizedVarianceFlux
  rw [sub_sub_sub_comm,
    ccmActualHeadParabolicNormalizedCentroidVariance_succ_sub,
    ccmActualHeadParabolicNormalizedCentroidVariance_succ_sub]
  ring

/-- The normalized variance defect is exactly the original literal strict-cross source current,
divided only by the positive physical head mass. -/
theorem ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect_eq_sourceCurrent
    (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect K =
      ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
        (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) /
        ccmActualHeadParabolicMass K := by
  unfold ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect
    ccmActualHeadParabolicNormalizedCentroidVariance
  rw [← sub_div,
    ← ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_centroidVariance]

/-- The cutoff flux retains its exact signed covariance--debt structure in centred coordinates.
Its first term is signed; its second term is the full nonnegative square debt. -/
theorem ccmActualHeadMatchedQuantileParabolicNormalizedVarianceFlux_eq_centered_signed_increment
    (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicNormalizedVarianceFlux K =
      -(criticalMellinAtomWeight (K + 3) * ccmActualHeadParabolicMass K /
        ccmActualHeadParabolicMass (K + 1)) *
        (2 * ccmActualHeadMatchedQuantileParabolicCenteredMatchedOffset K *
            ccmActualHeadMatchedQuantileParabolicCenteredDisplacement K +
          ccmActualHeadMatchedQuantileParabolicCenteredDisplacement K ^ (2 : ℕ)) := by
  unfold ccmActualHeadMatchedQuantileParabolicNormalizedVarianceFlux
    ccmActualHeadMatchedQuantileParabolicCenteredMatchedOffset
    ccmActualHeadMatchedQuantileParabolicCenteredDisplacement
  rw [ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement]
  ring

/-- The literal cutoff flux is exactly stationary at every non-prime-power admission. -/
theorem ccmActualHeadMatchedQuantileParabolicNormalizedVarianceFlux_eq_zero_of_not_isPrimePow
    (K : ℕ) (hK : ¬ IsPrimePow (K + 3)) :
    ccmActualHeadMatchedQuantileParabolicNormalizedVarianceFlux K = 0 := by
  unfold ccmActualHeadMatchedQuantileParabolicNormalizedVarianceFlux
  have hw : criticalMellinAtomWeight (K + 3) = 0 := by
    rw [criticalMellinAtomWeight_eq_div_sqrt,
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hK, zero_div]
  rw [hw]
  ring

end RHTower
