import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarCovarianceHardCore
import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarParabolicSourceRelativeOffsetIncrement

/-!
# Exterior two-moment producer for literal matched--quantile covariance

The SP-E/CCM hard core is a signed covariance.  This module identifies its minimal interacting
pre-scalar carrier: two literal source-moment vectors in a real two-plane, paired by its exterior
form.  A newly admitted atom adds collinear directions to both vectors, hence has zero self-area.
Only its interaction with full retained history updates the covariance.

This is not a bound.  It rules out any proposed local self-energy control and exposes the exact
nonlinear history term that a source-faithful cancellation producer must control.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- The exterior pairing on the two source moments. -/
def ccmActualHeadTwoMomentExteriorPairing (v w : Fin 2 → ℝ) : ℝ :=
  v 0 * w 1 - v 1 * w 0

/-- First literal source moment vector: mass and displacement-weighted mass. -/
def ccmActualHeadMatchedQuantileDisplacementMomentVector (K : ℕ) : Fin 2 → ℝ :=
  ![ccmActualHeadParabolicMass K,
    ∑ n ∈ Finset.range (K + 1),
      criticalMellinAtomWeight (n + 2) *
        ccmActualHeadMatchedQuantilePolarDisplacement (n + 2)]

/-- Second literal source moment vector: centroid mass and displacement-centroid mass. -/
def ccmActualHeadMatchedQuantileCentroidDisplacementMomentVector (K : ℕ) : Fin 2 → ℝ :=
  ![∑ n ∈ Finset.range (K + 1),
      criticalMellinAtomWeight (n + 2) * ccmActualHeadMatchedPolarCentroid (n + 2),
    ∑ n ∈ Finset.range (K + 1),
      criticalMellinAtomWeight (n + 2) *
        ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) *
          ccmActualHeadMatchedPolarCentroid (n + 2)]

/-- The unique signed covariance is exactly the exterior pairing of the two actual source
moment vectors. -/
theorem ccmActualHeadMatchedQuantileParabolicDisplacementCentroidCovariance_eq_exteriorPairing
    (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicDisplacementCentroidCovariance K =
      ccmActualHeadTwoMomentExteriorPairing
        (ccmActualHeadMatchedQuantileDisplacementMomentVector K)
        (ccmActualHeadMatchedQuantileCentroidDisplacementMomentVector K) := by
  unfold ccmActualHeadMatchedQuantileParabolicDisplacementCentroidCovariance
    ccmActualHeadTwoMomentExteriorPairing
    ccmActualHeadMatchedQuantileDisplacementMomentVector
    ccmActualHeadMatchedQuantileCentroidDisplacementMomentVector
  simp

/-- Direction of one newly admitted literal atom in the exterior two-moment source plane. -/
def ccmActualHeadMatchedQuantileAtomExteriorDirection (n : ℕ) : Fin 2 → ℝ :=
  ![1, ccmActualHeadMatchedQuantilePolarDisplacement n]

theorem ccmActualHeadMatchedQuantileDisplacementMomentVector_succ (K : ℕ) :
    ccmActualHeadMatchedQuantileDisplacementMomentVector (K + 1) =
      ccmActualHeadMatchedQuantileDisplacementMomentVector K +
        criticalMellinAtomWeight (K + 3) •
          ccmActualHeadMatchedQuantileAtomExteriorDirection (K + 3) := by
  funext i
  fin_cases i <;>
    simp [ccmActualHeadMatchedQuantileDisplacementMomentVector,
      ccmActualHeadMatchedQuantileAtomExteriorDirection,
      ccmActualHeadParabolicMass, Finset.sum_range_succ]

theorem ccmActualHeadMatchedQuantileCentroidDisplacementMomentVector_succ (K : ℕ) :
    ccmActualHeadMatchedQuantileCentroidDisplacementMomentVector (K + 1) =
      ccmActualHeadMatchedQuantileCentroidDisplacementMomentVector K +
        (criticalMellinAtomWeight (K + 3) * ccmActualHeadMatchedPolarCentroid (K + 3)) •
          ccmActualHeadMatchedQuantileAtomExteriorDirection (K + 3) := by
  funext i
  fin_cases i
  · simp [ccmActualHeadMatchedQuantileCentroidDisplacementMomentVector,
      ccmActualHeadMatchedQuantileAtomExteriorDirection, Finset.sum_range_succ]
  · simp [ccmActualHeadMatchedQuantileCentroidDisplacementMomentVector,
      ccmActualHeadMatchedQuantileAtomExteriorDirection, Finset.sum_range_succ]
    ring

/-- One atom has zero exterior self-area.  Therefore the covariance has no local quadratic
admission term: every nonzero update is a signed interaction with previously retained history. -/
theorem ccmActualHeadMatchedQuantileAtomExteriorDirection_self (n : ℕ) :
    ccmActualHeadTwoMomentExteriorPairing
      (ccmActualHeadMatchedQuantileAtomExteriorDirection n)
      (ccmActualHeadMatchedQuantileAtomExteriorDirection n) = 0 := by
  simp [ccmActualHeadTwoMomentExteriorPairing,
    ccmActualHeadMatchedQuantileAtomExteriorDirection]

/-- **Exterior history-update law.** The actual covariance update is linear in the new prime
mass and consists only of its two exterior interactions with full finite history.  The would-be
quadratic self term vanishes identically because both new source marks lie on the same direction. -/
theorem ccmActualHeadMatchedQuantileParabolicDisplacementCentroidCovariance_succ_sub_eq_exteriorHistory
    (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicDisplacementCentroidCovariance (K + 1) -
      ccmActualHeadMatchedQuantileParabolicDisplacementCentroidCovariance K =
      criticalMellinAtomWeight (K + 3) *
        (ccmActualHeadTwoMomentExteriorPairing
            (ccmActualHeadMatchedQuantileAtomExteriorDirection (K + 3))
            (ccmActualHeadMatchedQuantileCentroidDisplacementMomentVector K) +
          ccmActualHeadMatchedPolarCentroid (K + 3) *
            ccmActualHeadTwoMomentExteriorPairing
              (ccmActualHeadMatchedQuantileDisplacementMomentVector K)
              (ccmActualHeadMatchedQuantileAtomExteriorDirection (K + 3))) := by
  rw [ccmActualHeadMatchedQuantileParabolicDisplacementCentroidCovariance_eq_exteriorPairing,
    ccmActualHeadMatchedQuantileParabolicDisplacementCentroidCovariance_eq_exteriorPairing,
    ccmActualHeadMatchedQuantileDisplacementMomentVector_succ,
    ccmActualHeadMatchedQuantileCentroidDisplacementMomentVector_succ]
  unfold ccmActualHeadTwoMomentExteriorPairing
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Zero von-Mangoldt admissions leave the full exterior covariance stationary, so every
nontrivial update of this exact source producer is supported at a literal prime power. -/
theorem ccmActualHeadMatchedQuantileParabolicDisplacementCentroidCovariance_succ_eq_of_not_isPrimePow
    (K : ℕ) (hK : ¬ IsPrimePow (K + 3)) :
    ccmActualHeadMatchedQuantileParabolicDisplacementCentroidCovariance (K + 1) =
      ccmActualHeadMatchedQuantileParabolicDisplacementCentroidCovariance K := by
  rw [← sub_eq_zero,
    ccmActualHeadMatchedQuantileParabolicDisplacementCentroidCovariance_succ_sub_eq_exteriorHistory,
    criticalMellinAtomWeight_eq_zero_of_not_isPrimePow hK]
  ring

end RHTower
