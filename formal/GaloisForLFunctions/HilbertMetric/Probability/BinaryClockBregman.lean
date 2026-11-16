import GaloisForLFunctions.HilbertMetric.Probability.BregmanCalibration
import GaloisForLFunctions.HTGeometry.BinaryFisherClockEstimator

/-!
# Bregman forecasts of the binary Fisher clock

The binary escort source is an actual probability law. Its calibrated
clock reading is therefore the unique target of three different losses.
Their risk gaps distinguish Fisher variance from forecast miscalibration.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HilbertMetric.Probability
open GaloisForLFunctions.HTGeometry
noncomputable section

/-- The binary escort clock's normalized law at the physical parameter. -/
def binaryEscortLaw (t : ℝ) : FiniteProbabilityLaw (Fin 2) where
  prob := finiteExponentialTilt binaryEscortWeight binaryEscortScore t
  nonneg i := (finiteExponentialTilt_pos
    (by simp [binaryEscortWeight]) binaryEscortWeight_sum t i).le
  sum_prob := finiteExponentialTilt_sum
    (by simp [binaryEscortWeight]) binaryEscortWeight_sum t

/-- Every generator has an exact forecast gap at the calibration point. -/
theorem binaryClock_bregman_gap (φ : ℝ → ℝ) (t q : ℝ) :
    bregmanRisk (binaryEscortLaw t) φ (binaryFisherClockEstimator t) q =
      bregmanRisk (binaryEscortLaw t) φ (binaryFisherClockEstimator t) t +
        scalarBregman φ t q := by
  have hm : finiteWeightedMean (binaryEscortLaw t).prob
      (binaryFisherClockEstimator t) = t := binaryFisherEstimator_unbiased t
  rw [bregmanRisk_mean_split, hm]

/-- Least-squares risk is reciprocal Fisher information plus squared clock bias. -/
theorem binaryClock_square_risk (t q : ℝ) :
    (∑ i, (binaryEscortLaw t).prob i *
      (binaryFisherClockEstimator t i - q) ^ (2 : ℕ)) =
      (finiteTiltVariance binaryEscortWeight binaryEscortScore t)⁻¹ +
        (t - q) ^ (2 : ℕ) := by
  have h := binaryClock_bregman_gap (fun x => x ^ (2 : ℕ)) t q
  simp only [bregmanRisk, scalarBregman_square] at h
  change _ = binaryFisherEstimatorVariance t + (t - q) ^ (2 : ℕ) at h
  rwa [binaryFisherEstimatorVariance_formula] at h

/-- Quartic miscalibration controls squared clock error with an explicit coefficient. -/
theorem binaryClock_quartic_gap (t q : ℝ) :
    bregmanRisk (binaryEscortLaw t) quarticGenerator (binaryFisherClockEstimator t) q -
      bregmanRisk (binaryEscortLaw t) quarticGenerator (binaryFisherClockEstimator t) t =
        (t - q) ^ (2 : ℕ) * ((t + q) ^ (2 : ℕ) + 2 * q ^ (2 : ℕ) + 1) := by
  rw [binaryClock_bregman_gap, scalarBregman_quartic]
  ring

/-- Changing the strictly convex generator preserves the calibrated clock target. -/
theorem binaryClock_quartic_minimizer (t q : ℝ) :
    (∀ r, bregmanRisk (binaryEscortLaw t) quarticGenerator (binaryFisherClockEstimator t) q ≤
      bregmanRisk (binaryEscortLaw t) quarticGenerator (binaryFisherClockEstimator t) r) ↔
        q = t := by
  rw [quarticRisk_minimizer_iff]
  change (q = binaryFisherEstimatorMean t t) ↔ q = t
  rw [binaryFisherEstimator_unbiased]

theorem binaryClock_exponential_minimizer (t q : ℝ) :
    (∀ r, bregmanRisk (binaryEscortLaw t) Real.exp (binaryFisherClockEstimator t) q ≤
      bregmanRisk (binaryEscortLaw t) Real.exp (binaryFisherClockEstimator t) r) ↔
        q = t := by
  rw [exponentialRisk_minimizer_iff]
  change (q = binaryFisherEstimatorMean t t) ↔ q = t
  rw [binaryFisherEstimator_unbiased]

/-- Away from calibration, the loss selects the actual mean of the clock reading. -/
theorem binaryClock_misspecified_target (calibration actual q : ℝ) :
    (∀ r, bregmanRisk (binaryEscortLaw actual) quarticGenerator
      (binaryFisherClockEstimator calibration) q ≤
      bregmanRisk (binaryEscortLaw actual) quarticGenerator
        (binaryFisherClockEstimator calibration) r) ↔
      q = calibration +
        (finiteTiltMean binaryEscortWeight binaryEscortScore actual -
          finiteTiltMean binaryEscortWeight binaryEscortScore calibration) /
        finiteTiltVariance binaryEscortWeight binaryEscortScore calibration := by
  rw [quarticRisk_minimizer_iff]
  change (q = binaryFisherEstimatorMean calibration actual) ↔ _
  rw [binaryFisherEstimatorMean_formula]

#print axioms binaryClock_square_risk
#print axioms binaryClock_quartic_gap
#print axioms binaryClock_exponential_minimizer
#print axioms binaryClock_misspecified_target

end
end GaloisForLFunctions.HilbertMetric.Probability
