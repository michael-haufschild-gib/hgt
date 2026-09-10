import GaloisForLFunctions.HTGeometry.ResponsePolarizationBinaryWitness

/-!
# Exact locally calibrated estimators for binary Fisher time

The Cramér--Rao relation in arXiv:2605.03958, equation (11), applied to the
binary escort clock. A constructed estimator is unbiased and has unit
response at its calibration point, with variance exactly reciprocal Fisher
information. No fixed two-outcome estimator is globally unbiased for the
unbounded log-odds parameter.
-/
open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Locally efficient reading calibrated at a chosen log-odds parameter. -/
def binaryFisherClockEstimator (calibration : ℝ) (i : Fin 2) : ℝ :=
  calibration + (binaryEscortScore i - finiteTiltMean binaryEscortWeight binaryEscortScore calibration) /
    finiteTiltVariance binaryEscortWeight binaryEscortScore calibration

/-- Actual expectation under the physical parameter, distinct from the calibration parameter. -/
def binaryFisherEstimatorMean (calibration actual : ℝ) : ℝ :=
  ∑ i, finiteExponentialTilt binaryEscortWeight binaryEscortScore actual i *
    binaryFisherClockEstimator calibration i

/-- Actual centered estimation variance at calibration. -/
def binaryFisherEstimatorVariance (calibration : ℝ) : ℝ :=
  ∑ i, finiteExponentialTilt binaryEscortWeight binaryEscortScore calibration i *
    (binaryFisherClockEstimator calibration i - calibration) ^ 2

theorem binaryFisherEstimatorMean_formula (calibration actual : ℝ) :
    binaryFisherEstimatorMean calibration actual = calibration +
      (finiteTiltMean binaryEscortWeight binaryEscortScore actual -
        finiteTiltMean binaryEscortWeight binaryEscortScore calibration) /
      finiteTiltVariance binaryEscortWeight binaryEscortScore calibration := by
  unfold binaryFisherEstimatorMean binaryFisherClockEstimator
  have hs := finiteExponentialTilt_sum
    (r := binaryEscortScore) (by simp [binaryEscortWeight]) binaryEscortWeight_sum actual
  calc
    _ = ∑ i, (calibration * finiteExponentialTilt binaryEscortWeight binaryEscortScore actual i +
        (finiteExponentialTilt binaryEscortWeight binaryEscortScore actual i * binaryEscortScore i -
          finiteTiltMean binaryEscortWeight binaryEscortScore calibration *
            finiteExponentialTilt binaryEscortWeight binaryEscortScore actual i) /
          finiteTiltVariance binaryEscortWeight binaryEscortScore calibration) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div,
        Finset.sum_sub_distrib, ← Finset.mul_sum, hs]
      simp only [mul_one]
      rfl

/-- Local unbiasedness is proved for the constructed estimator, never assumed. -/
theorem binaryFisherEstimator_unbiased (calibration : ℝ) :
    binaryFisherEstimatorMean calibration calibration = calibration := by
  rw [binaryFisherEstimatorMean_formula]
  simp

/-- The expectation responds at unit rate to the physical parameter at calibration. -/
theorem binaryFisherEstimator_unit_response (calibration : ℝ) :
    HasDerivAt (binaryFisherEstimatorMean calibration) 1 calibration := by
  have hp := hasDerivAt_finiteTiltMean (r := binaryEscortScore)
    (by simp [binaryEscortWeight]) binaryEscortWeight_sum calibration
  have hv : finiteTiltVariance binaryEscortWeight binaryEscortScore calibration ≠ 0 := by
    rw [binary_variance]
    positivity
  have h := ((hp.sub_const (finiteTiltMean binaryEscortWeight binaryEscortScore calibration)).div_const
    (finiteTiltVariance binaryEscortWeight binaryEscortScore calibration)).const_add calibration
  rw [div_self hv] at h
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t =>
    binaryFisherEstimatorMean_formula calibration t)

/-- Exact reciprocal-Fisher variance of an actual finite random variable. -/
theorem binaryFisherEstimatorVariance_formula (calibration : ℝ) :
    binaryFisherEstimatorVariance calibration =
      (finiteTiltVariance binaryEscortWeight binaryEscortScore calibration)⁻¹ := by
  have hv : finiteTiltVariance binaryEscortWeight binaryEscortScore calibration ≠ 0 := by
    rw [binary_variance]
    positivity
  unfold binaryFisherEstimatorVariance binaryFisherClockEstimator
  have he : (∑ i, finiteExponentialTilt binaryEscortWeight binaryEscortScore calibration i *
      (calibration + (binaryEscortScore i - finiteTiltMean binaryEscortWeight binaryEscortScore calibration) /
        finiteTiltVariance binaryEscortWeight binaryEscortScore calibration - calibration) ^ 2) =
      finiteTiltVariance binaryEscortWeight binaryEscortScore calibration /
        finiteTiltVariance binaryEscortWeight binaryEscortScore calibration ^ 2 := by
    rw [finiteTiltVariance, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  field_simp

/-- The Cramér--Rao product is exactly one at every finite clock calibration. -/
theorem binaryFisherEstimator_cramer_rao_equality (calibration : ℝ) :
    binaryFisherEstimatorVariance calibration *
      finiteTiltVariance binaryEscortWeight binaryEscortScore calibration = 1 := by
  rw [binaryFisherEstimatorVariance_formula]
  apply inv_mul_cancel₀
  rw [binary_variance]
  positivity

/-- A single two-outcome reading cannot be globally unbiased for an unbounded time label. -/
theorem binaryFisherClock_no_global_unbiased_estimator :
    ¬ ∃ estimate : Fin 2 → ℝ, ∀ t : ℝ,
      (∑ i, finiteExponentialTilt binaryEscortWeight binaryEscortScore t i * estimate i) = t := by
  rintro ⟨estimate, h⟩
  let M := max (estimate 0) (estimate 1)
  have hb : ∀ t : ℝ,
      (∑ i, finiteExponentialTilt binaryEscortWeight binaryEscortScore t i * estimate i) ≤ M := by
    intro t
    have hs := finiteExponentialTilt_sum (r := binaryEscortScore)
      (by simp [binaryEscortWeight]) binaryEscortWeight_sum t
    calc
      _ ≤ ∑ i, finiteExponentialTilt binaryEscortWeight binaryEscortScore t i * M := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left
        · fin_cases i
          · exact le_max_left _ _
          · exact le_max_right _ _
        · apply le_of_lt
          exact finiteExponentialTilt_pos (by simp [binaryEscortWeight]) binaryEscortWeight_sum t i
      _ = M := by rw [← Finset.sum_mul, hs, one_mul]
  have hh := hb (M + 1)
  rw [h (M + 1)] at hh
  linarith

end GaloisForLFunctions.HTGeometry
