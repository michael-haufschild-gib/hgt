import GaloisForLFunctions.RHTower.ProjectiveGaussianRateDistortion

/-!
# Operational effective-support separation

The amplitude target `1 - eta` corresponds for pure states to trace-distance
radius `sqrt (2 * eta - eta^(2 : ℕ))`.  This file compares projective water entropy
with hard support at half that operational radius, the sharper truncation
scale used in current geometric recurrence bounds.
-/

noncomputable section

namespace RHTower

/-- Trace-distance radius corresponding to fidelity target `(1 - eta)^(2 : ℕ)`. -/
def binaryTraceDistanceRadius (eta : ℝ) : ℝ :=
  Real.sqrt (2 * eta - eta ^ (2 : ℕ))

/-- The half-trace-distance tail scale used for the sharper hard-support
comparison. -/
def binaryTraceSupportTail (eta : ℝ) : ℝ :=
  binaryTraceDistanceRadius eta / 2

theorem binaryTraceDistanceRadius_sq
    {eta : ℝ} (heta0 : 0 ≤ eta) (heta2 : eta ≤ 2) :
    binaryTraceDistanceRadius eta ^ (2 : ℕ) = 1 - (1 - eta) ^ (2 : ℕ) := by
  have hrad : 0 ≤ 2 * eta - eta ^ (2 : ℕ) := by
    nlinarith [mul_nonneg heta0 (sub_nonneg.mpr heta2)]
  rw [binaryTraceDistanceRadius, Real.sq_sqrt hrad]
  ring

/-- Below amplitude defect `2/5`, the half-trace-distance support tail is
strictly larger than the amplitude defect itself. -/
theorem eta_lt_binaryTraceSupportTail
    {eta : ℝ} (heta0 : 0 < eta) (heta2fifths : eta < 2 / 5) :
    eta < binaryTraceSupportTail eta := by
  have hrad : 0 ≤ 2 * eta - eta ^ (2 : ℕ) := by
    nlinarith [sq_nonneg eta]
  have hsqrt_nonneg : 0 ≤ Real.sqrt (2 * eta - eta ^ (2 : ℕ)) :=
    Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt (2 * eta - eta ^ (2 : ℕ)) ^ (2 : ℕ) =
      2 * eta - eta ^ (2 : ℕ) := Real.sq_sqrt hrad
  have hgap : 4 * eta ^ (2 : ℕ) < 2 * eta - eta ^ (2 : ℕ) := by
    nlinarith [mul_pos heta0 (by linarith : 0 < 2 - 5 * eta)]
  simp only [binaryTraceSupportTail, binaryTraceDistanceRadius]
  nlinarith

theorem binaryTraceSupportTail_lt_half
    {eta : ℝ} (heta0 : 0 < eta) (heta2fifths : eta < 2 / 5) :
    binaryTraceSupportTail eta < 1 / 2 := by
  have hrad : 0 ≤ 2 * eta - eta ^ (2 : ℕ) := by
    nlinarith [sq_nonneg eta]
  have hsqrt_nonneg : 0 ≤ Real.sqrt (2 * eta - eta ^ (2 : ℕ)) :=
    Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt (2 * eta - eta ^ (2 : ℕ)) ^ (2 : ℕ) =
      2 * eta - eta ^ (2 : ℕ) := Real.sq_sqrt hrad
  have hradlt : 2 * eta - eta ^ (2 : ℕ) < 1 := by
    nlinarith [sq_nonneg eta]
  simp only [binaryTraceSupportTail, binaryTraceDistanceRadius]
  nlinarith

/-- If the discarded tail is smaller than the light binary weight, neither
singleton carries the target mass. -/
theorem binaryNeedsBothCoordinates_of_tail_lt_light
    {delta c : ℝ} (hdeltac : delta < c) (hc : c ≤ 1 / 2) :
    BinaryNeedsBothCoordinates c delta := by
  constructor <;> linarith

theorem balancedBinaryNeedsBothCoordinates
    {delta : ℝ} (hdelta : delta < 1 / 2) :
    BinaryNeedsBothCoordinates (1 / 2) delta := by
  constructor <;> linarith

/-- **Operational hard-support/water-entropy separation.**  At the common
half-trace-distance tail scale, the scaled and balanced binary packets both
need two coordinates.  Their exact projective water entropies at amplitude
defect `eta` are nevertheless strictly ordered. -/
theorem operationalBinary_supportAndWaterEntropySeparation
    {q eta : ℝ} (heta0 : 0 < eta) (heta2fifths : eta < 2 / 5)
    (hq : 1 < q)
    (hqdelta : q * binaryTraceSupportTail eta < 1 / 2) :
    BinaryNeedsBothCoordinates
        (q * binaryTraceSupportTail eta) (binaryTraceSupportTail eta) ∧
      BinaryNeedsBothCoordinates (1 / 2) (binaryTraceSupportTail eta) ∧
      projectiveGaussianRateDistortionMinimum (by norm_num)
          (binaryProjectiveWeights (q * binaryTraceSupportTail eta)) eta =
        (1 / 2 : ℝ) * Real.log
          (q * binaryTraceSupportTail eta / eta) ∧
      projectiveGaussianRateDistortionMinimum (by norm_num)
          (binaryProjectiveWeights (1 / 2)) eta =
        (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) / eta) ∧
      (1 / 2 : ℝ) * Real.log
          (q * binaryTraceSupportTail eta / eta) <
        (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) / eta) := by
  have hetadelta := eta_lt_binaryTraceSupportTail heta0 heta2fifths
  have hdelta0 : 0 < binaryTraceSupportTail eta := heta0.trans hetadelta
  have hdeltac : binaryTraceSupportTail eta <
      q * binaryTraceSupportTail eta := by
    nlinarith [mul_pos (sub_pos.mpr hq) hdelta0]
  have hetac : eta < q * binaryTraceSupportTail eta :=
    hetadelta.trans hdeltac
  have hc : q * binaryTraceSupportTail eta ≤ 1 / 2 := hqdelta.le
  have hdeltaHalf : binaryTraceSupportTail eta < 1 / 2 :=
    binaryTraceSupportTail_lt_half heta0 heta2fifths
  have hetaHalf : eta < 1 / 2 := by linarith
  refine ⟨binaryNeedsBothCoordinates_of_tail_lt_light hdeltac hc,
    balancedBinaryNeedsBothCoordinates hdeltaHalf,
    binary_projectiveGaussianRateDistortionMinimum heta0 hetac hc,
    binary_projectiveGaussianRateDistortionMinimum heta0 hetaHalf (by norm_num),
    ?_⟩
  have hratio : q * binaryTraceSupportTail eta / eta <
      (1 / 2 : ℝ) / eta :=
    (div_lt_div_iff_of_pos_right heta0).2 hqdelta
  have hleft : 0 < q * binaryTraceSupportTail eta / eta :=
    div_pos (heta0.trans hetac) heta0
  have hright : 0 < (1 / 2 : ℝ) / eta := div_pos (by norm_num) heta0
  have hlog := Real.strictMonoOn_log hleft hright hratio
  nlinarith

/-- The scaled binary packet's least worst-spectrum Floquet deadline obeys
the exact dimension-two water-entropy band at the operational support scale. -/
theorem operationalBinary_floquetTime_waterEntropySandwich
    {q eta : ℝ} (heta0 : 0 < eta) (heta2fifths : eta < 2 / 5)
    (hq : 1 < q)
    (hqdelta : q * binaryTraceSupportTail eta < 1 / 2) :
    (1 / 2 : ℝ) * Real.log
          (q * binaryTraceSupportTail eta / eta) -
        Real.pi / 4 - Real.log 4 <
      Real.log (universalWeightedFloquetFidelityRecurrenceTime
        (by norm_num)
        (binaryProjectiveWeights (q * binaryTraceSupportTail eta))
        (binaryProjectiveWeights_nonneg
          (by
            have hetadelta := eta_lt_binaryTraceSupportTail heta0 heta2fifths
            have hdelta0 : 0 < binaryTraceSupportTail eta := heta0.trans hetadelta
            exact (mul_pos (by linarith) hdelta0).le)
          (by linarith))
        (sum_binaryProjectiveWeights (q * binaryTraceSupportTail eta))
        eta heta0 (by linarith) : ℝ) ∧
    Real.log (universalWeightedFloquetFidelityRecurrenceTime
        (by norm_num)
        (binaryProjectiveWeights (q * binaryTraceSupportTail eta))
        (binaryProjectiveWeights_nonneg
          (by
            have hetadelta := eta_lt_binaryTraceSupportTail heta0 heta2fifths
            have hdelta0 : 0 < binaryTraceSupportTail eta := heta0.trans hetadelta
            exact (mul_pos (by linarith) hdelta0).le)
          (by linarith))
        (sum_binaryProjectiveWeights (q * binaryTraceSupportTail eta))
        eta heta0 (by linarith) : ℝ) ≤
      (1 / 2 : ℝ) * Real.log
          (q * binaryTraceSupportTail eta / eta) +
        Real.log projectivePhaseResolutionConstant := by
  have hetadelta := eta_lt_binaryTraceSupportTail heta0 heta2fifths
  have hdelta0 : 0 < binaryTraceSupportTail eta := heta0.trans hetadelta
  have hdeltac : binaryTraceSupportTail eta <
      q * binaryTraceSupportTail eta := by
    nlinarith [mul_pos (sub_pos.mpr hq) hdelta0]
  have hetac : eta < q * binaryTraceSupportTail eta :=
    hetadelta.trans hdeltac
  have hc0 : 0 < q * binaryTraceSupportTail eta := heta0.trans hetac
  have hc1 : q * binaryTraceSupportTail eta < 1 := hqdelta.trans (by norm_num)
  have hw := binaryProjectiveWeights_pos hc0 hc1
  have heta1 : eta ≤ 1 := by linarith
  have h := universalWeightedFloquetFidelityRecurrenceTime_rateDistortionSandwich
    (by norm_num) (binaryProjectiveWeights (q * binaryTraceSupportTail eta))
    hw (sum_binaryProjectiveWeights _) eta heta0 heta1
  rw [binary_projectiveGaussianRateDistortionMinimum
    heta0 hetac hqdelta.le] at h
  norm_num at h ⊢
  simpa [projectivePhaseResolutionConstant] using h

end RHTower
