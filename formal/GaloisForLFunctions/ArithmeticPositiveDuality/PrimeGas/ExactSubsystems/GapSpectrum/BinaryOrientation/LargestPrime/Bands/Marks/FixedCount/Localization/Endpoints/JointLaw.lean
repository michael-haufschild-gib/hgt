import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints.Concentration
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! # Weak convergence of the full fixed-count spectrum to an endpoint vector -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints

open Filter Topology Set MeasureTheory

private theorem to_endpoint {k : ℕ} (z : Fin k → ℝ) (μ : Ioi (0:ℝ) → ProbabilityMeasure (Fin k → ℝ))
    (hμ : ∀ F : Set (Fin k → ℝ), IsClosed F → z ∉ F → Tendsto (fun h => (μ h F : ℝ)) criticalApproach (𝓝 0)) :
    Tendsto μ criticalApproach (𝓝 (diracProba z)) := by
  letI : NeBot criticalApproach := criticalApproach_neBot
  apply tendsto_of_forall_isClosed_limsup_real_le'
  intro F hF
  by_cases hz : z ∈ F
  · rw [Measure.real,diracProba_toMeasure_apply' z hF.measurableSet,indicator_of_mem hz,Pi.one_apply,ENNReal.toReal_one]
    exact limsup_le_of_le (isCoboundedUnder_le_of_le _ fun _ => measureReal_nonneg) (Eventually.of_forall fun _ => measureReal_le_one)
  · simp only [ProbabilityMeasure.measureReal_eq_coe_coeFn]
    rw [(hμ F hF hz).limsup_eq]
    exact (diracProba z F).property

/-- Positive diverging thermal drift collapses all k ordered locations to the lower endpoint. -/
theorem positive_drift {c d : ℝ} (hc : 0 < c) (hcd : c < d) {a : Ioi (0:ℝ) → ℝ}
    (ha : Tendsto a criticalApproach atTop) {k : ℕ} (hk : 0 < k) :
    Tendsto (fun h => conditional c d (a h) h k) criticalApproach (𝓝 (diracProba (fun _ : Fin k => c))) :=
  to_endpoint _ _ fun _ hF hz => lower_tail hc hcd ha hk hF hz

/-- Negative diverging thermal drift collapses all k ordered locations to the upper endpoint. -/
theorem negative_drift {c d : ℝ} (hc : 0 < c) (hcd : c < d) {a : Ioi (0:ℝ) → ℝ}
    (ha : Tendsto a criticalApproach atBot) {k : ℕ} (hk : 0 < k) :
    Tendsto (fun h => conditional c d (a h) h k) criticalApproach (𝓝 (diracProba (fun _ : Fin k => d))) := by
  apply to_endpoint
  intro F hF hz
  have H := upper_tail hc hcd (tendsto_neg_atBot_atTop.comp ha) hk hF hz
  change Tendsto (fun h => (thermalLaw c d h (1+ a h*h.val) k F : ℝ)) _ _
  simpa only [Function.comp_def,neg_mul,sub_neg_eq_add] using H

private theorem reciprocal : Tendsto (fun h : Ioi (0:ℝ) => h.val⁻¹) criticalApproach atTop :=
  tendsto_inv_nhdsGT_zero.comp (show Tendsto (Subtype.val : Ioi (0:ℝ) → ℝ) criticalApproach (𝓝[>] 0) from tendsto_comap)

/-- At fixed inverse temperature above one, the whole spectrum concentrates at c. -/
theorem above {c d s : ℝ} (hc : 0 < c) (hcd : c < d) (hs : 1 < s) {k : ℕ} (hk : 0 < k) :
    Tendsto (fun h => thermalLaw c d h s k) criticalApproach (𝓝 (diracProba (fun _ : Fin k => c))) := by
  apply (positive_drift hc hcd (reciprocal.const_mul_atTop (sub_pos.mpr hs)) hk).congr
  intro h
  change thermalLaw c d h (1+(s-1)*h.val⁻¹*h.val) k = _
  rw [show 1+(s-1)*h.val⁻¹*h.val = s by rw [mul_assoc,inv_mul_cancel₀ (show 0 < h.val from h.property).ne',mul_one]; ring]

/-- At fixed inverse temperature below one, the whole spectrum concentrates at d. -/
theorem below {c d s : ℝ} (hc : 0 < c) (hcd : c < d) (hs : s < 1) {k : ℕ} (hk : 0 < k) :
    Tendsto (fun h => thermalLaw c d h s k) criticalApproach (𝓝 (diracProba (fun _ : Fin k => d))) := by
  have H := tendsto_neg_atTop_atBot.comp (reciprocal.const_mul_atTop (sub_pos.mpr hs))
  apply (negative_drift hc hcd H hk).congr
  intro h
  change thermalLaw c d h (1+-((1-s)*h.val⁻¹)*h.val) k = _
  rw [neg_mul, mul_assoc,inv_mul_cancel₀ (show 0 < h.val from h.property).ne',mul_one]
  congr 1
  ring

theorem at_one {c d : ℝ} (hc : 0 < c) (hcd : c < d) (k : ℕ) :
    Tendsto (fun h => thermalLaw c d h 1 k) criticalApproach (𝓝 (orderStatistics k (draw hc hcd.le 0))) := by
  simpa only [conditional,thermalLaw,zero_mul,add_zero] using conditional_limit hc hcd 0 k

#print axioms positive_drift
#print axioms negative_drift
#print axioms above
#print axioms below
#print axioms at_one

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints
