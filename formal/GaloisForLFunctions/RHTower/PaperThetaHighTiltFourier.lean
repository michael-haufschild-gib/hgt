import GaloisForLFunctions.RHTower.PaperThetaLogPowerSelector
import GaloisForLFunctions.RHTower.PaperThetaSourceFourier

/-! # Genuine non-L² theta inputs to the proven Fourier endpoint theorem

The literal modes with imaginary parameter greater than two pay L log L while
failing L². The paper's full symmetric Fourier theorem therefore reconstructs
an entire new family outside the previous square-integrable divisor domain.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace RHTower.PaperThetaEndpoint

open HedenmalmThetaSource GaloisForLFunctions.HTGeometry FourierLLogL

theorem measurable_circleMode_all (z : ℂ) : Measurable (circleMode z) :=
  (measurable_pullback_all z).comp Period.measurable_coord

theorem memLp_circleMode_iff_all (z : ℂ) :
    MemLp (circleMode z) 2 circleMeasure ↔ z = 0 ∨ XiC z = 0 := by
  rw [← measurePreserving_circle.map_eq,
    memLp_map_measure_iff (measurable_circleMode_all z).aestronglyMeasurable
      Period.measurable_circle.aemeasurable]
  change MemLp (fun t => circleMode z (Period.circle t)) 2 unitIntervalMeasure ↔ _
  exact (memLp_congr_ae (circleMode_circle_ae z)).trans (memLp_pullback_iff_all z)

theorem integrable_circle_logPower_iff (z : ℂ) (a : ℝ≥0) :
    Integrable (fun x => ‖circleMode z x‖ * Real.log (2 + ‖circleMode z x‖) ^ (a : ℝ))
      circleMeasure ↔ z = 0 ∨ XiC z = 0 ∨ 2 * (a : ℝ) < z.im := by
  have hn := (measurable_circleMode_all z).norm
  have hm : Measurable (fun x => ‖circleMode z x‖ * Real.log (2 + ‖circleMode z x‖) ^ (a : ℝ)) :=
    hn.mul ((measurable_const.add hn).log.pow_const (a : ℝ))
  rw [← measurePreserving_circle.map_eq,
    integrable_map_measure hm.aestronglyMeasurable Period.measurable_circle.aemeasurable,
    ← integrable_pullbackLogPower_iff z a]
  apply integrable_congr
  filter_upwards [circleMode_circle_ae z] with t ht
  simp only [Function.comp_apply, ht, pullbackLogPower]

/-- Exact admission to the proven endpoint theorem over the whole complex plane. -/
theorem memLLogL_circleMode_iff_all (z : ℂ) :
    MemLLogL (circleMode z) ↔ z = 0 ∨ XiC z = 0 ∨ 2 < z.im := by
  rw [MemLLogL, and_iff_right (measurable_circleMode_all z).aestronglyMeasurable]
  simpa only [NNReal.coe_one, Real.rpow_one, mul_one]
    using integrable_circle_logPower_iff z 1

abbrev HighTiltPoint := {z : ℂ // 2 < z.im}

theorem memLLogL_highTilt (z : HighTiltPoint) : MemLLogL (circleMode z.val) :=
  (memLLogL_circleMode_iff_all z.val).mpr (Or.inr (Or.inr z.property))

/-- Every high-tilt input lies strictly outside L², with no nonvanishing premise. -/
theorem not_memLp_highTilt (z : HighTiltPoint) : ¬ MemLp (circleMode z.val) 2 circleMeasure := by
  rw [memLp_circleMode_iff_all]
  rintro (h0 | hXi)
  · have hz := z.property
    rw [h0, Complex.zero_im] at hz
    linarith
  · have hs := abs_im_lt_one_of_XiC_eq_zero hXi
    have hz := z.property
    linarith [le_abs_self z.val.im]

/-- Actual endpoint admission and actual failure of the Hilbert-space domain. -/
theorem highTilt_strict_endpoint (z : HighTiltPoint) :
    MemLLogL (circleMode z.val) ∧ ¬ MemLp (circleMode z.val) 2 circleMeasure :=
  ⟨memLLogL_highTilt z, not_memLp_highTilt z⟩

/-- Full symmetric Fourier recovery of the non-L² modes, with a measurable null set. -/
theorem circle_recovery_highTilt (z : HighTiltPoint) :
    ∃ E : Set Torus, MeasurableSet E ∧ circleMeasure E = 0 ∧ ∀ x ∉ E,
      Tendsto (fun N : ℕ => symmetricPartialSum (circleMode z.val) N x)
        atTop (𝓝 (circleMode z.val x)) :=
  almost_everywhere_fourier_convergence _ (memLLogL_highTilt z)

theorem quantile_recovery_highTilt (z : HighTiltPoint) :
    ∀ᵐ t ∂unitIntervalMeasure,
      Tendsto (fun N : ℕ => symmetricPartialSum (circleMode z.val) N (Period.circle t))
        atTop (𝓝 (flatModePullback z.val t)) := by
  obtain ⟨E, _, hE, hconv⟩ := circle_recovery_highTilt z
  have ha : ∀ᵐ x ∂circleMeasure,
      Tendsto (fun N : ℕ => symmetricPartialSum (circleMode z.val) N x)
        atTop (𝓝 (circleMode z.val x)) := by
    filter_upwards [show ∀ᵐ x ∂circleMeasure, x ∉ E from by
      rw [ae_iff]
      simpa only [not_not, setOf_mem_eq] using hE] with x hx
    exact hconv x hx
  filter_upwards [measurePreserving_circle.quasiMeasurePreserving.ae ha,
    circleMode_circle_ae z.val] with t ht he
  simpa only [he] using ht

/-- The paper's full entropy-sensitive height-layer cost is paid by these non-L² modes. -/
theorem summable_height_cost_highTilt (z : HighTiltPoint) :
    Summable (fun j => heightLayerMass (circleMode z.val) j *
      ((2 : ℝ) ^ (j + 2) + max 0 (-Real.log (heightLayerMass (circleMode z.val) j)))) :=
  (memLLogL_highTilt z).summable_heightLayerCost

end RHTower.PaperThetaEndpoint
