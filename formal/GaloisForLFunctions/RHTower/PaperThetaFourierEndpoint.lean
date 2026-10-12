import GaloisForLFunctions.RHTower.PaperThetaEndpointSelector
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.PaperMain
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Fourier.Coordinates
import GaloisForLFunctions.HTGeometry.PaperFourierLLogLAdmission

/-! # Fourier endpoint recovery in the original theta quantile coordinate

The literal pullback is L¹ throughout the upper strip and lies in L log L exactly
at the Xi divisor. The proven Fourier endpoint theorem recovers every admitted
mode by the full sequence of symmetric partial sums, without changing the source weight.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry FourierLLogL HedenmalmThetaSource HedenmalmQuantile

namespace PaperThetaEndpoint

theorem unitIntervalMeasure_eq_periodMeasure : unitIntervalMeasure = Period.μ₁ :=
  (Measure.restrict_congr_set Ico_ae_eq_Icc).symm

theorem measurePreserving_circle :
    MeasurePreserving Period.circle unitIntervalMeasure circleMeasure := by
  rw [unitIntervalMeasure_eq_periodMeasure]
  exact ⟨Period.measurable_circle, Period.map_circle_volume⟩

/-- No amplitude normalization: only the standard period-one circle coordinate. -/
def circleMode (z : ℂ) (x : Torus) : ℂ := flatModePullback z (Period.coord x)

theorem measurable_circleMode_of_strip {z : ℂ} (hz : |z.im| < 1) :
    Measurable (circleMode z) :=
  (((continuous_flatMode hz).measurable.comp thetaSource.measurable_quantileFun).div
    (measurable_metricSymbol thetaSource)).comp Period.measurable_coord

theorem measurable_circleMode (z : Point) : Measurable (circleMode z) :=
  (measurable_pullback z).comp Period.measurable_coord

theorem circleMode_circle_ae (z : ℂ) :
    (fun t => circleMode z (Period.circle t)) =ᵐ[unitIntervalMeasure] flatModePullback z := by
  rw [unitIntervalMeasure_eq_periodMeasure]
  filter_upwards [ae_restrict_mem Period.measurable_unitInt] with t ht
  exact congrArg (flatModePullback z) (Period.coord_circle_eq ht)

/-- Every parameter in the strip supplies genuine Fourier coefficients. -/
theorem integrable_circleMode (z : Point) : Integrable (circleMode z) circleMeasure := by
  rw [← measurePreserving_circle.map_eq,
    integrable_map_measure (measurable_circleMode z).aestronglyMeasurable
      Period.measurable_circle.aemeasurable]
  exact (integrable_pullback z).congr (circleMode_circle_ae z).symm

/-- Exact admission for the proven L log L Fourier theorem. -/
theorem memLLogL_circleMode_iff (z : Point) : MemLLogL (circleMode z) ↔ XiC z = 0 := by
  have hn := (measurable_circleMode z).norm
  have hm : Measurable (fun x => ‖circleMode z.val x‖ * Real.log (2 + ‖circleMode z.val x‖)) :=
    hn.mul ((measurable_const.add hn).log)
  rw [MemLLogL, and_iff_right (measurable_circleMode z).aestronglyMeasurable,
    ← measurePreserving_circle.map_eq, integrable_map_measure hm.aestronglyMeasurable
      Period.measurable_circle.aemeasurable, ← integrable_pullback_log_iff z]
  apply integrable_congr
  filter_upwards [circleMode_circle_ae z] with t ht
  simp only [Function.comp_apply, ht]

/-- All Xi zeros, including those on the critical line, with their full complex position. -/
abbrev DivisorPoint := {z : ℂ // XiC z = 0}

theorem memLp_divisorMode (z : DivisorPoint) : MemLp (circleMode z.val) 2 circleMeasure := by
  have hm := measurable_circleMode_of_strip (abs_im_lt_one_of_XiC_eq_zero z.property)
  rw [← measurePreserving_circle.map_eq,
    memLp_map_measure_iff hm.aestronglyMeasurable Period.measurable_circle.aemeasurable]
  have hp : MemLp (flatModePullback z.val) 2 unitIntervalMeasure :=
    (memLp_congr_ae (portEigenmode_ae_flatModePullback z.property)).1
      (Lp.memLp (portEigenmode z.val))
  exact (memLp_congr_ae (circleMode_circle_ae z.val).symm).1 hp

theorem memLLogL_divisorMode (z : DivisorPoint) : MemLLogL (circleMode z.val) :=
  (paperMemLLogL_Lp ((memLp_divisorMode z).toLp _)).congr_ae
    (memLp_divisorMode z).coeFn_toLp

/-- Full symmetric Fourier recovery on the circle, with an explicit null exceptional set. -/
theorem circle_recovery (z : DivisorPoint) :
    ∃ E : Set Torus, MeasurableSet E ∧ circleMeasure E = 0 ∧ ∀ x ∉ E,
      Tendsto (fun N : ℕ => symmetricPartialSum (circleMode z.val) N x)
        atTop (𝓝 (circleMode z.val x)) :=
  almost_everywhere_fourier_convergence _ (memLLogL_divisorMode z)

/-- The endpoint theorem recovers the literal mode in the original quantile coordinate. -/
theorem quantile_recovery (z : DivisorPoint) :
    ∀ᵐ t ∂unitIntervalMeasure,
      Tendsto (fun N : ℕ => symmetricPartialSum (circleMode z.val) N (Period.circle t))
        atTop (𝓝 (flatModePullback z.val t)) := by
  obtain ⟨E, _, hE, hconv⟩ := circle_recovery z
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

/-- The paper's entropy-sensitive height-layer cost is paid by the actual divisor mode. -/
theorem summable_height_cost (z : DivisorPoint) :
    Summable (fun j => heightLayerMass (circleMode z.val) j *
      ((2 : ℝ) ^ (j + 2) + max 0 (-Real.log (heightLayerMass (circleMode z.val) j)))) :=
  (memLLogL_divisorMode z).summable_heightLayerCost

end PaperThetaEndpoint
end RHTower
