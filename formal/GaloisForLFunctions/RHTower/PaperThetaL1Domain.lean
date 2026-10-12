import GaloisForLFunctions.RHTower.PaperThetaBoundedDomain
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Fourier.Dirichlet

/-! # Exact L¹ admission and the literal periodic theta representative -/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace RHTower.PaperThetaEndpoint

open HedenmalmThetaSource GaloisForLFunctions.HTGeometry FourierLLogL

/-- The original quantile mode has an exact whole-plane L¹ domain. -/
theorem integrable_pullback_iff_all (z : ℂ) :
    Integrable (flatModePullback z) unitIntervalMeasure ↔ z = 0 ∨ XiC z = 0 ∨ 0 < z.im := by
  rw [← integrable_norm_iff (measurable_pullback_all z).aestronglyMeasurable]
  have he : pullbackLogPower z 0 = fun t => ‖flatModePullback z t‖ := by
    funext t
    simp only [pullbackLogPower, NNReal.coe_zero, Real.rpow_zero, mul_one]
  simpa only [he, NNReal.coe_zero, mul_zero]
    using integrable_pullbackLogPower_iff z 0

theorem integrable_circleMode_iff_all (z : ℂ) :
    Integrable (circleMode z) circleMeasure ↔ z = 0 ∨ XiC z = 0 ∨ 0 < z.im := by
  rw [← integrable_norm_iff (measurable_circleMode_all z).aestronglyMeasurable]
  simpa only [NNReal.coe_zero, Real.rpow_zero, mul_one, mul_zero]
    using integrable_circle_logPower_iff z 0

abbrev L1Point := {z : ℂ // z = 0 ∨ XiC z = 0 ∨ 0 < z.im}

theorem integrable_circleMode_L1 (z : L1Point) : Integrable (circleMode z.val) circleMeasure :=
  (integrable_circleMode_iff_all z.val).mpr z.property

/-- The existing circle representative lifted to the real period-one coordinate. -/
def periodicMode (z : ℂ) (t : ℝ) : ℂ := circleMode z (Period.circle t)

theorem measurable_periodicMode (z : ℂ) : Measurable (periodicMode z) :=
  (measurable_circleMode_all z).comp Period.measurable_circle

theorem periodic_periodicMode (z : ℂ) : Function.Periodic (periodicMode z) 1 := by
  intro t
  rw [periodicMode, Period.periodic_circle, periodicMode]

theorem periodicMode_eq_pullback (z : ℂ) (t : Ioo (0 : ℝ) 1) :
    periodicMode z t.val = flatModePullback z t.val := by
  unfold periodicMode circleMode
  rw [Period.coord_circle_eq ⟨t.property.1.le, t.property.2⟩]

theorem integrable_periodicMode_L1 (z : L1Point) : Integrable (periodicMode z.val) Period.μ₁ := by
  rw [← unitIntervalMeasure_eq_periodMeasure]
  exact measurePreserving_circle.integrable_comp_of_integrable (integrable_circleMode_L1 z)

theorem intervalIntegrable_periodicMode (z : L1Point) (a b : ℝ) :
    IntervalIntegrable (periodicMode z.val) volume a b := by
  have hi : IntegrableOn (periodicMode z.val) (Ico (0 : ℝ) 1) :=
    integrable_periodicMode_L1 z
  have hI : IntervalIntegrable (periodicMode z.val) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      ((integrableOn_congr_set_ae Ico_ae_eq_Ioc).mp hi)
  exact (periodic_periodicMode z.val).intervalIntegrable₀ one_ne_zero hI a b

/-- Reversing the centered period retains actual L¹ integrability at every observation. -/
theorem integrable_centered_periodicMode (z : L1Point) (t : ℝ) :
    IntegrableOn (fun y => periodicMode z.val (t - y)) Period.centerWin := by
  have h := (intervalIntegrable_periodicMode z (t + 1/2) (t - 1/2)).comp_sub_left t
  have hI : IntervalIntegrable (fun y => periodicMode z.val (t-y)) volume (-1/2) (1/2) := by
    convert h using 1 <;> ring
  exact (integrableOn_congr_set_ae Ico_ae_eq_Ioc).mpr
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp hI)

end RHTower.PaperThetaEndpoint
