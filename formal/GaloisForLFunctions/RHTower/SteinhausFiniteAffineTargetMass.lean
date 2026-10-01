import GaloisForLFunctions.RHTower.SteinhausFiniteAffineVariance
import Mathlib.MeasureTheory.Measure.Real


open MeasureTheory
open scoped ENNReal

noncomputable section
namespace RHTower
open SteinhausModel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Small total column energy places at least half the biased law inside the actual centered target ball. -/
theorem measure_steinhausFiniteCenteredSum_ball_ge_half {n : ℕ} {m : Fin n → ℂ}
    (hm : ∀ i, ‖m i‖ ≤ 1 / 2) (a : Fin n → E) {r : ℝ} (hr : 0 < r)
    (henergy : (∑ i, ‖a i‖ ^ 2) ≤ r ^ 2 / 2) :
    ENNReal.ofReal (1 / 2 : ℝ) ≤
      steinhausFiniteAffineMeasure m {x | ‖steinhausFiniteCenteredSum m a x‖ < r} := by
  letI := isProbabilityMeasure_steinhausFiniteAffineMeasure hm
  have hE : MeasurableSet {x | ‖steinhausFiniteCenteredSum m a x‖ < r} :=
    measurableSet_lt (continuous_steinhausFiniteCenteredSum m a).norm.measurable measurable_const
  have hcomp : {x | ‖steinhausFiniteCenteredSum m a x‖ < r}ᶜ =
      {x | r ^ 2 ≤ ‖steinhausFiniteCenteredSum m a x‖ ^ 2} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    have hn := norm_nonneg (steinhausFiniteCenteredSum m a x)
    exact (sq_le_sq₀ hr.le hn).symm
  have hmkv := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun x => sq_nonneg (‖steinhausFiniteCenteredSum m a x‖))
    (integrable_norm_sq_steinhausFiniteCenteredSum hm a) (r ^ 2)
  have hupper := hmkv.trans ((integral_norm_sq_steinhausFiniteCenteredSum_le hm a).trans henergy)
  have hsum := measureReal_add_measureReal_compl
    (μ := steinhausFiniteAffineMeasure m) hE
  rw [hcomp, probReal_univ] at hsum
  have hreal : (1 / 2 : ℝ) ≤ (steinhausFiniteAffineMeasure m).real
      {x | ‖steinhausFiniteCenteredSum m a x‖ < r} := by
    have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
    have hbad : (steinhausFiniteAffineMeasure m).real
        {x | r ^ 2 ≤ ‖steinhausFiniteCenteredSum m a x‖ ^ 2} ≤ 1 / 2 := by
      apply (mul_le_mul_iff_right₀ hr2).mp
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using hupper
    linarith
  have h := ENNReal.ofReal_le_ofReal hreal
  simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h

end RHTower
