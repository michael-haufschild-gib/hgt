import GaloisForLFunctions.RHTower.SteinhausFiniteAffineTargetMass
import GaloisForLFunctions.RHTower.SteinhausFiniteTargetBiases


open MeasureTheory
open scoped ENNReal

noncomputable section
namespace RHTower
open SteinhausModel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- An original-law local target lower bound from an actual coercive frame with small columns and small total variance. -/
theorem measureReal_steinhausFiniteLocalTarget_ge {n : ℕ} (a : Fin n → E)
    {c r : ℝ} (hc : 0 < c) (hr : 0 < r)
    (hframe : ∀ w : E, c * ‖w‖ ^ 2 ≤ ∑ i, ‖inner ℂ (a i) w‖ ^ 2)
    (v : E) (hsmall : ∀ i, ‖a i‖ * ‖v‖ / c ≤ 1 / 2)
    (henergy : (∑ i, ‖a i‖ ^ 2) ≤ r ^ 2 / 2) :
    (1 / 4 : ℝ) * Real.exp (-2 * ‖v‖ ^ 2 / c) ≤
      (steinhausFinitePhaseMeasure n).real {x | ‖(∑ i, charFactor 1 (x i) • a i) - v‖ < r} := by
  obtain ⟨m, hsynth, hcost, hbias⟩ := exists_steinhausFiniteTargetBiases a hc hframe v
  have hm (i : Fin n) : ‖m i‖ ≤ 1 / 2 := (hbias i).trans (hsmall i)
  have heq (x : Fin n → ℝ) : steinhausFiniteCenteredSum m a x =
      (∑ i, charFactor 1 (x i) • a i) - v := by
    simp only [steinhausFiniteCenteredSum, steinhausFiniteCenteredPhase,
      sub_smul, Finset.sum_sub_distrib, hsynth]
  have hmass := measure_steinhausFiniteCenteredSum_ball_ge_half hm a hr henergy
  have hE : MeasurableSet {x | ‖steinhausFiniteCenteredSum m a x‖ < r} :=
    measurableSet_lt (continuous_steinhausFiniteCenteredSum m a).norm.measurable measurable_const
  have h := measureReal_event_ge_steinhausFiniteAffineCost hm hE hmass
  simp_rw [heq] at h
  apply le_trans _ h
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 4)
  apply Real.exp_le_exp.mpr
  have h2 := mul_le_mul_of_nonneg_left hcost (by norm_num : (0 : ℝ) ≤ 2)
  calc
    -2 * ‖v‖ ^ 2 / c = -(2 * (‖v‖ ^ 2 / c)) := by ring
    _ ≤ _ := neg_le_neg h2

end RHTower
