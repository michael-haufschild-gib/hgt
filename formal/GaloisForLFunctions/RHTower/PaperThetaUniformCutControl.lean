import GaloisForLFunctions.RHTower.PaperThetaConfluentCut
import Mathlib.Analysis.Complex.AbsMax

/-! # One BV control for a whole complex disk of literal cut modes

The two native tails share the endpoint trace `-1`. Joining their variation
budgets with enough monotone jump controls increments across the actual cut,
as well as within either tail. The same bounded monotone function works for
every parameter in a disk. This is the arithmetic graph admission ingredient,
not a bound on a truncated prime form.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex Metric

namespace RHTower.PaperThetaEndpoint

def cutControlSize (z : ℂ) (a : ℝ) : ℝ :=
  parameterVariationBudget (-z) (-a) + parameterVariationBudget z a

def cutVariationControl (z : ℂ) (a x : ℝ) : ℝ :=
  if x < a then parameterVariationBudget (-z) (-x)
  else 2 * cutControlSize z a - parameterVariationBudget z x

theorem cutControlSize_nonneg (z : ℂ) (a : ℝ) : 0 ≤ cutControlSize z a :=
  add_nonneg (parameterVariationBudget_nonneg _ _) (parameterVariationBudget_nonneg _ _)

theorem cutVariationControl_bounds (z : ℂ) (a x : ℝ) :
    0 ≤ cutVariationControl z a x ∧ cutVariationControl z a x ≤ 2 * cutControlSize z a := by
  have hl := parameterVariationBudget_nonneg (-z) (-a)
  have hr := parameterVariationBudget_nonneg z a
  have hx := parameterVariationBudget_nonneg z x
  have hn := parameterVariationBudget_nonneg (-z) (-x)
  unfold cutVariationControl cutControlSize
  split_ifs with h
  · have hm := parameterVariationBudget_antitone (-z) (neg_le_neg h.le)
    constructor <;> linarith
  · have hm := parameterVariationBudget_antitone z (le_of_not_gt h)
    constructor <;> linarith

theorem monotone_cutVariationControl (z : ℂ) (a : ℝ) :
    Monotone (cutVariationControl z a) := by
  intro x y hxy
  by_cases hy : y < a
  · have hx := lt_of_le_of_lt hxy hy
    simp only [cutVariationControl, if_pos hx, if_pos hy]
    exact parameterVariationBudget_antitone (-z) (neg_le_neg hxy)
  by_cases hx : x < a
  · have hl := parameterVariationBudget_antitone (-z) (neg_le_neg hx.le)
    have hr := parameterVariationBudget_antitone z (le_of_not_gt hy)
    have hn := cutControlSize_nonneg z a
    simp only [cutVariationControl, if_pos hx, if_neg hy]
    dsimp [cutControlSize] at *
    linarith
  · simp only [cutVariationControl, if_neg hx, if_neg hy]
    exact sub_le_sub_left (parameterVariationBudget_antitone z hxy) _

theorem boundedVariationOn_cutVariationControl (z : ℂ) (a : ℝ) :
    BoundedVariationOn (cutVariationControl z a) univ := by
  apply ((monotone_cutVariationControl z a).monotoneOn univ).boundedVariationOn
  intro x _
  rw [abs_of_nonneg (cutVariationControl_bounds z a x).1]
  exact (cutVariationControl_bounds z a x).2

theorem differentiable_cutQuotient_parameter (a x : ℝ) :
    Differentiable ℂ (fun z => cutQuotient z a x) := by
  by_cases hx : x < a
  · simp only [cutQuotient, if_pos hx, leftQuotient]
    exact (differentiable_flatQuotient_parameter (-x)).comp differentiable_neg
  · simpa only [cutQuotient, if_neg hx] using differentiable_flatQuotient_parameter x

theorem measurable_cutQuotient (z : ℂ) (a : ℝ) : Measurable (cutQuotient z a) :=
  Measurable.ite measurableSet_Iio (continuous_leftQuotient z).measurable
    (continuous_flatQuotient z).measurable

private theorem neg_mem_parameter_sphere {z w : ℂ} (hw : w ∈ sphere z 1) :
    -w ∈ sphere (-z) 1 := by
  simpa only [mem_sphere, dist_neg_neg] using hw

theorem cutQuotient_add_one_circle (z : ℂ) (a x : ℝ)
    {w : ℂ} (hw : w ∈ sphere z 1) :
    ‖cutQuotient w a x + 1‖ ≤ cutControlSize z a := by
  have hl := parameterVariationBudget_nonneg (-z) (-a)
  have hr := parameterVariationBudget_nonneg z a
  by_cases hx : x < a
  · have hb := flatQuotient_add_one_parameter_circle (-z) (-x) (neg_mem_parameter_sphere hw)
    have hm := parameterVariationBudget_antitone (-z) (neg_le_neg hx.le)
    simpa only [cutQuotient, if_pos hx, leftQuotient] using
      hb.trans (by dsimp [cutControlSize]; linarith)
  · have hb := flatQuotient_add_one_parameter_circle z x hw
    have hm := parameterVariationBudget_antitone z (le_of_not_gt hx)
    simpa only [cutQuotient, if_neg hx] using
      hb.trans (by dsimp [cutControlSize]; linarith)

theorem cutQuotient_increment_circle (z : ℂ) (a : ℝ) {x y : ℝ} (hxy : x ≤ y)
    {w : ℂ} (hw : w ∈ sphere z 1) :
    ‖cutQuotient w a y - cutQuotient w a x‖ ≤
      cutVariationControl z a y - cutVariationControl z a x := by
  by_cases hy : y < a
  · have hx := lt_of_le_of_lt hxy hy
    have h := flatQuotient_increment_parameter_circle (-z) (neg_le_neg hxy)
      (neg_mem_parameter_sphere hw)
    simpa only [cutQuotient, cutVariationControl, if_pos hx, if_pos hy,
      leftQuotient, norm_sub_rev] using h
  by_cases hx : x < a
  · have hl := flatQuotient_add_one_parameter_circle (-z) (-x) (neg_mem_parameter_sphere hw)
    have hr := flatQuotient_add_one_parameter_circle z y hw
    have hla := parameterVariationBudget_antitone (-z) (neg_le_neg hx.le)
    have hra := parameterVariationBudget_antitone z (le_of_not_gt hy)
    simp only [cutQuotient, cutVariationControl, if_pos hx, if_neg hy, leftQuotient]
    have ht := norm_sub_le (flatQuotient w y + 1) (flatQuotient (-w) (-x) + 1)
    rw [add_sub_add_right_eq_sub] at ht
    dsimp [cutControlSize]
    linarith
  · have h := flatQuotient_increment_parameter_circle z hxy hw
    simp only [cutQuotient, cutVariationControl, if_neg hx, if_neg hy]
    linarith

private theorem norm_le_in_parameter_ball (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (z : ℂ) (B : ℝ) (hB : ∀ w ∈ sphere z 1, ‖f w‖ ≤ B)
    {w : ℂ} (hw : w ∈ ball z 1) : ‖f w‖ ≤ B := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hf.diffContOnCl
    (fun v hv => hB v ?_) (subset_closure hw)
  simpa only [frontier_ball z (by norm_num : (1 : ℝ) ≠ 0)] using hv

theorem cutQuotient_norm_ball (z : ℂ) (a x : ℝ)
    {w : ℂ} (hw : w ∈ ball z 1) :
    ‖cutQuotient w a x‖ ≤ cutControlSize z a + 1 := by
  apply norm_le_in_parameter_ball _ (differentiable_cutQuotient_parameter a x) z _ _ hw
  intro v hv
  have h := cutQuotient_add_one_circle z a x hv
  have ht := norm_sub_le (cutQuotient v a x + 1) (1 : ℂ)
  simp only [add_sub_cancel_right, norm_one] at ht
  linarith

/-- A single actual BV difference dominates every edge throughout a complex disk. -/
theorem cutQuotient_difference_ball (z : ℂ) (a x y : ℝ)
    {w : ℂ} (hw : w ∈ ball z 1) :
    ‖cutQuotient w a x - cutQuotient w a y‖ ≤
      |cutVariationControl z a x - cutVariationControl z a y| := by
  have h (x y : ℝ) (hxy : x ≤ y) :
      ‖cutQuotient w a y - cutQuotient w a x‖ ≤
        cutVariationControl z a y - cutVariationControl z a x :=
    norm_le_in_parameter_ball _
      ((differentiable_cutQuotient_parameter a y).sub
        (differentiable_cutQuotient_parameter a x)) z _
      (fun v hv => cutQuotient_increment_circle z a hxy hv) hw
  rcases le_total y x with hyx | hxy
  · rw [abs_of_nonneg (sub_nonneg.mpr (monotone_cutVariationControl z a hyx))]
    exact h y x hyx
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (monotone_cutVariationControl z a hxy)),
      norm_sub_rev]
    exact h x y hxy

end RHTower.PaperThetaEndpoint
