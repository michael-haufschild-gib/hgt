import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Restriction to a measurable set as an operator on `Lᵖ`

Multiplying by the indicator of a measurable set is well defined on almost-everywhere classes,
is linear, and does not increase the `Lᵖ` seminorm.  It is therefore a bounded operator of norm
at most one on `Lᵖ`.

This is the completed form of coordinate restriction: on finitely supported divisor coordinates
restriction deletes coordinates, and on the completion it is this operator.

* `deningerLpIndicatorFun` is the underlying map, with `deningerLpIndicatorFun_coeFn` its
  defining almost-everywhere description.
* `deningerLpIndicator` is the bounded operator, with `deningerLpIndicator_norm_le`.
-/

namespace RHTower

open MeasureTheory

open scoped ENNReal NNReal

section LpIndicator

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {s : Set α}

/-- Multiplication by the indicator of a measurable set, on `Lᵖ`. -/
noncomputable def deningerLpIndicatorFun (hs : MeasurableSet s) (f : Lp ℝ p μ) : Lp ℝ p μ :=
  ((Lp.memLp f).indicator hs).toLp _

omit [Fact (1 ≤ p)] in
theorem deningerLpIndicatorFun_coeFn (hs : MeasurableSet s) (f : Lp ℝ p μ) :
    (deningerLpIndicatorFun hs f : α → ℝ) =ᵐ[μ] s.indicator (f : α → ℝ) :=
  MemLp.coeFn_toLp _

omit [Fact (1 ≤ p)] in
theorem deningerLpIndicatorFun_add (hs : MeasurableSet s) (f g : Lp ℝ p μ) :
    deningerLpIndicatorFun hs (f + g)
      = deningerLpIndicatorFun hs f + deningerLpIndicatorFun hs g := by
  refine Lp.ext ?_
  filter_upwards [deningerLpIndicatorFun_coeFn hs (f + g),
    deningerLpIndicatorFun_coeFn hs f, deningerLpIndicatorFun_coeFn hs g,
    Lp.coeFn_add f g,
    Lp.coeFn_add (deningerLpIndicatorFun hs f) (deningerLpIndicatorFun hs g)]
    with a h0 h1 h2 h3 h4
  rw [h0, h4]
  simp only [Pi.add_apply]
  rw [h1, h2]
  by_cases ha : a ∈ s
  · simp only [Set.indicator_of_mem ha]
    simpa using h3
  · simp [Set.indicator_of_notMem ha]

omit [Fact (1 ≤ p)] in
theorem deningerLpIndicatorFun_smul (hs : MeasurableSet s) (c : ℝ) (f : Lp ℝ p μ) :
    deningerLpIndicatorFun hs (c • f) = c • deningerLpIndicatorFun hs f := by
  refine Lp.ext ?_
  filter_upwards [deningerLpIndicatorFun_coeFn hs (c • f),
    deningerLpIndicatorFun_coeFn hs f, Lp.coeFn_smul c f,
    Lp.coeFn_smul c (deningerLpIndicatorFun hs f)] with a h0 h1 h2 h3
  rw [h0, h3]
  simp only [Pi.smul_apply]
  rw [h1]
  by_cases ha : a ∈ s
  · simp only [Set.indicator_of_mem ha, smul_eq_mul]
    simpa using h2
  · simp [Set.indicator_of_notMem ha]

omit [Fact (1 ≤ p)] in
theorem deningerLpIndicatorFun_norm_le (hs : MeasurableSet s) (f : Lp ℝ p μ) :
    ‖deningerLpIndicatorFun hs f‖ ≤ ‖f‖ := by
  rw [deningerLpIndicatorFun, Lp.norm_toLp, Lp.norm_def]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) ?_
  exact eLpNorm_indicator_le _

/-- **Restriction to a measurable set is a bounded operator on `Lᵖ` of norm at most one.** -/
noncomputable def deningerLpIndicator (hs : MeasurableSet s) : Lp ℝ p μ →L[ℝ] Lp ℝ p μ :=
  LinearMap.mkContinuous
    { toFun := deningerLpIndicatorFun hs
      map_add' := deningerLpIndicatorFun_add hs
      map_smul' := fun c f => deningerLpIndicatorFun_smul hs c f } 1 (by
      intro f
      rw [one_mul]
      exact deningerLpIndicatorFun_norm_le hs f)

@[simp] theorem deningerLpIndicator_apply (hs : MeasurableSet s) (f : Lp ℝ p μ) :
    deningerLpIndicator hs f = deningerLpIndicatorFun hs f := rfl

theorem deningerLpIndicator_norm_le (hs : MeasurableSet s) (f : Lp ℝ p μ) :
    ‖deningerLpIndicator hs f‖ ≤ ‖f‖ :=
  deningerLpIndicatorFun_norm_le hs f

omit [Fact (1 ≤ p)] in
/-- Restriction is idempotent. -/
theorem deningerLpIndicatorFun_idem (hs : MeasurableSet s) (f : Lp ℝ p μ) :
    deningerLpIndicatorFun hs (deningerLpIndicatorFun hs f) = deningerLpIndicatorFun hs f := by
  refine Lp.ext ?_
  filter_upwards [deningerLpIndicatorFun_coeFn hs (deningerLpIndicatorFun hs f),
    deningerLpIndicatorFun_coeFn hs f] with a h1 h2
  rw [h1]
  by_cases ha : a ∈ s
  · rw [Set.indicator_of_mem ha]
  · rw [Set.indicator_of_notMem ha, h2, Set.indicator_of_notMem ha]

omit [Fact (1 ≤ p)] in
/-- Restricting to a set and then to its complement is zero. -/
theorem deningerLpIndicatorFun_compl_comp (hs : MeasurableSet s) (f : Lp ℝ p μ) :
    deningerLpIndicatorFun hs.compl (deningerLpIndicatorFun hs f) = 0 := by
  refine Lp.ext ?_
  filter_upwards [deningerLpIndicatorFun_coeFn hs.compl (deningerLpIndicatorFun hs f),
    deningerLpIndicatorFun_coeFn hs f, Lp.coeFn_zero ℝ p μ] with a h1 h2 h3
  rw [h1, h3]
  by_cases ha : a ∈ s
  · rw [Set.indicator_of_notMem (by simp [ha] : a ∉ sᶜ)]
    simp
  · rw [Set.indicator_of_mem (ha : a ∈ sᶜ), h2, Set.indicator_of_notMem ha]
    simp

/-- The restriction operators of a set and its complement decompose the identity. -/
theorem deningerLpIndicator_add_compl (hs : MeasurableSet s) (f : Lp ℝ p μ) :
    deningerLpIndicator hs f + deningerLpIndicator hs.compl f = f := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add (deningerLpIndicator hs f) (deningerLpIndicator hs.compl f),
    deningerLpIndicatorFun_coeFn hs f, deningerLpIndicatorFun_coeFn hs.compl f] with a h0 h1 h2
  rw [h0]
  simp only [deningerLpIndicator_apply, Pi.add_apply]
  rw [h1, h2]
  by_cases ha : a ∈ s
  · have hc : a ∉ sᶜ := by simp [ha]
    rw [Set.indicator_of_mem ha, Set.indicator_of_notMem hc, add_zero]
  · have hc : a ∈ sᶜ := ha
    rw [Set.indicator_of_notMem ha, Set.indicator_of_mem hc, zero_add]

end LpIndicator

end RHTower
