import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# The `α`-power estimate for averages of `log⁺`

For `0 < α` and a nonnegative function `F`,

```text
⨍ log⁺ F  =  (1/α) · ⨍ log⁺ (F^α)  ≤  (1/α) · ⨍ log (1 + F^α)  ≤  (1/α) · log (1 + ⨍ F^α),
```

the last step by Jensen's inequality for the concave function `y ↦ log (1 + y)`.

This is the device that makes a sum of many small contributions affordable inside a `log⁺` average:
if `F` is a sum of `n` terms each of whose `α`-th powers has bounded average, then `⨍ F^α ≤ n·C` by
the subadditivity `(x + y)^α ≤ x^α + y^α` for `α ≤ 1`, and the average of `log⁺ F` costs only
`(1/α)·log(1 + nC)`.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Real

/-- `y ↦ log (1 + y)` is concave on the nonnegative reals. -/
theorem concaveOn_log_one_add : ConcaveOn ℝ (Set.Ici (0 : ℝ)) fun y => Real.log (1 + y) := by
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  have hx0 : (0 : ℝ) < 1 + x := by
    rw [Set.mem_Ici] at hx
    linarith
  have hy0 : (0 : ℝ) < 1 + y := by
    rw [Set.mem_Ici] at hy
    linarith
  have hlog := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.mpr hx0) (Set.mem_Ioi.mpr hy0)
    ha hb hab
  have heq : a • (1 + x) + b • (1 + y) = 1 + (a • x + b • y) := by
    simp only [smul_eq_mul]
    nlinarith [hab]
  rw [heq] at hlog
  exact hlog

/-- `log (1 + y) ≤ y` for `y ≥ 0`. -/
theorem log_one_add_le {y : ℝ} (hy : 0 ≤ y) : Real.log (1 + y) ≤ y := by
  have h := Real.add_one_le_exp y
  have h1 : (0 : ℝ) < 1 + y := by linarith
  calc Real.log (1 + y) ≤ Real.log (Real.exp y) := by
        refine Real.log_le_log h1 ?_
        linarith [h]
    _ = y := Real.log_exp y

/-- `log⁺ y ≤ log (1 + y)` for `y ≥ 0`. -/
theorem posLog_le_log_one_add {y : ℝ} (hy : 0 ≤ y) : Real.posLog y ≤ Real.log (1 + y) := by
  rw [Real.posLog]
  refine max_le ?_ ?_
  · exact Real.log_nonneg (by linarith)
  · rcases eq_or_lt_of_le hy with h | h
    · rw [← h]
      simp
    · exact Real.log_le_log h (by linarith)

/-- `log⁺ y ≤ y` for `y ≥ 0`. -/
theorem posLog_le_self {y : ℝ} (hy : 0 ≤ y) : Real.posLog y ≤ y :=
  le_trans (posLog_le_log_one_add hy) (log_one_add_le hy)

/-- `log⁺` of a power: `log⁺ (y^α) = α · log⁺ y` for `α > 0` and `y ≥ 0`. -/
theorem posLog_rpow {α : ℝ} (hα : 0 < α) {y : ℝ} (hy : 0 ≤ y) :
    Real.posLog (y ^ α) = α * Real.posLog y := by
  rcases eq_or_lt_of_le hy with h | h
  · rw [← h, Real.zero_rpow (ne_of_gt hα)]
    simp [Real.posLog]
  · rw [Real.posLog, Real.posLog, Real.log_rpow h]
    rcases le_or_gt (Real.log y) 0 with hl | hl
    · rw [max_eq_left (show α * Real.log y ≤ 0 by nlinarith), max_eq_left hl, mul_zero]
    · rw [max_eq_right (show (0 : ℝ) ≤ α * Real.log y by positivity), max_eq_right hl.le]

/-- **Jensen's inequality for `log (1 + ·)`.** -/
theorem average_log_one_add_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    [NeZero μ] {G : Ω → ℝ} (hG0 : ∀ x, 0 ≤ G x) (hint : Integrable G μ) :
    ⨍ x, Real.log (1 + G x) ∂μ ≤ Real.log (1 + ⨍ x, G x ∂μ) := by
  have hmem : ∀ᵐ x ∂μ, G x ∈ Set.Ici (0 : ℝ) :=
    Filter.Eventually.of_forall fun x => Set.mem_Ici.mpr (hG0 x)
  have hcont : ContinuousOn (fun y => Real.log (1 + y)) (Set.Ici (0 : ℝ)) := by
    refine ContinuousOn.log (by fun_prop) fun y hy => ?_
    rw [Set.mem_Ici] at hy
    linarith
  have haem : AEMeasurable (fun x => 1 + G x) μ := aemeasurable_const.add hint.aemeasurable
  have hcomp : Integrable (fun x => Real.log (1 + G x)) μ := by
    refine Integrable.mono' hint
      (Real.measurable_log.comp_aemeasurable haem).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith [hG0 x]))]
    exact log_one_add_le (hG0 x)
  exact concaveOn_log_one_add.le_map_average hcont isClosed_Ici hmem hint hcomp

/-- **The `α`-power estimate for an average of `log⁺`.**  A nonnegative function whose `α`-th power
is integrable has `⨍ log⁺ F ≤ (1/α) · log (1 + ⨍ F^α)`. -/
theorem average_posLog_le_log_one_add_average_rpow {α : ℝ} (hα : 0 < α) {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] [NeZero μ] {F : Ω → ℝ}
    (hF0 : ∀ x, 0 ≤ F x) (hFmeas : Measurable F) (hint : Integrable (fun x => (F x) ^ α) μ) :
    ⨍ x, Real.posLog (F x) ∂μ ≤ (1 / α) * Real.log (1 + ⨍ x, (F x) ^ α ∂μ) := by
  have hG0 : ∀ x, 0 ≤ (F x) ^ α := fun x => Real.rpow_nonneg (hF0 x) α
  have hmF : Measurable fun x => (F x) ^ α := hFmeas.pow_const α
  have hlint : Integrable (fun x => Real.log (1 + (F x) ^ α)) μ := by
    refine Integrable.mono' hint ((measurable_const.add hmF).log).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith [hG0 x]))]
    exact log_one_add_le (hG0 x)
  have hpm : Measurable fun x => Real.posLog ((F x) ^ α) := by
    simp only [Real.posLog]
    exact measurable_const.max (Real.measurable_log.comp hmF)
  have hpint : Integrable (fun x => Real.posLog ((F x) ^ α)) μ := by
    refine Integrable.mono' hint hpm.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    exact posLog_le_self (hG0 x)
  have hle : ∀ x, Real.posLog ((F x) ^ α) ≤ Real.log (1 + (F x) ^ α) :=
    fun x => posLog_le_log_one_add (hG0 x)
  have havgmono : ⨍ x, Real.posLog ((F x) ^ α) ∂μ ≤ ⨍ x, Real.log (1 + (F x) ^ α) ∂μ := by
    rw [MeasureTheory.average_eq, MeasureTheory.average_eq]
    refine smul_le_smul_of_nonneg_left
      (MeasureTheory.integral_mono hpint hlint hle) (by positivity)
  have hpt : (fun x => Real.posLog (F x)) = fun x => (1 / α) * Real.posLog ((F x) ^ α) := by
    funext x
    rw [posLog_rpow hα (hF0 x)]
    field_simp
  have hlin : ⨍ x, (1 / α) * Real.posLog ((F x) ^ α) ∂μ
      = (1 / α) * ⨍ x, Real.posLog ((F x) ^ α) ∂μ := by
    rw [MeasureTheory.average_eq, MeasureTheory.average_eq, MeasureTheory.integral_const_mul,
      smul_eq_mul, smul_eq_mul]
    ring
  rw [hpt, hlin]
  have hstep := average_log_one_add_le hG0 hint
  have hαinv : (0 : ℝ) ≤ 1 / α := by positivity
  calc (1 / α) * ⨍ x, Real.posLog ((F x) ^ α) ∂μ
      ≤ (1 / α) * ⨍ x, Real.log (1 + (F x) ^ α) ∂μ :=
        mul_le_mul_of_nonneg_left havgmono hαinv
    _ ≤ (1 / α) * Real.log (1 + ⨍ x, (F x) ^ α ∂μ) := mul_le_mul_of_nonneg_left hstep hαinv

end GaloisForLFunctions.HTGeometry
