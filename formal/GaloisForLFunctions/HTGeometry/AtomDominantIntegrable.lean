import GaloisForLFunctions.HTGeometry.AtomKernelDominant

/-!
# Integrability of the atom dominant

The atom-limit layer carries the hypothesis that the height-independent dominant is integrable, and
nothing established it.  The dominant is a bounded indicator near the node plus a multiple of the
Herglotz weight away from it, so its integrability is exactly the two standing conditions of a
Herglotz measure: finite mass on a bounded set, and an integrable Herglotz weight.  For a finite
measure both are automatic.

* **`integrable_atomDominant`** — the criterion;
* **`integrable_atomDominant_of_isFiniteMeasure`** — hence no hypothesis at all on a finite measure.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

open scoped Classical ENNReal

theorem measurableSet_atomBall (a R : ℝ) : MeasurableSet {t : ℝ | |t - a| < R} :=
  (isOpen_lt (by fun_prop) continuous_const).measurableSet

/-- **The atom dominant is integrable under the two Herglotz conditions.**  Near the node it is the
constant one on a set of finite measure; away from it, a multiple of the Herglotz weight. -/
theorem integrable_atomDominant {a R : ℝ} (ν : Measure ℝ)
    (hball : ν {t : ℝ | |t - a| < R} ≠ ∞)
    (hherglotz : Integrable (fun t : ℝ => 1 / (1 + t ^ 2)) ν) :
    Integrable (atomDominant a R) ν := by
  have hmeas := measurableSet_atomBall a R
  have h1 : Integrable
      (Set.indicator {t : ℝ | |t - a| < R} (fun _ => (1 : ℝ))) ν := by
    refine IntegrableOn.integrable_indicator ?_ hmeas
    exact integrableOn_const hball (by simp)
  have h2 : Integrable
      (Set.indicator {t : ℝ | ¬ |t - a| < R}
        (fun s => tailComparison a R / (1 + s ^ 2))) ν := by
    refine Integrable.indicator ?_ hmeas.compl
    have := hherglotz.const_mul (tailComparison a R)
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    simp [div_eq_mul_inv]
  have hfun : atomDominant a R =
      fun t => Set.indicator {t : ℝ | |t - a| < R} (fun _ => (1 : ℝ)) t +
        Set.indicator {t : ℝ | ¬ |t - a| < R}
          (fun s => tailComparison a R / (1 + s ^ 2)) t :=
    funext (atomDominant_eq_indicator a R)
  rw [hfun]
  exact h1.add h2

/-- The Herglotz weight is bounded, hence integrable against any finite measure. -/
theorem integrable_herglotzWeight_of_isFiniteMeasure (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Integrable (fun t : ℝ => 1 / (1 + t ^ 2)) ν := by
  refine (integrable_const (1 : ℝ)).mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
  · exact ((measurable_const.div ((measurable_const.add
      (measurable_id.pow_const 2)))).aestronglyMeasurable)
  · have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [div_le_one hpos]
    nlinarith [sq_nonneg t]

/-- **On a finite measure the atom dominant is integrable outright.** -/
theorem integrable_atomDominant_of_isFiniteMeasure {a R : ℝ} (ν : Measure ℝ)
    [IsFiniteMeasure ν] : Integrable (atomDominant a R) ν :=
  integrable_atomDominant ν (measure_ne_top ν _)
    (integrable_herglotzWeight_of_isFiniteMeasure ν)

end

end GaloisForLFunctions.HTGeometry
