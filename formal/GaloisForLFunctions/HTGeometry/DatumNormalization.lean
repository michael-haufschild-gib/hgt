import GaloisForLFunctions.HTGeometry.JumpProfileLevels

/-!
# Normalizing a Mellin datum

A density produced by a Mellin representation is only measurable and bounded on `(1, ∞)`.  Cutting
it off below `1` produces a globally bounded, globally measurable function with the same Mellin
transform, the same primitives on `[1, ∞)`, and the same decay.
-/

noncomputable section

open MeasureTheory Filter

namespace GaloisForLFunctions.HTGeometry

/-- The datum cut off below `1`. -/
def truncDatum (q : ℝ → ℂ) : ℝ → ℂ := Set.indicator (Set.Ioi (1:ℝ)) q

theorem truncDatum_apply_of_lt {q : ℝ → ℂ} {t : ℝ} (ht : 1 < t) : truncDatum q t = q t := by
  rw [truncDatum, Set.indicator_of_mem (Set.mem_Ioi.2 ht)]

theorem truncDatum_apply_of_le {q : ℝ → ℂ} {t : ℝ} (ht : t ≤ 1) : truncDatum q t = 0 := by
  rw [truncDatum, Set.indicator_of_notMem (by simpa using ht)]

theorem norm_truncDatum_le {q : ℝ → ℂ} {M : ℝ} (hM : ∀ x : ℝ, 1 ≤ x → ‖q x‖ ≤ M) (t : ℝ) :
    ‖truncDatum q t‖ ≤ max M 0 := by
  rcases lt_or_ge 1 t with ht | ht
  · rw [truncDatum_apply_of_lt ht]
    exact le_trans (hM t (le_of_lt ht)) (le_max_left _ _)
  · rw [truncDatum_apply_of_le ht, norm_zero]
    exact le_max_right _ _

theorem aestronglyMeasurable_truncDatum {q : ℝ → ℂ}
    (hq : AEStronglyMeasurable q (volume.restrict (Set.Ioi (1:ℝ)))) :
    AEStronglyMeasurable (truncDatum q) volume :=
  (aestronglyMeasurable_indicator_iff measurableSet_Ioi).2 hq

theorem intervalIntegrable_truncDatum {q : ℝ → ℂ} {M : ℝ}
    (hq : AEStronglyMeasurable q (volume.restrict (Set.Ioi (1:ℝ))))
    (hM : ∀ x : ℝ, 1 ≤ x → ‖q x‖ ≤ M) (u v : ℝ) :
    IntervalIntegrable (truncDatum q) volume u v := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded ?_ (aestronglyMeasurable_truncDatum hq)
    (M := max M 0) (Filter.Eventually.of_forall (fun t => norm_truncDatum_le hM t))
  rw [Set.uIoc_eq_union]
  refine ne_of_lt (lt_of_le_of_lt (measure_union_le _ _) ?_)
  exact ENNReal.add_lt_top.2 ⟨measure_Ioc_lt_top, measure_Ioc_lt_top⟩

theorem tendsto_truncDatum {q : ℝ → ℂ} (h : Tendsto q atTop (nhds 0)) :
    Tendsto (truncDatum q) atTop (nhds 0) := by
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
  exact (truncDatum_apply_of_lt ht).symm

theorem setIntegral_truncDatum (q f : ℝ → ℂ) :
    (∫ x in Set.Ioi (1:ℝ), truncDatum q x * f x) = ∫ x in Set.Ioi (1:ℝ), q x * f x := by
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [truncDatum_apply_of_lt (Set.mem_Ioi.1 hx)]

theorem integral_truncDatum_interval (q : ℝ → ℂ) {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in (1:ℝ)..x, truncDatum q t) = ∫ t in (1:ℝ)..x, q t := by
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
  rw [Set.uIoc_of_le hx] at ht
  rw [truncDatum_apply_of_lt ht.1]

/-- Past `1` the whole chain is unchanged by the cut-off. -/
theorem iteratedAntideriv_truncDatum (q : ℝ → ℂ) :
    ∀ (j : ℕ) {y : ℝ}, 1 ≤ y →
      iteratedAntideriv (truncDatum q) (j + 1) y = iteratedAntideriv q (j + 1) y := by
  intro j
  induction j with
  | zero =>
      intro y hy
      rw [iteratedAntideriv_succ, iteratedAntideriv_succ]
      exact integral_truncDatum_interval q hy
  | succ j ih =>
      intro y hy
      rw [iteratedAntideriv_succ, iteratedAntideriv_succ]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hy] at ht
      exact ih ht.1

theorem arithJumpProfile_truncDatum (q : ℝ → ℂ) (a : ℕ → ℂ) (j : ℕ) {y : ℝ} (hy : 1 ≤ y) :
    arithJumpProfile (truncDatum q) a j y = arithJumpProfile q a j y := by
  rw [arithJumpProfile, arithJumpProfile, iteratedAntideriv_truncDatum q j hy]

end GaloisForLFunctions.HTGeometry

end
