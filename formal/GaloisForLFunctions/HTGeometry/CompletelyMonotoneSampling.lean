import GaloisForLFunctions.HTGeometry.HausdorffMomentTheorem

/-!
# Sampling a completely monotone function into the Hausdorff moment problem

This is the discretization half of the Bernstein–Widder representation theorem, which several
reservoir/Markov cards in the pipeline are gated on.

`CompletelyMonotoneDiff H` is complete monotonicity of `H` on `(0,∞)` in the finite-difference
form — every alternating forward difference of every positive step is nonnegative.  For continuous
`H` this is equivalent to the usual derivative form `(-1)^k H^{(k)} ≥ 0`, and it is the form the
Hausdorff moment problem consumes directly: sampling along an arithmetic progression
`n ↦ H(a + nδ)` inside `(0,∞)` yields a `HausdorffCompletelyMonotone` sequence
(`hausdorffCompletelyMonotone_sample`), because the step-`1` differences of the sample are exactly
the step-`δ` differences of `H` (`fwdDiff_iter_eq_sum_shift` on both sides).

`exists_hausdorffSource_of_completelyMonotoneDiff` then feeds this to the tree's Hausdorff moment
theorem: every such sample is the moment sequence of a finite positive measure on `[0,1]`.  What
remains for the full Bernstein–Widder statement is the limit `δ → 0` of these sample measures under
`t = e^{-δ r}`, for which mathlib now supplies Prokhorov
(`Mathlib/MeasureTheory/Measure/Prokhorov.lean`).

Also recorded: a completely monotone function is nonnegative (`completelyMonotoneDiff_nonneg`) and
antitone (`completelyMonotoneDiff_antitone`) on `(0,∞)` — the `k = 0` and `k = 1` cases.
-/

noncomputable section

open Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry



/-- Complete monotonicity of a function on the open right half line, in the finite-difference
form: every alternating forward difference of every positive step is nonnegative. -/
def CompletelyMonotoneDiff (H : ℝ → ℝ) : Prop :=
  ∀ (k : ℕ) (δ : ℝ), 0 < δ → ∀ t : ℝ, 0 < t → 0 ≤ (-1) ^ k * (fwdDiff δ)^[k] H t

/-- Sampling a completely monotone function along an arithmetic progression inside `(0,∞)`
produces a Hausdorff completely monotone sequence. -/
theorem hausdorffCompletelyMonotone_sample {H : ℝ → ℝ} (hH : CompletelyMonotoneDiff H)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    HausdorffCompletelyMonotone (fun n : ℕ => H (a + (n : ℝ) * δ)) := by
  intro m k
  have hrewrite : (fwdDiff (1 : ℕ))^[k] (fun n : ℕ => H (a + (n : ℝ) * δ)) m
      = (fwdDiff δ)^[k] H (a + (m : ℝ) * δ) := by
    rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 2
    push_cast
    ring
  rw [hrewrite]
  exact hH k δ hδ _ (by positivity)

/-- **Sampled Hausdorff representation.**  A completely monotone function on `(0,∞)`, sampled
along any arithmetic progression inside `(0,∞)`, is the moment sequence of a finite positive
measure on `[0,1]`.  This is the discretization half of the Bernstein–Widder representation: the
sample measures live on `[0,1]` and their moments recover `H` on the progression. -/
theorem exists_hausdorffSource_of_completelyMonotoneDiff {H : ℝ → ℝ}
    (hH : CompletelyMonotoneDiff H) {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    ∃ ν : Measure HausdorffSourceSpace, IsFiniteMeasure ν ∧
      ∀ n : ℕ, H (a + (n : ℝ) * δ) = ∫ y : HausdorffSourceSpace, (y : ℝ) ^ n ∂ν := by
  obtain ⟨ν, hfin, hmom⟩ :=
    exists_hausdorffSource_of_completelyMonotone (hausdorffCompletelyMonotone_sample hH ha hδ)
  refine ⟨ν, hfin, fun n => ?_⟩
  have h := congrFun hmom n
  exact h.symm

/-- A completely monotone function is nonnegative on `(0,∞)`. -/
theorem completelyMonotoneDiff_nonneg {H : ℝ → ℝ} (hH : CompletelyMonotoneDiff H)
    {t : ℝ} (ht : 0 < t) : 0 ≤ H t := by
  have h := hH 0 1 one_pos t ht
  simpa using h

/-- A completely monotone function is antitone on `(0,∞)`. -/
theorem completelyMonotoneDiff_antitone {H : ℝ → ℝ} (hH : CompletelyMonotoneDiff H)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : H t ≤ H s := by
  rcases eq_or_lt_of_le hst with rfl | hlt
  · exact le_rfl
  · have hδ : 0 < t - s := by linarith
    have h := hH 1 (t - s) hδ s hs
    simp only [Function.iterate_one, fwdDiff, pow_one] at h
    have hts : s + (t - s) = t := by ring
    rw [hts] at h
    linarith


end GaloisForLFunctions.HTGeometry

end
