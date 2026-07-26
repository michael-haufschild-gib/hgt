import GaloisForLFunctions.RHTower.XiCTaylorThetaTailUniformFiniteTranslationDefectCurrent

/-!
# Continuum-uniform signed finite translation defect

A diagonal choice argument upgrades the signed sequential estimate to one eventual estimate for
every displacement in the symmetric logarithmic chamber.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

private theorem eventually_forall_absInterval_of_tendsto_every_choice
    (F : ℕ → ℝ → ℝ) (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n)
    (hchoice : ∀ a : ℕ → ℝ,
      (∀ n, |a n| ≤ B n) → Tendsto (fun n => F n (a n)) atTop (nhds 0))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∀ a : ℝ, |a| ≤ B n → F n a < epsilon := by
  classical
  by_contra hnot
  have hfrequentRaw : ∃ᶠ n : ℕ in atTop,
      ∃ a : ℝ, ∃ (_hale : |a| ≤ B n), epsilon ≤ F n a := by
    simpa only [not_eventually, not_forall, Classical.not_imp, not_lt] using hnot
  have hfrequent : ∃ᶠ n : ℕ in atTop,
      ∃ a : ℝ, |a| ≤ B n ∧ epsilon ≤ F n a := by
    apply hfrequentRaw.mono
    intro n hn
    rcases hn with ⟨a, hale, hlarge⟩
    exact ⟨a, hale, hlarge⟩
  let Bad : ℕ → Prop := fun n =>
    ∃ a : ℝ, |a| ≤ B n ∧ epsilon ≤ F n a
  let a : ℕ → ℝ := fun n => if hn : Bad n then Classical.choose hn else 0
  have hale : ∀ n, |a n| ≤ B n := by
    intro n
    by_cases hn : Bad n
    · simp only [a, dif_pos hn]
      exact (Classical.choose_spec hn).1
    · simp only [a, dif_neg hn, abs_zero]
      exact hB n
  have hselected : ∃ᶠ n : ℕ in atTop, epsilon ≤ F n (a n) := by
    apply hfrequent.mono
    intro n hn
    change Bad n at hn
    change epsilon ≤ F n (if h : Bad n then Classical.choose h else 0)
    rw [dif_pos hn]
    exact (Classical.choose_spec hn).2
  have hsmall : ∀ᶠ n : ℕ in atTop, F n (a n) < epsilon :=
    (tendsto_order.1 (hchoice a hale)).2 epsilon hepsilon
  obtain ⟨n, hnLarge, hnSmall⟩ := (hselected.and_eventually hsmall).exists
  exact (not_lt_of_ge hnLarge) hnSmall

/-- **Continuum-uniform signed complete defect.**  One eventual estimate holds simultaneously
for every displacement in the symmetric logarithmic chamber. -/
theorem eventually_forall_thetaCuspTailPhaseTranslationFullDefect_mul_pow_lt_of_abs_le
    (A M R : ℕ) (hR : 1 ≤ R) (d : ℕ → ℕ) (hd : ∀ n, n ≤ d n)
    (z : ℕ → ℂ) (hz : ∀ᶠ n : ℕ in atTop, ‖z n‖ ≤ R)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∀ a : ℝ,
      |a| ≤ xiCTaylorLogarithmicHaarDisplacement A n →
        |thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent (d n) (z n) a| *
          (((n + 1 : ℕ) : ℝ) ^ M) < epsilon := by
  let F : ℕ → ℝ → ℝ := fun n a =>
    |thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent (d n) (z n) a| *
      (((n + 1 : ℕ) : ℝ) ^ M)
  let B : ℕ → ℝ := xiCTaylorLogarithmicHaarDisplacement A
  apply eventually_forall_absInterval_of_tendsto_every_choice F B
  · intro n
    unfold B xiCTaylorLogarithmicHaarDisplacement xiCTaylorLogarithmicHaarDepth
    positivity
  · intro a hale
    simpa only [F] using
      tendsto_thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent_mul_pow_zero_of_abs_le
        A M R hR d hd z hz a hale
  · exact hepsilon

/-- Scheduled continuum-uniform signed channel at twice the local Xi order. -/
theorem eventually_forall_scheduled_thetaCuspTailPhaseTranslationFullDefect_localOrder_of_abs_le
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (A : ℕ) (sigma : ℂ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∀ a : ℝ,
      |a| ≤ xiCTaylorLogarithmicHaarDisplacement A n →
        |thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent
            (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
            (xiCTaylorAnisotropicCenteredPoint sigma n) a| *
          (((n + 1 : ℕ) : ℝ) ^
            (2 * (analyticOrderAt xi sigma).toNat)) < epsilon := by
  obtain ⟨R, hR, hz⟩ :=
    exists_eventually_xiCTaylorAnisotropicCenteredPoint_norm_le_nat sigma
  exact eventually_forall_thetaCuspTailPhaseTranslationFullDefect_mul_pow_lt_of_abs_le
    A (2 * (analyticOrderAt xi sigma).toNat) R hR
      (fun n => D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
      (le_xiCTaylorScheduledThetaTailDepth hD sigma)
      (xiCTaylorAnisotropicCenteredPoint sigma) hz hepsilon

end


end RHTower
