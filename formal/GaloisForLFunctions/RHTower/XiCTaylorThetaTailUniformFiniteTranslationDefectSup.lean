import GaloisForLFunctions.RHTower.XiCTaylorThetaTailUniformFiniteTranslationDefectCurrent

/-!
# Uniform logarithmic-horizon control of the complete finite translation defect

The existing theorem controls every mesh-dependent displacement sequence below the logarithmic
horizon.  A primitive-ray chamber contains a continuum of such displacements at each mesh stage.
This file closes that quantifier gap: a diagonal choice argument upgrades the sequential theorem
to one eventual estimate holding simultaneously for every displacement in the full interval.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

private theorem eventually_forall_interval_of_tendsto_every_choice
    (F : ℕ → ℝ → ℝ) (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n)
    (hchoice : ∀ a : ℕ → ℝ,
      (∀ n, 0 ≤ a n) → (∀ n, a n ≤ B n) →
        Tendsto (fun n => F n (a n)) atTop (nhds 0))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∀ a : ℝ, 0 ≤ a → a ≤ B n → F n a < epsilon := by
  classical
  by_contra hnot
  have hfrequentRaw : ∃ᶠ n : ℕ in atTop,
      ∃ a : ℝ, ∃ (_ha : 0 ≤ a), ∃ (_hale : a ≤ B n), epsilon ≤ F n a := by
    simpa only [not_eventually, not_forall, Classical.not_imp, not_lt] using hnot
  have hfrequent : ∃ᶠ n : ℕ in atTop,
      ∃ a : ℝ, 0 ≤ a ∧ a ≤ B n ∧ epsilon ≤ F n a := by
    apply hfrequentRaw.mono
    intro n hn
    rcases hn with ⟨a, ha, hale, hlarge⟩
    exact ⟨a, ha, hale, hlarge⟩
  let Bad : ℕ → Prop := fun n =>
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ B n ∧ epsilon ≤ F n a
  let a : ℕ → ℝ := fun n => if hn : Bad n then Classical.choose hn else 0
  have ha0 : ∀ n, 0 ≤ a n := by
    intro n
    by_cases hn : Bad n
    · simp only [a, dif_pos hn]
      exact (Classical.choose_spec hn).1
    · simp only [a, dif_neg hn]
      exact le_rfl
  have hale : ∀ n, a n ≤ B n := by
    intro n
    by_cases hn : Bad n
    · simp only [a, dif_pos hn]
      exact (Classical.choose_spec hn).2.1
    · simp only [a, dif_neg hn]
      exact hB n
  have hselected : ∃ᶠ n : ℕ in atTop, epsilon ≤ F n (a n) := by
    apply hfrequent.mono
    intro n hn
    change Bad n at hn
    change epsilon ≤ F n (if h : Bad n then Classical.choose h else 0)
    rw [dif_pos hn]
    exact (Classical.choose_spec hn).2.2
  have hsmall : ∀ᶠ n : ℕ in atTop, F n (a n) < epsilon :=
    (tendsto_order.1 (hchoice a ha0 hale)).2 epsilon hepsilon
  obtain ⟨n, hnLarge, hnSmall⟩ := (hselected.and_eventually hsmall).exists
  exact (not_lt_of_ge hnLarge) hnSmall

/-- **Continuum-uniform complete positive-channel defect.**  At sufficiently large mesh stage,
the same bound holds for every displacement below the logarithmic horizon. -/
theorem eventually_forall_thetaCuspTailPhaseTranslationFullDefect_mul_pow_lt_of_le
    (A M R : ℕ) (hR : 1 ≤ R) (d : ℕ → ℕ) (hd : ∀ n, n ≤ d n)
    (z : ℕ → ℂ) (hz : ∀ᶠ n : ℕ in atTop, ‖z n‖ ≤ R)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∀ a : ℝ,
      0 ≤ a → a ≤ xiCTaylorLogarithmicHaarDisplacement A n →
        |thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent (d n) (z n) a| *
          (((n + 1 : ℕ) : ℝ) ^ M) < epsilon := by
  let F : ℕ → ℝ → ℝ := fun n a =>
    |thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent (d n) (z n) a| *
      (((n + 1 : ℕ) : ℝ) ^ M)
  let B : ℕ → ℝ := xiCTaylorLogarithmicHaarDisplacement A
  apply eventually_forall_interval_of_tendsto_every_choice F B
  · intro n
    unfold B xiCTaylorLogarithmicHaarDisplacement xiCTaylorLogarithmicHaarDepth
    positivity
  · intro a ha hale
    simpa only [F] using
      tendsto_thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent_mul_pow_zero_of_le
        A M R hR d hd z hz a ha hale
  · exact hepsilon

/-- Scheduled continuum-uniform positive channel at twice the local Xi order. -/
theorem eventually_forall_scheduled_thetaCuspTailPhaseTranslationFullDefect_localOrder_of_le
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (A : ℕ) (sigma : ℂ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∀ a : ℝ,
      0 ≤ a → a ≤ xiCTaylorLogarithmicHaarDisplacement A n →
        |thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent
            (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
            (xiCTaylorAnisotropicCenteredPoint sigma n) a| *
          (((n + 1 : ℕ) : ℝ) ^
            (2 * (analyticOrderAt xi sigma).toNat)) < epsilon := by
  obtain ⟨R, hR, hz⟩ :=
    exists_eventually_xiCTaylorAnisotropicCenteredPoint_norm_le_nat sigma
  exact eventually_forall_thetaCuspTailPhaseTranslationFullDefect_mul_pow_lt_of_le
    A (2 * (analyticOrderAt xi sigma).toNat) R hR
      (fun n => D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
      (le_xiCTaylorScheduledThetaTailDepth hD sigma)
      (xiCTaylorAnisotropicCenteredPoint sigma) hz hepsilon

/-- Scheduled continuum-uniform negative channel on the same one-sided mesh. -/
theorem eventually_forall_scheduled_thetaCuspTailNegativePhaseTranslationFullDefect_localOrder_of_le
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (A : ℕ) (sigma : ℂ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∀ a : ℝ,
      0 ≤ a → a ≤ xiCTaylorLogarithmicHaarDisplacement A n →
        |thetaCuspTailNegativePhaseTranslationFullDefectIntegratedCurrent
            (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
            (xiCTaylorAnisotropicCenteredPoint sigma n) a| *
          (((n + 1 : ℕ) : ℝ) ^
            (2 * (analyticOrderAt xi sigma).toNat)) < epsilon := by
  obtain ⟨R, hR, hz⟩ :=
    exists_eventually_xiCTaylorAnisotropicCenteredPoint_norm_le_nat sigma
  have hzneg : ∀ᶠ n : ℕ in atTop,
      ‖-xiCTaylorAnisotropicCenteredPoint sigma n‖ ≤ R := by
    simpa only [norm_neg] using hz
  have hpositive :=
    eventually_forall_thetaCuspTailPhaseTranslationFullDefect_mul_pow_lt_of_le
      A (2 * (analyticOrderAt xi sigma).toNat) R hR
        (fun n => D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
        (le_xiCTaylorScheduledThetaTailDepth hD sigma)
        (fun n => -xiCTaylorAnisotropicCenteredPoint sigma n) hzneg hepsilon
  filter_upwards [hpositive] with n hn
  intro a ha hale
  rw [thetaCuspTailNegativePhaseTranslationFullDefectIntegratedCurrent_eq_neg_positive_neg,
    abs_neg]
  exact hn a ha hale

end

end RHTower
