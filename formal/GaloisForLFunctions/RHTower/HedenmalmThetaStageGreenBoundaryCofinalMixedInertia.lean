import GaloisForLFunctions.RHTower.HedenmalmThetaActualStageGreenBalance
import GaloisForLFunctions.RHTower.HedenmalmPinnedVolterraBoundaryDefect

/-!
# Cofinal mixed inertia of actual theta-stage Green boundaries

Actual complete Green boundaries converge in operator norm to the pinned rank-two boundary form.
The limiting form has two fixed source vectors with quadratic values `1/6` and `-1/6`.  Continuous
quadratic evaluation therefore preserves both signs, with uniform half-margin, throughout one
cofinal tail.  Thus neither eventual positive nor eventual negative semidefiniteness can provide
the missing upstream arithmetic selector for theta-stage Green neutrality or GTA quartic charge.
-/

open Complex Filter

namespace RHTower.HedenmalmThetaSource

open RHTower

noncomputable section

/-- Operator-norm convergence transports to the real quadratic form on every fixed source vector. -/
theorem tendsto_re_inner_thetaSourceSignedStageGreenBoundary
    (f : H) :
    Tendsto
      (fun k => (inner ℂ (thetaSourceSignedStageGreenBoundary k f) f : ℂ).re)
      atTop (nhds (inner ℂ (pinnedBoundaryCLM f) f : ℂ).re) := by
  have hcontinuous : Continuous
      (fun T : H →L[ℂ] H => (inner ℂ (T f) f : ℂ).re) := by
    fun_prop
  exact hcontinuous.continuousAt.tendsto.comp
    thetaSourceSignedStageGreenBoundary_tendsto_pinned

/-- Same two fixed source vectors witness quantitatively strict mixed inertia at every sufficiently
late actual theta stage. -/
theorem eventually_thetaSourceSignedStageGreenBoundary_fixed_mixedInertia :
    ∀ᶠ k in atTop,
      (1 : ℝ) / 12 <
          (inner ℂ
            (thetaSourceSignedStageGreenBoundary k pinnedPositiveMode)
            pinnedPositiveMode : ℂ).re ∧
        (inner ℂ
            (thetaSourceSignedStageGreenBoundary k pinnedNegativeMode)
            pinnedNegativeMode : ℂ).re < -(1 : ℝ) / 12 := by
  have hpos : Tendsto
      (fun k => (inner ℂ
        (thetaSourceSignedStageGreenBoundary k pinnedPositiveMode)
        pinnedPositiveMode : ℂ).re)
      atTop (nhds ((1 : ℝ) / 6)) := by
    simpa [inner_pinnedBoundaryCLM_pinnedPositiveMode] using
      tendsto_re_inner_thetaSourceSignedStageGreenBoundary pinnedPositiveMode
  have hneg : Tendsto
      (fun k => (inner ℂ
        (thetaSourceSignedStageGreenBoundary k pinnedNegativeMode)
        pinnedNegativeMode : ℂ).re)
      atTop (nhds (-(1 : ℝ) / 6)) := by
    simpa [inner_pinnedBoundaryCLM_pinnedNegativeMode] using
      tendsto_re_inner_thetaSourceSignedStageGreenBoundary pinnedNegativeMode
  exact ((tendsto_order.1 hpos).1 ((1 : ℝ) / 12) (by norm_num)).and
    ((tendsto_order.1 hneg).2 (-(1 : ℝ) / 12) (by norm_num))

/-- Eventual positive semidefiniteness is incompatible with the fixed negative source witness. -/
theorem not_eventually_thetaSourceSignedStageGreenBoundary_isPositive :
    ¬ ∀ᶠ k in atTop, (thetaSourceSignedStageGreenBoundary k).IsPositive := by
  intro hpositive
  obtain ⟨k, hk, hmix⟩ :=
    (hpositive.and
      eventually_thetaSourceSignedStageGreenBoundary_fixed_mixedInertia).exists
  have hnonneg := hk.2 pinnedNegativeMode
  change 0 ≤
    (inner ℂ (thetaSourceSignedStageGreenBoundary k pinnedNegativeMode)
      pinnedNegativeMode : ℂ).re at hnonneg
  linarith

/-- Eventual negative semidefiniteness is incompatible with the fixed positive source witness. -/
theorem not_eventually_neg_thetaSourceSignedStageGreenBoundary_isPositive :
    ¬ ∀ᶠ k in atTop, (-thetaSourceSignedStageGreenBoundary k).IsPositive := by
  intro hpositive
  obtain ⟨k, hk, hmix⟩ :=
    (hpositive.and
      eventually_thetaSourceSignedStageGreenBoundary_fixed_mixedInertia).exists
  have hnonneg := hk.2 pinnedPositiveMode
  change 0 ≤
    (inner ℂ ((-thetaSourceSignedStageGreenBoundary k) pinnedPositiveMode)
      pinnedPositiveMode : ℂ).re at hnonneg
  simp only [neg_apply, inner_neg_left, Complex.neg_re] at hnonneg
  linarith

/-- Exact squared norm of the fixed positive witness. -/
theorem norm_pinnedPositiveMode_sq :
    ‖pinnedPositiveMode‖ ^ (2 : ℕ) = (13 : ℝ) / 12 := by
  calc
    ‖pinnedPositiveMode‖ ^ (2 : ℕ) =
        (inner ℂ pinnedPositiveMode pinnedPositiveMode : ℂ).re :=
      (inner_self_eq_norm_sq (𝕜 := ℂ) pinnedPositiveMode).symm
    _ = (13 : ℝ) / 12 := by
      simp only [pinnedPositiveMode, inner_sub_left, inner_sub_right,
        inner_pinnedOne_pinnedOne, inner_pinnedOne_pinnedCenter,
        inner_pinnedCenter_pinnedOne, inner_pinnedCenter_pinnedCenter]
      norm_num

/-- Exact squared norm of the fixed negative witness. -/
theorem norm_pinnedNegativeMode_sq :
    ‖pinnedNegativeMode‖ ^ (2 : ℕ) = (13 : ℝ) / 12 := by
  calc
    ‖pinnedNegativeMode‖ ^ (2 : ℕ) =
        (inner ℂ pinnedNegativeMode pinnedNegativeMode : ℂ).re :=
      (inner_self_eq_norm_sq (𝕜 := ℂ) pinnedNegativeMode).symm
    _ = (13 : ℝ) / 12 := by
      simp only [pinnedNegativeMode, inner_add_left, inner_add_right,
        inner_pinnedOne_pinnedOne, inner_pinnedOne_pinnedCenter,
        inner_pinnedCenter_pinnedOne, inner_pinnedCenter_pinnedCenter]
      norm_num

/-- Cofinal actual boundaries remain uniformly separated from the positive-operator cone. -/
theorem eventually_thetaSourceSignedStageGreenBoundary_distance_positiveCone :
    ∀ᶠ k in atTop, ∀ P : H →L[ℂ] H, P.IsPositive →
      (1 : ℝ) / 13 < ‖thetaSourceSignedStageGreenBoundary k - P‖ := by
  filter_upwards [eventually_thetaSourceSignedStageGreenBoundary_fixed_mixedInertia]
    with k hmix
  intro P hP
  have hPnonneg := hP.2 pinnedNegativeMode
  change 0 ≤ (inner ℂ (P pinnedNegativeMode) pinnedNegativeMode : ℂ).re at hPnonneg
  have hdiff :
      (inner ℂ
        ((thetaSourceSignedStageGreenBoundary k - P) pinnedNegativeMode)
        pinnedNegativeMode : ℂ).re < -(1 : ℝ) / 12 := by
    rw [sub_apply, inner_sub_left, Complex.sub_re]
    linarith [hmix.2]
  have habs : (1 : ℝ) / 12 <
      |(inner ℂ
        ((thetaSourceSignedStageGreenBoundary k - P) pinnedNegativeMode)
        pinnedNegativeMode : ℂ).re| := by
    rw [abs_of_neg (lt_trans hdiff (by norm_num))]
    linarith
  have hbound :
      |(inner ℂ
        ((thetaSourceSignedStageGreenBoundary k - P) pinnedNegativeMode)
        pinnedNegativeMode : ℂ).re| ≤
        ‖thetaSourceSignedStageGreenBoundary k - P‖ * ‖pinnedNegativeMode‖ ^ (2 : ℕ) := by
    calc
      |_|≤ ‖(inner ℂ
          ((thetaSourceSignedStageGreenBoundary k - P) pinnedNegativeMode)
          pinnedNegativeMode : ℂ)‖ := Complex.abs_re_le_norm _
      _ ≤ ‖(thetaSourceSignedStageGreenBoundary k - P) pinnedNegativeMode‖ *
          ‖pinnedNegativeMode‖ := norm_inner_le_norm _ _
      _ ≤ (‖thetaSourceSignedStageGreenBoundary k - P‖ * ‖pinnedNegativeMode‖) *
          ‖pinnedNegativeMode‖ := by
            exact mul_le_mul_of_nonneg_right
              ((thetaSourceSignedStageGreenBoundary k - P).le_opNorm _)
              (norm_nonneg _)
      _ = ‖thetaSourceSignedStageGreenBoundary k - P‖ *
          ‖pinnedNegativeMode‖ ^ (2 : ℕ) := by ring
  rw [norm_pinnedNegativeMode_sq] at hbound
  nlinarith [norm_nonneg (thetaSourceSignedStageGreenBoundary k - P)]

/-- Cofinal actual boundaries remain uniformly separated from the negative-operator cone. -/
theorem eventually_thetaSourceSignedStageGreenBoundary_distance_negativeCone :
    ∀ᶠ k in atTop, ∀ P : H →L[ℂ] H, P.IsPositive →
      (1 : ℝ) / 13 < ‖thetaSourceSignedStageGreenBoundary k + P‖ := by
  filter_upwards [eventually_thetaSourceSignedStageGreenBoundary_fixed_mixedInertia]
    with k hmix
  intro P hP
  have hPnonneg := hP.2 pinnedPositiveMode
  change 0 ≤ (inner ℂ (P pinnedPositiveMode) pinnedPositiveMode : ℂ).re at hPnonneg
  have hdiff : (1 : ℝ) / 12 <
      (inner ℂ
        ((thetaSourceSignedStageGreenBoundary k + P) pinnedPositiveMode)
        pinnedPositiveMode : ℂ).re := by
    rw [add_apply, inner_add_left, Complex.add_re]
    linarith [hmix.1]
  have habs : (1 : ℝ) / 12 <
      |(inner ℂ
        ((thetaSourceSignedStageGreenBoundary k + P) pinnedPositiveMode)
        pinnedPositiveMode : ℂ).re| := by
    rw [abs_of_pos (lt_trans (by norm_num) hdiff)]
    exact hdiff
  have hbound :
      |(inner ℂ
        ((thetaSourceSignedStageGreenBoundary k + P) pinnedPositiveMode)
        pinnedPositiveMode : ℂ).re| ≤
        ‖thetaSourceSignedStageGreenBoundary k + P‖ * ‖pinnedPositiveMode‖ ^ (2 : ℕ) := by
    calc
      |_|≤ ‖(inner ℂ
          ((thetaSourceSignedStageGreenBoundary k + P) pinnedPositiveMode)
          pinnedPositiveMode : ℂ)‖ := Complex.abs_re_le_norm _
      _ ≤ ‖(thetaSourceSignedStageGreenBoundary k + P) pinnedPositiveMode‖ *
          ‖pinnedPositiveMode‖ := norm_inner_le_norm _ _
      _ ≤ (‖thetaSourceSignedStageGreenBoundary k + P‖ * ‖pinnedPositiveMode‖) *
          ‖pinnedPositiveMode‖ := by
            exact mul_le_mul_of_nonneg_right
              ((thetaSourceSignedStageGreenBoundary k + P).le_opNorm _)
              (norm_nonneg _)
      _ = ‖thetaSourceSignedStageGreenBoundary k + P‖ *
          ‖pinnedPositiveMode‖ ^ (2 : ℕ) := by ring
  rw [norm_pinnedPositiveMode_sq] at hbound
  nlinarith [norm_nonneg (thetaSourceSignedStageGreenBoundary k + P)]

end

end RHTower.HedenmalmThetaSource
