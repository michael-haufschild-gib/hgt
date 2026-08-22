import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62LargeTimeTailTruncation

/-!
# Chen--Gupta--Li Lemma 6.2: finite large-time window bound

On CGL's literal large-time window, the finite reflected critical-line
integral is controlled by `N^(1/2)` times the integral of the exact dual
Dirichlet prefix.  The Mellin factor is absorbed into a closed zeroth-order
Schwartz budget.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- CGL's large-time finite critical-line window is bounded by a closed
Mellin constant times `N^(1/2)` and the literal inverse-character Dirichlet
prefix integral. -/
theorem cglLemma62_largeTime_finiteCritical_window_bound
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) (w : CGLRealSmoothBump) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖∫ u : ℝ in -S.truncationWindow.radius..S.truncationWindow.radius,
          cglLemma62FiniteContourIntegrand w N B t S.tailCutoff.value
            (cglLemma62CriticalPoint u).value‖ ≤
        C * (N.value : ℝ) ^ (1 / 2 : ℝ) *
          ∫ u : ℝ in -S.truncationWindow.radius..S.truncationWindow.radius,
            ‖cglLemma62DirichletHead B.character⁻¹ S.tailCutoff.value
              (1 - (cglLemma62CriticalPoint u).value + (t : ℂ) * I)‖ := by
  let C : ℝ := cglLemma62MellinLineDecayBudget w (1 / 2) 0
  have hC : 0 ≤ C := by
    dsimp [C]
    exact le_trans (by positivity) (cglLemma62_mellinTransform_vertical_rapidDecay
      w (1 / 2) 0 0)
  have hR : 0 ≤ S.truncationWindow.radius := S.truncationWindow.radius_nonneg
  have hab : -S.truncationWindow.radius ≤ S.truncationWindow.radius := by linarith
  have hfinite : Integrable (fun u : ℝ =>
      cglLemma62FiniteContourIntegrand w N B t S.tailCutoff.value
        (cglLemma62CriticalPoint u).value) := by
    simpa [cglLemma62CriticalPoint] using
      cglLemma62_finiteContourIntegrand_right_integrable w N B t S.tailCutoff.value
  have harg : Continuous (fun u : ℝ =>
      1 - (cglLemma62CriticalPoint u).value + (t : ℂ) * I) := by
    unfold cglLemma62CriticalPoint
    fun_prop
  have hhead : Continuous (fun u : ℝ =>
      cglLemma62DirichletHead B.character⁻¹ S.tailCutoff.value
        (1 - (cglLemma62CriticalPoint u).value + (t : ℂ) * I)) :=
    (cglLemma62DirichletHead_differentiable B.character⁻¹ S.tailCutoff.value).continuous.comp harg
  have hfiniteInt : IntervalIntegrable (fun u : ℝ =>
      ‖cglLemma62FiniteContourIntegrand w N B t S.tailCutoff.value
        (cglLemma62CriticalPoint u).value‖) volume
      (-S.truncationWindow.radius) S.truncationWindow.radius := hfinite.norm.intervalIntegrable
  have hmajorInt : IntervalIntegrable (fun u : ℝ =>
      C * (N.value : ℝ) ^ (1 / 2 : ℝ) *
        ‖cglLemma62DirichletHead B.character⁻¹ S.tailCutoff.value
          (1 - (cglLemma62CriticalPoint u).value + (t : ℂ) * I)‖) volume
      (-S.truncationWindow.radius) S.truncationWindow.radius := by
    exact ((continuous_const.mul continuous_const).mul hhead.norm).intervalIntegrable
      (μ := volume) (-S.truncationWindow.radius) S.truncationWindow.radius
  have hpoint : ∀ u ∈ Set.Icc (-S.truncationWindow.radius) S.truncationWindow.radius,
      ‖cglLemma62FiniteContourIntegrand w N B t S.tailCutoff.value
        (cglLemma62CriticalPoint u).value‖ ≤
        C * (N.value : ℝ) ^ (1 / 2 : ℝ) *
          ‖cglLemma62DirichletHead B.character⁻¹ S.tailCutoff.value
            (1 - (cglLemma62CriticalPoint u).value + (t : ℂ) * I)‖ := by
    intro u hu
    have hMellin : ‖cglLemma62MellinTransform w (cglLemma62CriticalPoint u).value‖ ≤ C := by
      dsimp [C]
      simpa [cglLemma62CriticalPoint] using
        cglLemma62_mellinTransform_vertical_rapidDecay w (1 / 2) 0 u
    rw [cglLemma62_finiteCritical_norm_eq]
    gcongr
  refine ⟨C, hC, ?_⟩
  calc
    ‖∫ u : ℝ in -S.truncationWindow.radius..S.truncationWindow.radius,
        cglLemma62FiniteContourIntegrand w N B t S.tailCutoff.value
          (cglLemma62CriticalPoint u).value‖ ≤
      ∫ u : ℝ in -S.truncationWindow.radius..S.truncationWindow.radius,
        ‖cglLemma62FiniteContourIntegrand w N B t S.tailCutoff.value
          (cglLemma62CriticalPoint u).value‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ u : ℝ in -S.truncationWindow.radius..S.truncationWindow.radius,
        C * (N.value : ℝ) ^ (1 / 2 : ℝ) *
          ‖cglLemma62DirichletHead B.character⁻¹ S.tailCutoff.value
            (1 - (cglLemma62CriticalPoint u).value + (t : ℂ) * I)‖ :=
      intervalIntegral.integral_mono_on hab hfiniteInt hmajorInt hpoint
    _ = C * (N.value : ℝ) ^ (1 / 2 : ℝ) *
        ∫ u : ℝ in -S.truncationWindow.radius..S.truncationWindow.radius,
          ‖cglLemma62DirichletHead B.character⁻¹ S.tailCutoff.value
            (1 - (cglLemma62CriticalPoint u).value + (t : ℂ) * I)‖ := by
      rw [intervalIntegral.integral_const_mul]

end

end RHTower
