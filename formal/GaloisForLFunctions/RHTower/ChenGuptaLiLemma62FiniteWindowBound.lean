import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62FiniteTailTruncation

/-!
# Chen--Gupta--Li Lemma 6.2: finite small-time window bound

On CGL's literal small-time window, the finite reflected critical-line
integral is controlled by `N^(1/2)` times the integral of the exact dual
Dirichlet prefix.  The Mellin factor is absorbed into a closed zeroth-order
Schwartz budget.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- CGL's small-time finite critical-line window is bounded by a closed
Mellin constant times `N^(1/2)` and the literal inverse-character Dirichlet
prefix integral. -/
theorem cglLemma62_smallTime_finiteCritical_window_bound
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62SmallTimeSourceRegime B N t) (w : CGLRealSmoothBump) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖∫ u : ℝ in -S.truncationRadius..S.truncationRadius,
          cglLemma62FiniteContourIntegrand w N B t S.tailCutoff.value
            (cglLemma62CriticalPoint u).value‖ ≤
        C * (N.value : ℝ) ^ (1 / 2 : ℝ) *
          ∫ u : ℝ in -S.truncationRadius..S.truncationRadius,
            ‖cglLemma62DirichletHead B.character⁻¹ S.tailCutoff.value
              (1 - (cglLemma62CriticalPoint u).value + (t : ℂ) * I)‖ := by
  let C : ℝ := cglLemma62MellinLineDecayBudget w (1 / 2) 0
  have hC : 0 ≤ C := by
    dsimp [C]
    exact le_trans (by positivity) (cglLemma62_mellinTransform_vertical_rapidDecay
      w (1 / 2) 0 0)
  have hR : 0 ≤ S.truncationRadius := by
    unfold CGLLemma62SmallTimeSourceRegime.truncationRadius
    exact Real.rpow_nonneg (le_trans zero_le_one S.base_one) _
  have hab : -S.truncationRadius ≤ S.truncationRadius := by linarith
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
      (-S.truncationRadius) S.truncationRadius := hfinite.norm.intervalIntegrable
  have hmajorInt : IntervalIntegrable (fun u : ℝ =>
      C * (N.value : ℝ) ^ (1 / 2 : ℝ) *
        ‖cglLemma62DirichletHead B.character⁻¹ S.tailCutoff.value
          (1 - (cglLemma62CriticalPoint u).value + (t : ℂ) * I)‖) volume
      (-S.truncationRadius) S.truncationRadius := by
    exact ((continuous_const.mul continuous_const).mul hhead.norm).intervalIntegrable
      (μ := volume) (-S.truncationRadius) S.truncationRadius
  have hpoint : ∀ u ∈ Set.Icc (-S.truncationRadius) S.truncationRadius,
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
    ‖∫ u : ℝ in -S.truncationRadius..S.truncationRadius,
        cglLemma62FiniteContourIntegrand w N B t S.tailCutoff.value
          (cglLemma62CriticalPoint u).value‖ ≤
      ∫ u : ℝ in -S.truncationRadius..S.truncationRadius,
        ‖cglLemma62FiniteContourIntegrand w N B t S.tailCutoff.value
          (cglLemma62CriticalPoint u).value‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ u : ℝ in -S.truncationRadius..S.truncationRadius,
        C * (N.value : ℝ) ^ (1 / 2 : ℝ) *
          ‖cglLemma62DirichletHead B.character⁻¹ S.tailCutoff.value
            (1 - (cglLemma62CriticalPoint u).value + (t : ℂ) * I)‖ :=
      intervalIntegral.integral_mono_on hab hfiniteInt hmajorInt hpoint
    _ = C * (N.value : ℝ) ^ (1 / 2 : ℝ) *
        ∫ u : ℝ in -S.truncationRadius..S.truncationRadius,
          ‖cglLemma62DirichletHead B.character⁻¹ S.tailCutoff.value
            (1 - (cglLemma62CriticalPoint u).value + (t : ℂ) * I)‖ := by
      rw [intervalIntegral.integral_const_mul]

end

end RHTower
