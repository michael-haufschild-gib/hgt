import Mathlib

/-!
# Smoothness of parametric averages

Averaging a jointly smooth family along the unit interval,

`(A F)(x) = ∫₀¹ F x t dt`,

preserves every finite order of differentiability, and its derivative is the average of the partial
derivatives in the parameter.  The proof differentiates under the integral sign once, bounding the
partial derivative uniformly on a compact ball times the unit interval, and then induces on the
order.
-/

namespace GaloisForLFunctions.HTGeometry.Interfinity

open MeasureTheory Set Filter Topology intervalIntegral

noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Averaging a parametric family along the unit interval. -/
def paramAvg {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → ℝ → G) (x : E) : G :=
  ∫ t in (0 : ℝ)..1, F x t

omit [NormedSpace ℝ E] in
theorem continuous_paramAvg {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : E → ℝ → G} (hF : Continuous (Function.uncurry F)) : Continuous (paramAvg F) :=
  continuous_parametric_intervalIntegral_of_continuous hF continuous_const

/-- Precomposition with the parameter inclusion, as a continuous linear map. -/
def restrictInl (G : Type*) [NormedAddCommGroup G] [NormedSpace ℝ G] :
    ((E × ℝ) →L[ℝ] G) →L[ℝ] (E →L[ℝ] G) :=
  (ContinuousLinearMap.compL ℝ E (E × ℝ) G).flip (ContinuousLinearMap.inl ℝ E ℝ)

@[simp] theorem restrictInl_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : (E × ℝ) →L[ℝ] G) : restrictInl G L = L.comp (ContinuousLinearMap.inl ℝ E ℝ) := rfl

/-- The partial derivative of a parametric family in its parameter. -/
def partialFderiv {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → ℝ → G) (x : E)
    (t : ℝ) : E →L[ℝ] G :=
  restrictInl G (fderiv ℝ (Function.uncurry F) (x, t))

theorem uncurry_partialFderiv {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (F : E → ℝ → G) :
    Function.uncurry (partialFderiv F) =
      fun p => restrictInl G (fderiv ℝ (Function.uncurry F) p) := rfl

theorem hasFDerivAt_partial {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {F : E → ℝ → G}
    (hF : ContDiff ℝ 1 (Function.uncurry F)) (x : E) (t : ℝ) :
    HasFDerivAt (fun y => F y t) (partialFderiv F x t) x := by
  have hin : HasFDerivAt (fun y : E => (y, t)) (ContinuousLinearMap.inl ℝ E ℝ) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
  exact ((hF.differentiable (by norm_num) (x, t)).hasFDerivAt).comp x hin

theorem continuous_partialFderiv {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : E → ℝ → G} (hF : ContDiff ℝ 1 (Function.uncurry F)) :
    Continuous (Function.uncurry (partialFderiv F)) := by
  rw [uncurry_partialFderiv]
  exact (restrictInl G).continuous.comp (hF.continuous_fderiv (by norm_num))

/-- **Differentiating under the integral sign.** -/
theorem hasFDerivAt_paramAvg [FiniteDimensional ℝ E] {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] {F : E → ℝ → G}
    (hF : ContDiff ℝ 1 (Function.uncurry F)) (x : E) :
    HasFDerivAt (paramAvg F) (∫ t in (0 : ℝ)..1, partialFderiv F x t) x := by
  have hcontF : Continuous (Function.uncurry F) := hF.continuous
  have hcontD : Continuous (Function.uncurry (partialFderiv F)) := continuous_partialFderiv hF
  have hcompact : IsCompact (Metric.closedBall x 1 ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_closedBall x 1).prod isCompact_Icc
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hcontD.continuousOn
  have hM0 : 0 ≤ M := by
    have hmem : ((x, (0 : ℝ)) : E × ℝ) ∈ Metric.closedBall x 1 ×ˢ Icc (0 : ℝ) 1 :=
      ⟨Metric.mem_closedBall_self zero_le_one, ⟨le_rfl, zero_le_one⟩⟩
    exact le_trans (norm_nonneg _) (hM _ hmem)
  have hlip : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ uIoc (0 : ℝ) 1 →
      LipschitzOnWith (Real.nnabs M) (fun y : E => F y t) (Metric.ball x 1) := by
    filter_upwards with t ht
    rw [uIoc_of_le zero_le_one] at ht
    refine (convex_ball x 1).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun y _ => (hasFDerivAt_partial hF y t).differentiableAt) fun y hy => ?_
    rw [(hasFDerivAt_partial hF y t).fderiv]
    have hmem : ((y, t) : E × ℝ) ∈ Metric.closedBall x 1 ×ˢ Icc (0 : ℝ) 1 :=
      ⟨Metric.ball_subset_closedBall hy, ⟨ht.1.le, ht.2⟩⟩
    have hb : ‖partialFderiv F y t‖ ≤ M := hM (y, t) hmem
    rw [← NNReal.coe_le_coe]
    simpa [Real.coe_nnabs, abs_of_nonneg hM0] using hb
  have hres := intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip
    (F := F) (F' := partialFderiv F x) (bound := fun _ => M) (s := Metric.ball x 1)
    (Metric.ball_mem_nhds x one_pos)
    (Eventually.of_forall fun y => (hcontF.comp (Continuous.prodMk_right y)).aestronglyMeasurable)
    ((hcontF.comp (Continuous.prodMk_right x)).intervalIntegrable _ _)
    ((hcontD.comp (Continuous.prodMk_right x)).aestronglyMeasurable)
    hlip intervalIntegrable_const
    (by filter_upwards with t _ using hasFDerivAt_partial hF x t)
  exact hres.2

/-- **Parametric averaging preserves smoothness of every finite order.** -/
theorem contDiff_paramAvg [FiniteDimensional ℝ E] (n : ℕ) :
    ∀ {G : Type (max u v)} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      {F : E → ℝ → G}, ContDiff ℝ n (Function.uncurry F) → ContDiff ℝ n (paramAvg F) := by
  induction n with
  | zero =>
      intro G _ _ _ F hF
      have hF0 : ContDiff ℝ (0 : WithTop ℕ∞) (Function.uncurry F) := by exact_mod_cast hF
      have hres : ContDiff ℝ (0 : WithTop ℕ∞) (paramAvg F) :=
        contDiff_zero.2 (continuous_paramAvg (contDiff_zero.1 hF0))
      exact_mod_cast hres
  | succ n ih =>
      intro G _ _ _ F hF
      have hF1 : ContDiff ℝ 1 (Function.uncurry F) :=
        hF.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
      have hderiv : fderiv ℝ (paramAvg F) = paramAvg (partialFderiv F) := by
        funext y
        exact (hasFDerivAt_paramAvg hF1 y).fderiv
      have hFcast : ContDiff ℝ ((n : WithTop ℕ∞) + 1) (Function.uncurry F) := by
        exact_mod_cast hF
      have hD : ContDiff ℝ n (Function.uncurry (partialFderiv F)) := by
        rw [uncurry_partialFderiv]
        exact (restrictInl G).contDiff.comp (hFcast.fderiv_right le_rfl)
      have hmain : ContDiff ℝ ((n : WithTop ℕ∞) + 1) (paramAvg F) := by
        rw [contDiff_succ_iff_fderiv]
        refine ⟨fun y => (hasFDerivAt_paramAvg hF1 y).differentiableAt, ?_, ?_⟩
        · intro hcon
          exact absurd hcon (by simp)
        · rw [hderiv]
          exact ih hD
      exact_mod_cast hmain

end

end GaloisForLFunctions.HTGeometry.Interfinity
