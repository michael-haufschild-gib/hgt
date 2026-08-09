import GaloisForLFunctions.HTGeometry.CircleIntegralParam

/-!
# Holomorphy of a circle integral in a parameter, over an arbitrary open set

The product-domain hypothesis is inessential: all that a circle integral needs in order to be
holomorphic in the remaining variables is that the whole circle, for each nearby parameter, stays
inside one open set on which the integrand is holomorphic.  This is the form required when the
integrand is a logarithmic derivative, whose domain is the complement of a zero set and is never a
product.

* `HTGeometry.differentiableAt_circleIntegral_slice_open`.
-/

namespace HTGeometry

open Complex MeasureTheory GaloisForLFunctions.HTGeometry
open scoped Real

variable {n : ℕ}

/-- **A circle integral of a slice is holomorphic in the remaining variables**, for any open set
carrying the integrand.  The derivative is taken under the integral sign, dominated by the bound
obtained from continuity of the differential on the compact product of the circle with a closed
ball of parameters. -/
theorem differentiableAt_circleIntegral_slice_open
    {f : (Fin (n + 1) → ℂ) → ℂ} {U : Set (Fin (n + 1) → ℂ)} {V : Set (Fin n → ℂ)}
    (hUopen : IsOpen U) (hVopen : IsOpen V) (hf : DifferentiableOn ℂ f U)
    {t : ℝ} (ht : 0 < t)
    (g : ℂ → ℂ) (hg : Continuous fun θ : ℝ => g (circleMap 0 t θ))
    (hmemU : ∀ (θ : ℝ) (y : Fin n → ℂ), y ∈ V →
      (Fin.cons (circleMap 0 t θ) y : Fin (n + 1) → ℂ) ∈ U)
    {y₀ : Fin n → ℂ} (hy₀ : y₀ ∈ V) :
    DifferentiableAt ℂ (fun y : Fin n → ℂ => ∮ ζ in C(0, t), g ζ • f (Fin.cons ζ y)) y₀ := by
  classical
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.isOpen_iff.1 hVopen y₀ hy₀
  set δ' : ℝ := δ / 2 with hδ'
  have hδ'pos : 0 < δ' := by rw [hδ']; linarith
  have hclosedsub : Metric.closedBall y₀ δ' ⊆ V := by
    refine subset_trans (Metric.closedBall_subset_ball ?_) hδsub
    rw [hδ']
    linarith
  -- the differential of the slice
  set A : ℝ → (Fin n → ℂ) → ((Fin n → ℂ) →L[ℂ] ℂ) := fun θ y =>
    (fderiv ℂ f (Fin.cons (circleMap 0 t θ) y)).comp consLin with hA
  have hslicederiv : ∀ (θ : ℝ) (y : Fin n → ℂ), y ∈ V →
      HasFDerivAt (fun w : Fin n → ℂ => f (Fin.cons (circleMap 0 t θ) w)) (A θ y) y := by
    intro θ y hy
    have hfat : DifferentiableAt ℂ f (Fin.cons (circleMap 0 t θ) y) :=
      hf.differentiableAt (hUopen.mem_nhds (hmemU θ y hy))
    exact hfat.hasFDerivAt.comp y (hasFDerivAt_consMap _ y)
  -- boundedness of the differential on the compact product
  set K : Set (ℝ × (Fin n → ℂ)) := Set.Icc 0 (2 * Real.pi) ×ˢ Metric.closedBall y₀ δ' with hK
  have hKcomp : IsCompact K := isCompact_Icc.prod (isCompact_closedBall y₀ δ')
  have hcontA : ContinuousOn (fun p : ℝ × (Fin n → ℂ) => A p.1 p.2) K := by
    refine ContinuousOn.comp (g := fun q : (Fin (n + 1) → ℂ) => fderiv ℂ f q)
      (continuousOn_fderiv_of_differentiableOn hUopen hf) ?_ ?_ |>.clm_comp continuousOn_const
    · refine Continuous.continuousOn ?_
      refine continuous_pi fun i => ?_
      induction i using Fin.cases with
      | zero =>
          simp only [Fin.cons_zero]
          exact (continuous_circleMap 0 t).comp continuous_fst
      | succ j =>
          simp only [Fin.cons_succ]
          exact (continuous_apply j).comp continuous_snd
    · intro p hp
      exact hmemU p.1 p.2 (hclosedsub hp.2)
  obtain ⟨C, hC⟩ := hKcomp.exists_bound_of_continuousOn hcontA
  have hKmem : ((0 : ℝ), y₀) ∈ K :=
    ⟨⟨le_rfl, by positivity⟩, Metric.mem_closedBall_self hδ'pos.le⟩
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC _ hKmem)
  obtain ⟨Cg, hCg⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 2 * Real.pi)).exists_bound_of_continuousOn
    (hg.continuousOn)
  have hCgnn : 0 ≤ Cg :=
    le_trans (norm_nonneg _) (hCg 0 ⟨le_rfl, by positivity⟩)
  have hderivc : Continuous fun θ : ℝ => deriv (circleMap 0 t) θ := by
    simp only [deriv_circleMap]
    exact (continuous_circleMap 0 t).mul continuous_const
  have hconsC : ∀ y : Fin n → ℂ, Continuous fun θ : ℝ =>
      (Fin.cons (circleMap 0 t θ) y : Fin (n + 1) → ℂ) := by
    intro y
    refine continuous_pi fun i => ?_
    induction i using Fin.cases with
    | zero => simpa using continuous_circleMap 0 t
    | succ j => simpa using continuous_const
  set P : (Fin n → ℂ) → ℝ → ℂ := fun y θ =>
    deriv (circleMap 0 t) θ • (g (circleMap 0 t θ) • f (Fin.cons (circleMap 0 t θ) y)) with hP
  set P' : (Fin n → ℂ) → ℝ → ((Fin n → ℂ) →L[ℂ] ℂ) := fun y θ =>
    (deriv (circleMap 0 t) θ * g (circleMap 0 t θ)) • A θ y with hP'
  have hgoal : (fun y : Fin n → ℂ => ∮ ζ in C(0, t), g ζ • f (Fin.cons ζ y))
      = fun y : Fin n → ℂ => ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), P y θ := by
    funext y
    exact circleIntegral_def_Icc _ 0 t
  rw [hgoal]
  have hcontP : ∀ y : Fin n → ℂ, y ∈ V → Continuous fun θ : ℝ => P y θ := by
    intro y hy
    simp only [hP]
    refine hderivc.smul (Continuous.smul hg ?_)
    exact hf.continuousOn.comp_continuous (hconsC y) fun θ => hmemU θ y hy
  have hcontA' : ContinuousOn (fun θ : ℝ => A θ y₀) (Set.Icc (0 : ℝ) (2 * Real.pi)) := by
    refine ContinuousOn.comp (g := fun p : ℝ × (Fin n → ℂ) => A p.1 p.2) hcontA
      (f := fun θ : ℝ => (θ, y₀)) (Continuous.continuousOn (by fun_prop)) ?_
    intro θ hθ
    exact ⟨hθ, Metric.mem_closedBall_self hδ'pos.le⟩
  have hcontP' : ContinuousOn (fun θ : ℝ => P' y₀ θ) (Set.Icc (0 : ℝ) (2 * Real.pi)) := by
    simp only [hP']
    exact ContinuousOn.smul ((hderivc.mul hg).continuousOn) hcontA'
  have hmeasP : ∀ y : Fin n → ℂ, y ∈ V →
      AEStronglyMeasurable (fun θ : ℝ => P y θ) (volume.restrict (Set.Icc (0:ℝ) (2 * Real.pi))) :=
    fun y hy => (hcontP y hy).aestronglyMeasurable.restrict
  have hbound : ∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), ∀ y ∈ Metric.ball y₀ δ',
      ‖P' y θ‖ ≤ t * Cg * C := by
    intro θ hθ y hy
    have h1 : ‖deriv (circleMap 0 t) θ‖ = t := by
      rw [deriv_circleMap, norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero,
        abs_of_pos ht]
    have h2 : ‖g (circleMap 0 t θ)‖ ≤ Cg := hCg θ hθ
    have h3 : ‖A θ y‖ ≤ C := hC (θ, y) ⟨hθ, Metric.ball_subset_closedBall hy⟩
    have h4 : ‖P' y θ‖ = ‖deriv (circleMap 0 t) θ‖ * ‖g (circleMap 0 t θ)‖ * ‖A θ y‖ := by
      simp only [hP', norm_smul, norm_mul]
    rw [h4, h1]
    have h5 : t * ‖g (circleMap 0 t θ)‖ ≤ t * Cg := mul_le_mul_of_nonneg_left h2 ht.le
    exact mul_le_mul h5 h3 (norm_nonneg _) (by positivity)
  have hderivP : ∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), ∀ y ∈ Metric.ball y₀ δ',
      HasFDerivAt (fun w : Fin n → ℂ => P w θ) (P' y θ) y := by
    intro θ _ y hy
    have hyV : y ∈ V := hclosedsub (Metric.ball_subset_closedBall hy)
    have hbase := (hslicederiv θ y hyV).const_smul
      (deriv (circleMap 0 t) θ * g (circleMap 0 t θ))
    have heqf : ((deriv (circleMap 0 t) θ * g (circleMap 0 t θ)) •
        fun w : Fin n → ℂ => f (Fin.cons (circleMap 0 t θ) w))
        = fun w : Fin n → ℂ => P w θ := by
      funext w
      simp only [hP, Pi.smul_apply, smul_smul]
    rw [heqf] at hbase
    exact hbase
  refine (hasFDerivAt_integral_of_dominated_of_fderiv_le (F := P) (F' := P')
    (bound := fun _ => t * Cg * C) (x₀ := y₀) (s := Metric.ball y₀ δ')
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ'pos))
    (Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ'pos))
      fun y hy => hmeasP y (hclosedsub (Metric.ball_subset_closedBall hy)))
    ((hcontP y₀ hy₀).integrableOn_Icc)
    (hcontP'.aestronglyMeasurable measurableSet_Icc)
    ((ae_restrict_iff' measurableSet_Icc).2
      (Filter.Eventually.of_forall fun θ hθ y hy => hbound θ hθ y hy))
    (continuous_const.integrableOn_Icc (a := (0:ℝ)) (b := 2 * Real.pi))
    ((ae_restrict_iff' measurableSet_Icc).2
      (Filter.Eventually.of_forall fun θ hθ y hy => hderivP θ hθ y hy))).differentiableAt

end HTGeometry
