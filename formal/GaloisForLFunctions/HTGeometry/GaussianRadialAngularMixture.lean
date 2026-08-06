import GaloisForLFunctions.HTGeometry.ReplicaReporterSpectralExpansion

/-!
# Angular mixture of the radial observer--spectral action

The radial action kernel is a contraction and depends continuously on the
action, so a direction-indexed family of spectral packets may be averaged over
the direction law and the observation-time limit taken inside the average by
dominated convergence.  The limit is the direction average of the zero-action
sectors: the angular mixture of the completed spectral-orbit laws.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The radial action kernel is a contraction. -/
theorem norm_radialActionKernel_le_one {m : ℕ} (hm : 0 < m) (u : ℝ) :
    ‖radialActionKernel m u‖ ≤ 1 := by
  rw [radialActionKernel_eq_integral_stdGaussian hm]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hnorm : ∀ x : EuclideanSpace ℝ (Fin m),
      ‖Complex.exp (-((u * ‖x‖ : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    intro x
    rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
  rw [funext hnorm]
  simp

/-- The radial action kernel depends continuously on the action. -/
theorem continuous_radialActionKernel {m : ℕ} (hm : 0 < m) :
    Continuous (radialActionKernel m) := by
  have hfun : radialActionKernel m
      = fun w : ℝ => ∫ x, Complex.exp (-((w * ‖x‖ : ℝ) : ℂ) * Complex.I)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin m))) :=
    funext fun w => radialActionKernel_eq_integral_stdGaussian hm w
  rw [continuous_iff_continuousAt]
  intro u
  rw [ContinuousAt, hfun]
  refine tendsto_integral_filter_of_dominated_convergence
    (μ := stdGaussian (EuclideanSpace ℝ (Fin m))) (l := 𝓝 u)
    (F := fun (w : ℝ) (x : EuclideanSpace ℝ (Fin m)) =>
      Complex.exp (-((w * ‖x‖ : ℝ) : ℂ) * Complex.I))
    (f := fun x : EuclideanSpace ℝ (Fin m) =>
      Complex.exp (-((u * ‖x‖ : ℝ) : ℂ) * Complex.I))
    (fun _ => (1 : ℝ)) ?_ ?_
    (integrable_const (μ := stdGaussian (EuclideanSpace ℝ (Fin m))) (1 : ℝ)) ?_
  · filter_upwards with w
    exact (Measurable.aestronglyMeasurable (by fun_prop))
  · filter_upwards with w
    filter_upwards with x
    rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
  · filter_upwards with x
    exact ((Complex.continuous_exp.comp (by fun_prop)).tendsto u)

/-- **Angular mixture with dominated convergence.**  Averaging one spectral
character over a direction law converges to the average of its zero-action
value. -/
theorem tendsto_integral_angularMixture {Ω : Type*} [MeasurableSpace Ω]
    (σμ : Measure Ω) {m : ℕ} (hm : 0 < m) (c : Ω → ℂ) (d : Ω → ℝ)
    (hc : Integrable c σμ) (hd : Measurable d)
    [DecidablePred fun ω => d ω = 0] :
    Tendsto (fun t : ℝ => ∫ ω, c ω * radialActionKernel m (t * d ω) ∂σμ)
      atTop (𝓝 (∫ ω, (if d ω = 0 then c ω else 0) ∂σμ)) := by
  classical
  refine tendsto_integral_filter_of_dominated_convergence (fun ω => ‖c ω‖) ?_ ?_
    hc.norm ?_
  · filter_upwards with t
    refine hc.aestronglyMeasurable.mul ?_
    exact ((continuous_radialActionKernel hm).measurable.comp
      (measurable_const.mul hd)).aestronglyMeasurable
  · filter_upwards with t
    filter_upwards with ω
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_radialActionKernel_le_one hm _)
  · filter_upwards with ω
    by_cases hω : d ω = 0
    · rw [if_pos hω]
      have hconst : ∀ t : ℝ, c ω * radialActionKernel m (t * d ω) = c ω := by
        intro t
        rw [hω, mul_zero, radialActionKernel_zero hm, mul_one]
      exact Tendsto.congr (fun t => (hconst t).symm) tendsto_const_nhds
    · rw [if_neg hω]
      simpa using (tendsto_radialActionKernel_atTop (m := m) hω).const_mul (c ω)

variable {D k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Angular mixture of the observer--spectral action law.**  For a
direction-indexed family of spectral data, the direction average of the Gaussian
radial observation converges to the direction average of the completed-orbit
zero-action sectors. -/
theorem tendsto_integral_replicaReporter_angularMixture
    {Ω : Type*} [MeasurableSpace Ω] (σμ : Measure Ω) {m : ℕ} (hm : 0 < m)
    (A : Ω → Matrix (Fin k → Fin D) (Fin k → Fin D) ℂ)
    (v : Ω → ι → (Fin D → ℂ)) (α : Ω → ι → ℂ) (E : Ω → ι → ℝ)
    (hcoeff : ∀ p : Fin k → ι × ι,
      Integrable (fun ω => replicaCoefficient (A ω) (v ω) (α ω) p) σμ)
    (hdetuning : ∀ p : Fin k → ι × ι,
      Measurable fun ω => replicaDetuning (E ω) p) :
    Tendsto
      (fun time : ℝ =>
        ∫ ω, (∑ p : Fin k → ι × ι,
          replicaCoefficient (A ω) (v ω) (α ω) p *
            radialActionKernel m (time * replicaDetuning (E ω) p)) ∂σμ)
      atTop
      (𝓝 (∫ ω, (∑ p : Fin k → ι × ι,
        if replicaDetuning (E ω) p = 0 then
          replicaCoefficient (A ω) (v ω) (α ω) p else 0) ∂σμ)) := by
  classical
  have hsplit : ∀ time : ℝ,
      (∫ ω, (∑ p : Fin k → ι × ι,
        replicaCoefficient (A ω) (v ω) (α ω) p *
          radialActionKernel m (time * replicaDetuning (E ω) p)) ∂σμ)
        = ∑ p : Fin k → ι × ι,
          ∫ ω, replicaCoefficient (A ω) (v ω) (α ω) p *
            radialActionKernel m (time * replicaDetuning (E ω) p) ∂σμ := by
    intro time
    refine integral_finsetSum _ fun p _ => ?_
    refine Integrable.mono' ((hcoeff p).norm) ?_ ?_
    · refine (hcoeff p).aestronglyMeasurable.mul ?_
      exact ((continuous_radialActionKernel hm).measurable.comp
        (measurable_const.mul (hdetuning p))).aestronglyMeasurable
    · filter_upwards with ω
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (norm_radialActionKernel_le_one hm _)
  have hlimitSum : (∫ ω, (∑ p : Fin k → ι × ι,
        if replicaDetuning (E ω) p = 0 then
          replicaCoefficient (A ω) (v ω) (α ω) p else 0) ∂σμ)
      = ∑ p : Fin k → ι × ι,
        ∫ ω, (if replicaDetuning (E ω) p = 0 then
          replicaCoefficient (A ω) (v ω) (α ω) p else 0) ∂σμ := by
    refine integral_finsetSum _ fun p _ => ?_
    have hset : MeasurableSet {ω | replicaDetuning (E ω) p = 0} :=
      measurableSet_eq_fun (hdetuning p) measurable_const
    have hfun : (fun ω => if replicaDetuning (E ω) p = 0 then
        replicaCoefficient (A ω) (v ω) (α ω) p else 0)
        = {ω | replicaDetuning (E ω) p = 0}.indicator
            (fun ω => replicaCoefficient (A ω) (v ω) (α ω) p) := by
      funext ω
      by_cases hω : replicaDetuning (E ω) p = 0 <;> simp [hω]
    rw [hfun]
    exact (hcoeff p).indicator hset
  rw [hlimitSum]
  refine Tendsto.congr (fun time => (hsplit time).symm) ?_
  refine tendsto_finsetSum _ fun p _ => ?_
  exact tendsto_integral_angularMixture σμ hm _ _ (hcoeff p) (hdetuning p)

end

end GaloisForLFunctions.HTGeometry
