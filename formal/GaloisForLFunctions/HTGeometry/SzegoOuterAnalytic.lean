import GaloisForLFunctions.HTGeometry.SzegoOuterFunction
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
open MeasureTheory intervalIntegral Complex Metric Filter Topology
open scoped Real

namespace GaloisForLFunctions.HTGeometry

/-- `log w` coerced to `ℂ` is interval integrable. -/
theorem intervalIntegrable_logC {w : ℝ → ℝ}
    (hlog : IntervalIntegrable (fun θ => Real.log (w θ)) volume 0 (2 * π)) :
    IntervalIntegrable (fun θ => (Real.log (w θ) : ℂ)) volume 0 (2 * π) := by
  constructor <;>
  · apply MeasureTheory.Integrable.ofReal
    first | exact hlog.1 | exact hlog.2

/-- The Szegő exponent `∫₀²π -k(z) log w dθ` is complex-differentiable at every interior point, with
derivative obtained by differentiating the kernel under the integral sign. -/
theorem hasDerivAt_szegoExponent {w : ℝ → ℝ}
    (hlog : IntervalIntegrable (fun θ => Real.log (w θ)) volume 0 (2 * π))
    {z₀ : ℂ} (hz₀ : ‖z₀‖ < 1) :
    HasDerivAt (fun z => ∫ θ in (0:ℝ)..(2 * π),
        -herglotzRieszKernel 0 (circleMap 0 1 θ) z * (Real.log (w θ) : ℂ))
      (∫ θ in (0:ℝ)..(2 * π),
        2 * circleMap 0 1 θ / (z₀ - circleMap 0 1 θ) ^ 2 * (Real.log (w θ) : ℂ)) z₀ := by
  obtain ⟨r, hz₀r, hr1⟩ := exists_between hz₀
  have hr0 : (0:ℝ) ≤ r := le_trans (norm_nonneg z₀) hz₀r.le
  have hlogC := intervalIntegrable_logC hlog
  have hlogAESM : AEStronglyMeasurable (fun θ => (Real.log (w θ) : ℂ))
      (volume.restrict (Set.uIoc 0 (2 * π))) := by
    rw [Set.uIoc_of_le (by positivity)]; exact hlogC.1.aestronglyMeasurable
  have hanorm : ∀ θ : ℝ, ‖circleMap 0 1 θ‖ = 1 := fun θ => by rw [norm_circleMap_zero]; norm_num
  have hne : ∀ θ : ℝ, ∀ z : ℂ, ‖z‖ < 1 → z ≠ circleMap 0 1 θ := by
    intro θ z hz hcontra; rw [hcontra, hanorm] at hz; linarith
  -- continuity of the kernel and its derivative in `θ`
  have hcontK : ∀ z : ℂ, ‖z‖ < 1 →
      Continuous (fun θ : ℝ => -herglotzRieszKernel 0 (circleMap 0 1 θ) z) := by
    intro z hz
    simp only [herglotzRieszKernel_def, sub_zero]
    exact (Continuous.div (by fun_prop) (by fun_prop)
      (fun θ => sub_ne_zero.mpr (hne θ z hz))).neg
  have hcontK' : ∀ z : ℂ, ‖z‖ < 1 →
      Continuous (fun θ : ℝ => 2 * circleMap 0 1 θ / (z - circleMap 0 1 θ) ^ 2) := by
    intro z hz
    exact Continuous.div (by fun_prop) (by fun_prop)
      (fun θ => pow_ne_zero 2 (sub_ne_zero.mpr (hne θ z hz)))
  set F : ℂ → ℝ → ℂ := fun z θ =>
    -herglotzRieszKernel 0 (circleMap 0 1 θ) z * (Real.log (w θ) : ℂ) with hF
  set F' : ℂ → ℝ → ℂ := fun z θ =>
    2 * circleMap 0 1 θ / (z - circleMap 0 1 θ) ^ 2 * (Real.log (w θ) : ℂ) with hF'
  set bnd : ℝ → ℝ := fun θ => 2 / (1 - r) ^ 2 * ‖(Real.log (w θ) : ℂ)‖ with hbnd
  have hFint : ∀ z : ℂ, ‖z‖ < 1 → IntervalIntegrable (F z) volume 0 (2 * π) := fun z hz =>
    hlogC.continuousOn_mul (hcontK z hz).continuousOn
  have hF'meas : AEStronglyMeasurable (F' z₀) (volume.restrict (Set.uIoc 0 (2 * π))) :=
    ((hcontK' z₀ hz₀).aestronglyMeasurable).mul hlogAESM
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (bound := bnd) (F := F) (F' := F')
      (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz₀r)) ?_ (hFint z₀ hz₀) hF'meas ?_
      ?_ ?_).2
  · exact Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz₀r))
      (fun z hz => ((hcontK z (lt_trans (mem_ball_zero_iff.mp hz) hr1)).aestronglyMeasurable).mul
        hlogAESM)
  · refine Filter.Eventually.of_forall (fun θ _ z hz => ?_)
    have hzr : ‖z‖ ≤ r := (mem_ball_zero_iff.mp hz).le
    have hz1 : ‖z‖ < 1 := lt_trans (mem_ball_zero_iff.mp hz) hr1
    rw [hF', norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact norm_deriv_herglotz_bound (circleMap 0 1 θ) z (hanorm θ) hr1 hzr
  · exact hlogC.norm.const_mul (2 / (1 - r) ^ 2)
  · refine Filter.Eventually.of_forall (fun θ _ z hz => ?_)
    have hz1 : ‖z‖ < 1 := lt_trans (mem_ball_zero_iff.mp hz) hr1
    exact (hasDerivAt_neg_herglotz (circleMap 0 1 θ) z (hne θ z hz1)).mul_const _

/-- The Szegő outer function is complex-differentiable at every interior point of the disk. -/
theorem hasDerivAt_szegoOuter {w : ℝ → ℝ}
    (hlog : IntervalIntegrable (fun θ => Real.log (w θ)) volume 0 (2 * π))
    {z₀ : ℂ} (hz₀ : ‖z₀‖ < 1) :
    HasDerivAt (szegoOuter w)
      (szegoOuter w z₀ * ((1 / (4 * π) : ℂ) * ∫ θ in (0:ℝ)..(2 * π),
        2 * circleMap 0 1 θ / (z₀ - circleMap 0 1 θ) ^ 2 * (Real.log (w θ) : ℂ))) z₀ := by
  have hH := (hasDerivAt_szegoExponent hlog hz₀).const_mul (1 / (4 * π) : ℂ)
  simpa only [szegoOuter] using! hH.cexp

/-- The Szegő outer function is analytic on the open unit disk. -/
theorem analyticOnNhd_szegoOuter {w : ℝ → ℝ}
    (hlog : IntervalIntegrable (fun θ => Real.log (w θ)) volume 0 (2 * π)) :
    AnalyticOnNhd ℂ (szegoOuter w) (ball 0 1) := by
  have hdiff : DifferentiableOn ℂ (szegoOuter w) (ball 0 1) := by
    intro z hz
    have hd := hasDerivAt_szegoOuter hlog (mem_ball_zero_iff.mp hz)
    exact hd.differentiableAt.differentiableWithinAt
  exact DifferentiableOn.analyticOnNhd hdiff isOpen_ball

/-- The reciprocal outer function `1/D` is analytic on the open unit disk (`D` is analytic and
nowhere zero).  Its Taylor coefficients are the `bₖ` whose square-summability is `1/D ∈ H²`. -/
theorem analyticOnNhd_inv_szegoOuter {w : ℝ → ℝ}
    (hlog : IntervalIntegrable (fun θ => Real.log (w θ)) volume 0 (2 * π)) :
    AnalyticOnNhd ℂ (fun z => (szegoOuter w z)⁻¹) (ball 0 1) :=
  (analyticOnNhd_szegoOuter hlog).fun_inv (fun z _ => szegoOuter_ne_zero w z)


/-- The reciprocal outer function `1/D` has a convergent power series (Taylor series) on every
closed sub-disk of the unit disk.  Its coefficients `cauchyPowerSeries` are the `bₖ` whose
square-summability is `1/D ∈ H²`. -/
theorem hasFPowerSeriesOnBall_inv_szegoOuter {w : ℝ → ℝ}
    (hlog : IntervalIntegrable (fun θ => Real.log (w θ)) volume 0 (2 * π))
    {R : NNReal} (hR0 : 0 < R) (hR1 : (R : ℝ) < 1) :
    HasFPowerSeriesOnBall (fun z => (szegoOuter w z)⁻¹)
      (cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R) 0 R :=
  DifferentiableOn.hasFPowerSeriesOnBall
    ((analyticOnNhd_inv_szegoOuter hlog).differentiableOn.mono
      (Metric.closedBall_subset_ball hR1)) hR0


/-- Uniform convergence of the Taylor partial sums of `1/D` composed with the circle
parametrisation: `θ ↦ Sₙ(r e^{iθ}) → θ ↦ 1/D(r e^{iθ})` uniformly, for `r` inside the disk of
convergence. -/
theorem tendstoUniformlyOn_partialSum_inv_szegoOuter_circleMap {w : ℝ → ℝ}
    (hlog : IntervalIntegrable (fun θ => Real.log (w θ)) volume 0 (2 * π))
    {R : NNReal} (hR0 : 0 < R) (hR1 : (R : ℝ) < 1)
    {r : ℝ} (hr0 : 0 ≤ r) {r' : NNReal} (hrr' : r < (r' : ℝ)) (hr'R : r' < R) :
    TendstoUniformlyOn
      (fun n θ => (cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R).partialSum n
          (circleMap 0 r θ))
      (fun θ => (szegoOuter w (circleMap 0 r θ))⁻¹) atTop Set.univ := by
  have hp := hasFPowerSeriesOnBall_inv_szegoOuter hlog hR0 hR1
  have hunif := hp.tendstoUniformlyOn (r' := r') (by exact_mod_cast hr'R)
  have hcomp := hunif.comp (circleMap 0 r)
  have hset : (circleMap 0 r) ⁻¹' (Metric.ball 0 (r' : ℝ)) = Set.univ := by
    ext θ
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, norm_circleMap_zero,
      abs_of_nonneg hr0, Set.mem_univ, iff_true]
    exact hrr'
  rw [hset] at hcomp
  refine hcomp.congr_right ?_
  intro θ _
  simp [Function.comp, zero_add]


end GaloisForLFunctions.HTGeometry
