import GaloisForLFunctions.Bottcher.Montel
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Cauchy-dominated holomorphy under an integral

A local integrable bound on a holomorphic family also bounds its parameter derivative on a
half-sized ball, by Cauchy's estimate.  This turns ordinary domination of the family into the
derivative domination needed to differentiate its Bochner integral.
-/

open Complex Filter MeasureTheory Metric Set Topology

namespace GaloisForLFunctions.HTGeometry

/-- A locally uniformly summably bounded holomorphic family has a holomorphic sum. -/
theorem differentiableAt_tsum_of_cauchy_dominated
    {ι : Type*} {f : ι → ℂ → ℂ} {z₀ : ℂ} {R : ℝ} {bound : ι → ℝ}
    (hR : 0 < R)
    (hdiff : ∀ i : ι, DifferentiableOn ℂ (f i) (ball z₀ R))
    (hbound : ∀ i : ι, ∀ z ∈ ball z₀ R, ‖f i z‖ ≤ bound i)
    (hboundSum : Summable bound) :
    DifferentiableAt ℂ (fun z : ℂ => ∑' i : ι, f i z) z₀ := by
  have hderivBound : ∀ i : ι, ∀ z ∈ ball z₀ (R / 2),
      ‖deriv (f i) z‖ ≤ (2 / R) * bound i := by
    intro i z hz
    have hc := Bottcher.norm_deriv_le_of_bounded_on_ball hR (hdiff i) (hbound i) z hz
    calc
      ‖deriv (f i) z‖ ≤ 2 * bound i / R := hc
      _ = (2 / R) * bound i := by ring
  have hderivSum : Summable (fun i : ι => (2 / R) * bound i) :=
    hboundSum.mul_left (2 / R)
  have hterm : ∀ i : ι, ∀ z ∈ ball z₀ (R / 2),
      HasDerivAt (f i) (deriv (f i) z) z := by
    intro i z hz
    exact ((hdiff i).differentiableAt
      (isOpen_ball.mem_nhds (ball_subset_ball (by linarith) hz))).hasDerivAt
  have hvalueSum : Summable (fun i : ι => f i z₀) := by
    exact Summable.of_norm_bounded hboundSum fun i => hbound i z₀ (mem_ball_self hR)
  have hpre : IsPreconnected (ball z₀ (R / 2)) :=
    (convex_ball z₀ (R / 2)).isPreconnected
  exact (hasDerivAt_tsum_of_isPreconnected hderivSum isOpen_ball hpre
    hterm hderivBound (mem_ball_self (by positivity : 0 < R / 2)) hvalueSum
    (mem_ball_self (by positivity : 0 < R / 2))).differentiableAt

/-- The parameter derivative of a measurable complex family is measurable.  It is the pointwise
limit of measurable difference quotients. -/
theorem aestronglyMeasurable_deriv_param_complex
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℂ → α → ℂ} {z₀ : ℂ} {R : ℝ}
    (hR : 0 < R)
    (hmeas : ∀ z ∈ ball z₀ R, AEStronglyMeasurable (F z) μ)
    (hdiff : ∀ a : α, DifferentiableAt ℂ (fun z : ℂ => F z a) z₀) :
    AEStronglyMeasurable (fun a : α => deriv (fun z : ℂ => F z a) z₀) μ := by
  let q : ℕ → ℂ := fun n => (((R / 2) * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ)
  have hqmem : ∀ n : ℕ, z₀ + q n ∈ ball z₀ R := by
    intro n
    rw [mem_ball, dist_self_add_left, norm_real, Real.norm_of_nonneg]
    · have hone : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        norm_num
      nlinarith
    · positivity
  have hzmem : z₀ ∈ ball z₀ R := mem_ball_self hR
  have hstep : ∀ n : ℕ, AEStronglyMeasurable
      (fun a : α => slope (fun z : ℂ => F z a) z₀ (z₀ + q n)) μ := by
    intro n
    have hfun : (fun a : α => slope (fun z : ℂ => F z a) z₀ (z₀ + q n)) =
        fun a : α => (q n)⁻¹ * (F (z₀ + q n) a - F z₀ a) := by
      funext a
      simp only [slope, vsub_eq_sub, add_sub_cancel_left, smul_eq_mul]
    rw [hfun]
    exact ((hmeas _ (hqmem n)).sub (hmeas _ hzmem)).const_mul _
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop) hstep ?_
  filter_upwards with a
  have hslope := (hdiff a).hasDerivAt.tendsto_slope
  have hreal : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hscaled : Tendsto (fun n : ℕ => (R / 2) * (1 / ((n : ℝ) + 1)))
      atTop (nhds (0 : ℝ)) := by
    simpa using hreal.const_mul (R / 2)
  have hq : Tendsto q atTop (nhds (0 : ℂ)) := by
    exact (Complex.continuous_ofReal.tendsto 0).comp hscaled
  have hbase : Tendsto (fun n : ℕ => z₀ + q n) atTop (nhds z₀) := by
    simpa using hq.const_add z₀
  have hne : ∀ᶠ n : ℕ in atTop, z₀ + q n ∈ ({z₀}ᶜ : Set ℂ) := by
    filter_upwards with n
    have hpos : (0 : ℝ) < (R / 2) * (1 / ((n : ℝ) + 1)) := by positivity
    simp only [mem_compl_iff, mem_singleton_iff]
    intro hcontra
    have hzero : q n = 0 := by
      apply add_left_cancel (a := z₀)
      simpa using hcontra
    have : (R / 2) * (1 / ((n : ℝ) + 1)) = 0 := Complex.ofReal_injective hzero
    linarith
  exact hslope.comp
    (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hbase hne)

/-- A locally uniformly bounded holomorphic family has a holomorphic Bochner integral.  Unlike the
standard dominated-derivative theorem, callers only supply a bound for the family itself. -/
theorem differentiableAt_integral_of_cauchy_dominated
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℂ → α → ℂ} {z₀ : ℂ} {R : ℝ} {bound : α → ℝ}
    (hR : 0 < R)
    (hmeas : ∀ z ∈ ball z₀ R, AEStronglyMeasurable (F z) μ)
    (hdiff : ∀ a : α, DifferentiableOn ℂ (fun z : ℂ => F z a) (ball z₀ R))
    (hbound : ∀ a : α, ∀ z ∈ ball z₀ R, ‖F z a‖ ≤ bound a)
    (hboundInt : Integrable bound μ) :
    DifferentiableAt ℂ (fun z : ℂ => ∫ a : α, F z a ∂μ) z₀ := by
  have hzmem : z₀ ∈ ball z₀ R := mem_ball_self hR
  have hFint : Integrable (F z₀) μ := by
    exact Integrable.mono' hboundInt (hmeas z₀ hzmem)
      (Filter.Eventually.of_forall fun a => hbound a z₀ hzmem)
  have hderivMeas : AEStronglyMeasurable
      (fun a : α => deriv (fun z : ℂ => F z a) z₀) μ :=
    aestronglyMeasurable_deriv_param_complex hR hmeas
      (fun a => (hdiff a).differentiableAt (isOpen_ball.mem_nhds hzmem))
  have hderivBound : ∀ a : α, ∀ z ∈ ball z₀ (R / 2),
      ‖deriv (fun w : ℂ => F w a) z‖ ≤ (2 / R) * bound a := by
    intro a z hz
    have hc := Bottcher.norm_deriv_le_of_bounded_on_ball hR (hdiff a) (hbound a) z hz
    calc
      ‖deriv (fun w : ℂ => F w a) z‖ ≤ 2 * bound a / R := hc
      _ = (2 / R) * bound a := by ring
  have hboundInt' : Integrable (fun a => (2 / R) * bound a) μ :=
    hboundInt.const_mul (2 / R)
  have hdiff' : ∀ᵐ a : α ∂μ, ∀ z ∈ ball z₀ (R / 2),
      HasDerivAt (fun w : ℂ => F w a) (deriv (fun w : ℂ => F w a) z) z := by
    filter_upwards with a
    intro z hz
    exact ((hdiff a).differentiableAt
      (isOpen_ball.mem_nhds (ball_subset_ball (by linarith) hz))).hasDerivAt
  have hFmeas : ∀ᶠ z : ℂ in nhds z₀, AEStronglyMeasurable (F z) μ := by
    filter_upwards [ball_mem_nhds z₀ (by positivity : 0 < R / 2)] with z hz
    exact hmeas z (ball_subset_ball (by linarith) hz)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F)
    (F' := fun z a => deriv (fun w : ℂ => F w a) z)
    (bound := fun a => (2 / R) * bound a)
    (ball_mem_nhds z₀ (by positivity : 0 < R / 2))
    hFmeas hFint hderivMeas
    (Filter.Eventually.of_forall fun a z hz => hderivBound a z hz)
    hboundInt' hdiff').2.differentiableAt

end GaloisForLFunctions.HTGeometry
