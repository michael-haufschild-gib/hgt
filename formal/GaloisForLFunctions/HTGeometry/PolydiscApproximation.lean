import GaloisForLFunctions.HTGeometry.PolydiscAnalytic
import GaloisForLFunctions.HTGeometry.PolydiscCauchyLocal
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

/-!
# Local power series and approximation by entire functions on a polydisc

A function that is continuous everywhere and holomorphic on a polydisc has its Cauchy power series
on every strictly smaller polydisc: the only analytic input of the power series construction is the
Cauchy integral formula on the distinguished boundary, and that is available from holomorphy on the
polydisc alone.

The partial sums of a formal multilinear series are entire, and they converge uniformly on every
strictly smaller ball.  So a function holomorphic on a polydisc is, on every smaller polydisc, the
uniform limit of entire functions — the Runge step of the Mittag-Leffler construction, in the form
the polydisc supplies it, with no approximation theory needed beyond truncating a Taylor series.

* `GaloisForLFunctions.HTGeometry.polydiscHasFPowerSeriesOnBall_of_differentiableOn` : the local
  power series.
* `GaloisForLFunctions.HTGeometry.differentiable_partialSum` : the partial sums are entire.
* `GaloisForLFunctions.HTGeometry.exists_entire_approx_of_differentiableOn` : uniform approximation
  by entire functions on a smaller polydisc.
-/

open MeasureTheory Complex Set
open scoped Real ENNReal

namespace GaloisForLFunctions.HTGeometry

section PartialSum

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **The partial sums of a formal multilinear series are entire.**  Each term is a continuous
multilinear map evaluated on the diagonal. -/
theorem differentiable_partialSum (p : FormalMultilinearSeries ℂ E F) (n : ℕ) :
    Differentiable ℂ (p.partialSum n) := by
  have hterm : ∀ i : ℕ, Differentiable ℂ (fun y : E => (p i) (fun _ => y)) := by
    intro i
    have h : Differentiable ℂ (fun v : Fin i → E => (p i) v) :=
      ((p i).contDiff (n := (1 : ℕ))).differentiable (by norm_num)
    exact h.comp (differentiable_pi.2 fun _ => differentiable_id)
  have heq : p.partialSum n = ∑ i ∈ Finset.range n, (fun y : E => (p i) fun _ => y) := by
    funext y
    simp [FormalMultilinearSeries.partialSum, Finset.sum_apply]
  rw [heq]
  exact Differentiable.sum fun i _ => hterm i

end PartialSum

section LocalSeries

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **The Cauchy power series of a function holomorphic on a polydisc.**  Continuity is needed only
to integrate over the distinguished boundary; holomorphy is needed only on the polydisc. -/
theorem torusSet_subset_polydiscSet {c : Fin n → ℂ} {R R₁ : ℝ} (hRR₁ : R < R₁) :
    {z : Fin n → ℂ | ∀ i, ‖z i - c i‖ = R} ⊆ polydiscSet c (fun _ => R₁) := by
  intro z hz i
  rw [Metric.mem_ball, Complex.dist_eq, hz i]
  exact hRR₁

theorem polydiscHasFPowerSeriesOnBall_of_differentiableOn
    {f : (Fin n → ℂ) → E} (c : Fin n → ℂ) {R R₁ : ℝ} (hR : 0 < R)
    (hRR₁ : R < R₁) (hdiff : DifferentiableOn ℂ f (polydiscSet c fun _ => R₁)) :
    HasFPowerSeriesOnBall f (polydiscSeries f c R) c (ENNReal.ofReal (R / 2 ^ (n + 1))) :=
  polydiscHasFPowerSeriesOnBall_of_cauchy hR
    (hdiff.continuousOn.mono (torusSet_subset_polydiscSet hRR₁))
    (fun z hz => polydiscCauchyFormula_of_differentiableOn n f c (fun _ => R₁) (fun _ => R)
      hdiff (fun _ => hR.le) (fun _ => hRR₁) z hz)

/-- **Uniform approximation by entire functions on a smaller polydisc.**  The partial sums of the
Cauchy series are entire and converge uniformly on every ball strictly inside the ball of
convergence, so a function holomorphic on a polydisc is uniformly approximated on every smaller
polydisc by entire functions. -/
theorem exists_entire_approx_of_differentiableOn
    {f : (Fin n → ℂ) → E} (c : Fin n → ℂ) {R R₁ ρ ε : ℝ} (hR : 0 < R)
    (hRR₁ : R < R₁) (hdiff : DifferentiableOn ℂ f (polydiscSet c fun _ => R₁))
    (hρ : 0 ≤ ρ) (hρR : ρ < R / 2 ^ (n + 1)) (hε : 0 < ε) :
    ∃ P : (Fin n → ℂ) → E, Differentiable ℂ P ∧
      ∀ z ∈ Metric.ball c ρ, ‖f z - P z‖ < ε := by
  have hball := polydiscHasFPowerSeriesOnBall_of_differentiableOn c hR hRR₁ hdiff
  have hcoe : ((ρ.toNNReal : NNReal) : ℝ) = ρ := Real.coe_toNNReal ρ hρ
  have hlt : ((ρ.toNNReal : NNReal) : ℝ≥0∞) < ENNReal.ofReal (R / 2 ^ (n + 1)) := by
    rw [show ((ρ.toNNReal : NNReal) : ℝ≥0∞) = ENNReal.ofReal ρ from rfl]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hρR
  have huniform := hball.tendstoUniformlyOn hlt
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 huniform) ε hε)
  refine ⟨fun z => (polydiscSeries f c R).partialSum N (z - c),
    (differentiable_partialSum _ N).comp (differentiable_id.sub_const c), fun z hz => ?_⟩
  have hzball : z - c ∈ Metric.ball (0 : Fin n → ℂ) ((ρ.toNNReal : NNReal) : ℝ) := by
    rw [Metric.mem_ball, dist_zero_right, hcoe]
    rw [Metric.mem_ball, dist_eq_norm] at hz
    exact hz
  have hkey := hN N le_rfl (z - c) hzball
  rw [dist_eq_norm] at hkey
  have hzc : c + (z - c) = z := by ring
  rw [hzc] at hkey
  exact hkey

/-- **Uniform approximation by entire functions on a closed polydisc strictly inside.**  The terms
of the Cauchy series are dominated on the smaller closed polydisc by a convergent series whose
terms do not depend on the point, so a partial sum — an entire function — approximates uniformly to
any accuracy.  Unlike the ball-of-convergence packaging, this loses no factor in the radius: the
series converges at every point of the polydisc of radius `R`. -/
theorem exists_entire_approx_closedBall
    {f : (Fin n → ℂ) → E} (c : Fin n → ℂ) {R R₁ ρ ε : ℝ} (hR : 0 < R)
    (hRR₁ : R < R₁) (hdiff : DifferentiableOn ℂ f (polydiscSet c fun _ => R₁))
    (hρ0 : 0 ≤ ρ) (hρR : ρ < R) (hε : 0 < ε) :
    ∃ P : (Fin n → ℂ) → E, Differentiable ℂ P ∧
      ∀ z ∈ Metric.closedBall c ρ, ‖f z - P z‖ ≤ ε := by
  classical
  obtain ⟨M, hM⟩ := exists_bound_on_torus hR (hdiff.continuousOn.mono (torusSet_subset_polydiscSet hRR₁))
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM fun _ => 0)
  have hcauchy : ∀ z : Fin n → ℂ, (∀ i, z i ∈ Metric.ball (c i) R) →
      (∯ ζ in T(c, fun _ => R), (∏ i, (ζ i - z i)⁻¹) • f ζ) =
        ((2 * Real.pi * Complex.I) ^ n : ℂ) • f z :=
    fun z hz => polydiscCauchyFormula_of_differentiableOn n f c (fun _ => R₁) (fun _ => R)
      hdiff (fun _ => hR.le) (fun _ => hRR₁) z hz
  set a : ℕ → ℝ := fun k => (((k + 1) ^ n : ℕ) : ℝ) * (ρ / R) ^ k * M with ha
  have hasum : Summable a := by
    rw [ha]
    exact (summable_succ_pow_mul_geometric n (by positivity)
      ((div_lt_one hR).2 hρR)).mul_right M
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∑' i, a (i + N) ≤ ε := by
    have htend := tendsto_sum_nat_add a
    obtain ⟨N, hNall⟩ := (Metric.tendsto_atTop.1 htend) ε hε
    refine ⟨N, ?_⟩
    have h := hNall N le_rfl
    rw [Real.dist_eq, sub_zero] at h
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) h)
  refine ⟨fun z => (polydiscSeries f c R).partialSum N (z - c),
    (differentiable_partialSum _ N).comp (differentiable_id.sub_const c), fun z hz => ?_⟩
  set y : Fin n → ℂ := z - c with hy
  have hynorm : ‖y‖ ≤ ρ := by
    rw [hy, ← dist_eq_norm]
    exact Metric.mem_closedBall.mp hz
  have hyR : ‖y‖ < R := lt_of_le_of_lt hynorm hρR
  set tm : ℕ → E := fun k => polydiscSeries f c R k fun _ => y with htm
  have hbound : ∀ k, ‖tm k‖ ≤ a k := by
    intro k
    have h1 : ‖tm k‖ ≤ ‖polydiscSeries f c R k‖ * ‖y‖ ^ k := by
      have := (polydiscSeries f c R k).le_opNorm (fun _ : Fin k => y)
      simpa using this
    have h2 : ‖polydiscSeries f c R k‖ ≤ ((k + 1) ^ n : ℕ) * (M / R ^ k) :=
      norm_polydiscSeries_le c hR hM k
    have h3 : ‖y‖ ^ k ≤ ρ ^ k := pow_le_pow_left₀ (norm_nonneg _) hynorm k
    calc ‖tm k‖ ≤ ‖polydiscSeries f c R k‖ * ‖y‖ ^ k := h1
      _ ≤ (((k + 1) ^ n : ℕ) : ℝ) * (M / R ^ k) * ρ ^ k := by
          refine mul_le_mul h2 h3 (by positivity) (by positivity)
      _ = a k := by
          simp only [ha, div_pow]
          field_simp
  have hnormsum : Summable fun k => ‖tm k‖ :=
    hasum.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  have hsum : HasSum tm (f z) := by
    have h := polydiscSeries_hasSum_of_cauchy hR
      (hdiff.continuousOn.mono (torusSet_subset_polydiscSet hRR₁)) hcauchy hM hyR
    have hcy : c + y = z := by rw [hy]; ring
    rwa [hcy] at h
  have hsplit := hsum.summable.sum_add_tsum_nat_add N
  have hpart : (polydiscSeries f c R).partialSum N y = ∑ i ∈ Finset.range N, tm i := rfl
  have hdiff' : f z - (polydiscSeries f c R).partialSum N y = ∑' i, tm (i + N) := by
    rw [hpart, ← hsum.tsum_eq, ← hsplit]
    abel
  rw [hdiff']
  refine le_trans (norm_tsum_le_tsum_norm ((hnormsum.comp_injective (add_left_injective N)))) ?_
  refine le_trans (Summable.tsum_le_tsum (fun i => hbound (i + N))
    ((hnormsum.comp_injective (add_left_injective N)))
    ((hasum.comp_injective (add_left_injective N)))) hN

end LocalSeries

end GaloisForLFunctions.HTGeometry
