import GaloisForLFunctions.HTGeometry.SmoothUniformLimit

/-!
# Uniformly Cauchy sequences of smooth periodic functions converge

A sequence of smooth functions whose every derivative is uniformly Cauchy has a smooth limit, and
if the terms share a period so does the limit.  This is the sequential completeness underlying the
Fréchet structure of `C^∞(ℝ/Lℤ)`.

* `exists_smooth_limit_of_uniformCauchy` : **the limit exists, is smooth, and is periodic.**
-/

namespace GaloisForLFunctions

open Filter Topology
open scoped ContDiff

variable {F : ℕ → ℝ → ℂ}

/-- **A sequence of smooth functions with every derivative uniformly Cauchy has a smooth limit.**
If every term has period `L`, so does the limit, and every derivative converges uniformly. -/
theorem exists_smooth_limit_of_uniformCauchy
    (hFsmooth : ∀ n, ContDiff ℝ ∞ (F n))
    (hcauchy : ∀ r : ℕ, UniformCauchySeqOn (fun n => iteratedDeriv r (F n)) atTop Set.univ)
    {L : ℝ} (hper : ∀ n, Function.Periodic (F n) L) :
    ∃ G : ℝ → ℂ, ContDiff ℝ ∞ G ∧ Function.Periodic G L
      ∧ ∀ r, TendstoUniformly (fun n => iteratedDeriv r (F n)) (iteratedDeriv r G) atTop := by
  classical
  -- pointwise limits of every derivative
  have hpt : ∀ (r : ℕ) (x : ℝ), ∃ y : ℂ,
      Tendsto (fun n => iteratedDeriv r (F n) x) atTop (𝓝 y) := by
    intro r x
    refine cauchySeq_tendsto_of_complete ?_
    have := (hcauchy r).cauchySeq (Set.mem_univ x)
    exact this
  choose Gf hGf using hpt
  -- uniform convergence of every derivative
  have hunif : ∀ r : ℕ, TendstoUniformly (fun n => iteratedDeriv r (F n)) (Gf r) atTop := by
    intro r
    rw [← tendstoUniformlyOn_univ]
    exact (hcauchy r).tendstoUniformlyOn_of_tendsto fun x _ => hGf r x
  -- the limit is smooth with the expected derivatives
  have hsmooth : ContDiff ℝ ∞ (Gf 0) :=
    contDiff_of_tendstoUniformly_iteratedDeriv hFsmooth hunif
  have hiter : ∀ r, iteratedDeriv r (Gf 0) = Gf r :=
    iteratedDeriv_limit hFsmooth hunif
  refine ⟨Gf 0, hsmooth, ?_, ?_⟩
  · intro t
    have h1 : Tendsto (fun n => F n (t + L)) atTop (𝓝 (Gf 0 (t + L))) := by
      have := hGf 0 (t + L)
      simpa [iteratedDeriv_zero] using this
    have h2 : Tendsto (fun n => F n t) atTop (𝓝 (Gf 0 t)) := by
      have := hGf 0 t
      simpa [iteratedDeriv_zero] using this
    have h3 : (fun n => F n (t + L)) = fun n => F n t := funext fun n => hper n t
    rw [h3] at h1
    exact tendsto_nhds_unique h1 h2
  · intro r
    rw [hiter r]
    exact hunif r

end GaloisForLFunctions
