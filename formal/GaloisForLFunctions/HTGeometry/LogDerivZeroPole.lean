import Mathlib

/-!
# A zero is a genuine singularity of the curvature of the logarithmic derivative

If an analytic function factors as `f(z) = (z−ρ)^{n+1} g(z)` with `g(ρ) ≠ 0`, then on a punctured
neighbourhood

`(log f)′(z) = (n+1)/(z−ρ) + (log g)′(z)`,   `(log f)″(z) = −(n+1)/(z−ρ)² + (log g)″(z)`,

and the second is unbounded, because the correction is analytic at `ρ` and the pole is not.

This is the exact shape a Landau-type argument needs: it says the curvature of the logarithmic
derivative cannot be extended continuously — let alone holomorphically — through a zero, so a
transform equal to it on a half-plane cannot be holomorphic there either.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **The logarithmic derivative of an analytic function at a zero of order `m`.**  On a punctured
neighbourhood it is `m/(z−ρ)` plus the logarithmic derivative of the nonvanishing factor. -/
theorem logDeriv_eventuallyEq_of_factor {f g : ℂ → ℂ} {ρ : ℂ} {n : ℕ}
    (hg : AnalyticAt ℂ g ρ) (hgne : g ρ ≠ 0)
    (hfac : ∀ᶠ z in 𝓝 ρ, f z = (z - ρ) ^ (n + 1) * g z) :
    ∀ᶠ z in 𝓝[≠] ρ, logDeriv f z = ((n : ℂ) + 1) / (z - ρ) + logDeriv g z := by
  have hgc : ContinuousAt g ρ := hg.continuousAt
  have hgnb : ∀ᶠ z in 𝓝 ρ, g z ≠ 0 := hgc.eventually_ne hgne
  have hgd : ∀ᶠ z in 𝓝 ρ, DifferentiableAt ℂ g z := hg.eventually_analyticAt.mono
    fun z hz => hz.differentiableAt
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hfac, hgnb, hgd, eventually_eventually_nhds.mpr hfac] with z hz hgz hgdz hfz
  intro hzne
  have hzsub : z - ρ ≠ 0 := sub_ne_zero.mpr hzne
  have hpow : HasDerivAt (fun w : ℂ => (w - ρ) ^ (n + 1))
      (((n : ℂ) + 1) * (z - ρ) ^ n) z := by
    have h1 : HasDerivAt (fun w : ℂ => w - ρ) 1 z := (hasDerivAt_id z).sub_const ρ
    have h2 := h1.pow (n + 1)
    refine h2.congr_deriv ?_
    push_cast
    ring
  have hprod : HasDerivAt (fun w : ℂ => (w - ρ) ^ (n + 1) * g w)
      (((n : ℂ) + 1) * (z - ρ) ^ n * g z + (z - ρ) ^ (n + 1) * deriv g z) z :=
    hpow.mul hgdz.hasDerivAt
  have hderiv : deriv f z
      = ((n : ℂ) + 1) * (z - ρ) ^ n * g z + (z - ρ) ^ (n + 1) * deriv g z := by
    rw [Filter.EventuallyEq.deriv_eq hfz]
    exact hprod.deriv
  rw [logDeriv_apply, logDeriv_apply, hderiv, hz]
  have hden : (z - ρ) ^ (n + 1) * g z ≠ 0 := mul_ne_zero (pow_ne_zero _ hzsub) hgz
  field_simp
  ring

/-- The derivative of the logarithmic derivative, near a zero of order `n+1`. -/
theorem deriv_logDeriv_eventuallyEq_of_factor {f g : ℂ → ℂ} {ρ : ℂ} {n : ℕ}
    (hg : AnalyticAt ℂ g ρ) (hgne : g ρ ≠ 0)
    (hfac : ∀ᶠ z in 𝓝 ρ, f z = (z - ρ) ^ (n + 1) * g z) :
    ∀ᶠ z in 𝓝[≠] ρ,
      deriv (logDeriv f) z = -(((n : ℂ) + 1) / (z - ρ) ^ 2) + deriv (logDeriv g) z := by
  have hbase := logDeriv_eventuallyEq_of_factor hg hgne hfac
  rw [eventually_nhdsWithin_iff] at hbase
  obtain ⟨U, hUsub, hUopen, hUmem⟩ := mem_nhds_iff.mp hbase
  have hgd : ∀ᶠ z in 𝓝 ρ, DifferentiableAt ℂ g z := hg.eventually_analyticAt.mono
    fun z hz => hz.differentiableAt
  have hlog : AnalyticAt ℂ (logDeriv g) ρ := (hg.deriv).div hg hgne
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hUopen.mem_nhds hUmem, hlog.eventually_analyticAt] with z hzU hzA
  intro hzne
  have hopen : IsOpen (U \ {ρ}) := hUopen.sdiff isClosed_singleton
  have hmem : z ∈ U \ {ρ} := ⟨hzU, hzne⟩
  have hev : logDeriv f =ᶠ[𝓝 z] fun w : ℂ => ((n : ℂ) + 1) / (w - ρ) + logDeriv g w := by
    filter_upwards [hopen.mem_nhds hmem] with w hw
    exact hUsub hw.1 hw.2
  rw [Filter.EventuallyEq.deriv_eq hev]
  have hzsub : z - ρ ≠ 0 := sub_ne_zero.mpr hzne
  have hlogd : DifferentiableAt ℂ (logDeriv g) z := hzA.differentiableAt
  have hinv : HasDerivAt (fun w : ℂ => ((n : ℂ) + 1) / (w - ρ))
      (-(((n : ℂ) + 1) / (z - ρ) ^ 2)) z := by
    have h1 : HasDerivAt (fun w : ℂ => w - ρ) 1 z := (hasDerivAt_id z).sub_const ρ
    have h2 := (h1.inv hzsub).const_mul ((n : ℂ) + 1)
    refine h2.congr_deriv ?_
    field_simp
  have hsum : HasDerivAt (fun w : ℂ => ((n : ℂ) + 1) / (w - ρ) + logDeriv g w)
      (-(((n : ℂ) + 1) / (z - ρ) ^ 2) + deriv (logDeriv g) z) z :=
    hinv.add hlogd.hasDerivAt
  exact hsum.deriv

/-- **A zero of an analytic function is a genuine singularity of the derivative of its logarithmic
derivative.**  Near a zero of order `n+1` that derivative is `-(n+1)/(z−ρ)²` plus an analytic term,
hence unbounded. -/
theorem not_bounded_deriv_logDeriv_of_factor {f g : ℂ → ℂ} {ρ : ℂ} {n : ℕ}
    (hg : AnalyticAt ℂ g ρ) (hgne : g ρ ≠ 0)
    (hfac : ∀ᶠ z in 𝓝 ρ, f z = (z - ρ) ^ (n + 1) * g z) (C : ℝ) :
    ¬ (∀ᶠ z in 𝓝[≠] ρ, ‖deriv (logDeriv f) z‖ ≤ C) := by
  intro hC
  have hlog : AnalyticAt ℂ (logDeriv g) ρ := (hg.deriv).div hg hgne
  have hdlog : AnalyticAt ℂ (deriv (logDeriv g)) ρ := hlog.deriv
  have hcont : ContinuousAt (fun z : ℂ => ‖deriv (logDeriv g) z‖) ρ :=
    (hdlog.continuousAt).norm
  have hBlt : ‖deriv (logDeriv g) ρ‖ < ‖deriv (logDeriv g) ρ‖ + 1 := by linarith
  have hB : ∀ᶠ z in 𝓝 ρ, ‖deriv (logDeriv g) z‖ < ‖deriv (logDeriv g) ρ‖ + 1 :=
    hcont.eventually_lt_const hBlt
  have hBw : ∀ᶠ z in 𝓝[≠] ρ, ‖deriv (logDeriv g) z‖ < ‖deriv (logDeriv g) ρ‖ + 1 :=
    nhdsWithin_le_nhds hB
  have hkey : ∀ᶠ z in 𝓝[≠] ρ,
      ((n : ℝ) + 1) ≤ (C + (‖deriv (logDeriv g) ρ‖ + 1)) * ‖z - ρ‖ ^ 2 := by
    filter_upwards [deriv_logDeriv_eventuallyEq_of_factor hg hgne hfac, hC, hBw,
      self_mem_nhdsWithin] with z hz hz1 hz2 hzne
    have hzsub : z - ρ ≠ 0 := sub_ne_zero.mpr hzne
    have hnorm : ‖-(((n : ℂ) + 1) / (z - ρ) ^ 2)‖ = ((n : ℝ) + 1) / ‖z - ρ‖ ^ 2 := by
      rw [norm_neg, norm_div, norm_pow]
      congr 1
      rw [show ((n : ℂ) + 1) = ((((n : ℝ) + 1 : ℝ)) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hsplit : -(((n : ℂ) + 1) / (z - ρ) ^ 2)
        = deriv (logDeriv f) z - deriv (logDeriv g) z := by
      rw [hz]
      ring
    have hle : ((n : ℝ) + 1) / ‖z - ρ‖ ^ 2 ≤ C + (‖deriv (logDeriv g) ρ‖ + 1) := by
      rw [← hnorm, hsplit]
      exact (norm_sub_le _ _).trans (add_le_add hz1 hz2.le)
    have hpos : (0 : ℝ) < ‖z - ρ‖ ^ 2 := by
      have : (0 : ℝ) < ‖z - ρ‖ := norm_pos_iff.mpr hzsub
      positivity
    rw [div_le_iff₀ hpos] at hle
    exact hle
  have htend : Filter.Tendsto
      (fun z : ℂ => (C + (‖deriv (logDeriv g) ρ‖ + 1)) * ‖z - ρ‖ ^ 2) (𝓝[≠] ρ) (nhds 0) := by
    have h0 : Filter.Tendsto (fun z : ℂ => ‖z - ρ‖ ^ 2) (𝓝 ρ) (nhds 0) := by
      have hc : ContinuousAt (fun z : ℂ => ‖z - ρ‖ ^ 2) ρ := by fun_prop
      have ht := hc.tendsto
      simpa using ht
    have h1 : Filter.Tendsto (fun z : ℂ => ‖z - ρ‖ ^ 2) (𝓝[≠] ρ) (nhds 0) :=
      h0.mono_left nhdsWithin_le_nhds
    simpa using h1.const_mul (C + (‖deriv (logDeriv g) ρ‖ + 1))
  have hfinal : ((n : ℝ) + 1) ≤ 0 := ge_of_tendsto htend hkey
  have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  linarith

end GaloisForLFunctions.HTGeometry
