import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import GaloisForLFunctions.HTGeometry.WeightedArgumentPrincipleDisc

/-!
# Factoring the zeros of a holomorphic function out of a disc

A function holomorphic on a neighbourhood of a closed disc and nonvanishing on the bounding circle
factors, on a slightly larger disc, as a finite product of powers of linear factors — one for each
of its finitely many zeros, all of them strictly inside — times a factor that is holomorphic and
nowhere zero there.

The zeros are finite in number because the divisor of a meromorphic function has locally finite
support and the closed disc is compact; the factorization itself is the elimination of zeros and
poles, whose conclusion holds off a set with no accumulation points and is upgraded to a pointwise
identity by continuity, every point of an open disc being an accumulation point of it.

* `HTGeometry.mem_thickening_sphere`;
* `HTGeometry.exists_factorization_of_analytic_disc`.
-/

open Complex Metric Filter Function
open scoped Real Topology

namespace HTGeometry

/-- A point at most `δ` further out than a sphere lies in the `δ`-thickening of that sphere. -/
theorem mem_thickening_sphere {t δ : ℝ} (ht : 0 < t) {z : ℂ}
    (h1 : t ≤ ‖z‖) (h2 : ‖z‖ < t + δ) : z ∈ thickening δ (sphere (0 : ℂ) t) := by
  have hz0 : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le ht h1
  refine Metric.mem_thickening_iff.2 ⟨(t / ‖z‖ : ℝ) • z, ?_, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ t / ‖z‖)]
    field_simp
  · rw [dist_eq_norm]
    have hsub : z - (t / ‖z‖ : ℝ) • z = ((1 : ℝ) - t / ‖z‖) • z := by
      rw [sub_smul, one_smul]
    have hnn : (0 : ℝ) ≤ 1 - t / ‖z‖ := by
      have : t / ‖z‖ ≤ 1 := by
        rw [div_le_one hz0]
        exact h1
      linarith
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnn]
    have hval : (1 - t / ‖z‖) * ‖z‖ = ‖z‖ - t := by
      field_simp
    rw [hval]
    linarith

/-- **Factoring the zeros out of a disc.**  A function holomorphic on a neighbourhood of the closed
disc of radius `t` and nonvanishing on the circle of radius `t` is, on a slightly larger open disc,
a finite product of powers of linear factors based at its zeros — all strictly inside the circle —
times a nowhere vanishing holomorphic factor. -/
theorem exists_factorization_of_analytic_disc
    {t : ℝ} (ht : 0 < t) {U : Set ℂ} (hU : IsOpen U) (hsub : closedBall (0 : ℂ) t ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hne : ∀ ζ ∈ sphere (0 : ℂ) t, f ζ ≠ 0) :
    ∃ (t₁ : ℝ) (s : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ),
      t < t₁ ∧ ball (0 : ℂ) t₁ ⊆ U ∧
      (∀ u ∈ s, u ∈ ball (0 : ℂ) t) ∧
      DifferentiableOn ℂ g (ball (0 : ℂ) t₁) ∧ (∀ z ∈ ball (0 : ℂ) t₁, g z ≠ 0) ∧
      Set.EqOn f (fun z => (∏ u ∈ s, (z - u) ^ m u) * g z) (ball (0 : ℂ) t₁) := by
  classical
  -- a radius on which `f` is holomorphic and has no zero outside the original disc
  obtain ⟨ε₁, hε₁, hε₁sub⟩ :=
    (isCompact_closedBall (0 : ℂ) t).exists_thickening_subset_open hU hsub
  rw [thickening_closedBall hε₁ ht.le] at hε₁sub
  set N : Set ℂ := U ∩ f ⁻¹' {(0 : ℂ)}ᶜ with hN
  have hNopen : IsOpen N := hf.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
  have hsphereN : sphere (0 : ℂ) t ⊆ N := fun ζ hζ =>
    ⟨hsub (sphere_subset_closedBall hζ), hne ζ hζ⟩
  obtain ⟨ε₂, hε₂, hε₂sub⟩ :=
    (isCompact_sphere (0 : ℂ) t).exists_thickening_subset_open hNopen hsphereN
  set ε : ℝ := min ε₁ ε₂ with hεdef
  have hε : 0 < ε := lt_min hε₁ hε₂
  set t₁ : ℝ := t + ε / 2 with ht₁def
  have ht₁ : t < t₁ := by rw [ht₁def]; linarith
  have hballU : ball (0 : ℂ) t₁ ⊆ U := by
    refine subset_trans ?_ hε₁sub
    refine ball_subset_ball ?_
    have : ε ≤ ε₁ := min_le_left _ _
    rw [ht₁def]
    linarith
  -- no zero of `f` in the closed annulus between the two radii
  have hannulus : ∀ z : ℂ, t ≤ ‖z‖ → ‖z‖ ≤ t₁ → f z ≠ 0 := by
    intro z h1 h2
    have h3 : ‖z‖ < t + ε₂ := by
      have : ε ≤ ε₂ := min_le_right _ _
      rw [ht₁def] at h2
      linarith
    have := hε₂sub (mem_thickening_sphere ht h1 h3)
    exact this.2
  -- the analytic data on the closed disc of the larger radius
  set K : Set ℂ := closedBall (0 : ℂ) t₁ with hK
  have hKsub : K ⊆ ball (0 : ℂ) (t + ε) := by
    intro z hz
    rw [mem_closedBall_zero_iff] at hz
    rw [mem_ball_zero_iff]
    rw [ht₁def] at hz
    linarith
  have hKU : K ⊆ U := by
    refine subset_trans hKsub (subset_trans (ball_subset_ball ?_) hε₁sub)
    have : ε ≤ ε₁ := min_le_left _ _
    linarith
  have hanU : AnalyticOnNhd ℂ f U := hf.analyticOnNhd hU
  have hanK : AnalyticOnNhd ℂ f K := fun z hz => hanU z (hKU hz)
  have hmero : MeromorphicOn f K := hanK.meromorphicOn
  -- `f` is nowhere locally zero on the larger disc
  have hballconn : IsPreconnected (ball (0 : ℂ) (t + ε)) :=
    (convex_ball (0 : ℂ) (t + ε)).isPreconnected
  have hanbig : AnalyticOnNhd ℂ f (ball (0 : ℂ) (t + ε)) := by
    intro z hz
    refine hanU z ?_
    refine hε₁sub ?_
    have : ε ≤ ε₁ := min_le_left _ _
    exact ball_subset_ball (by linarith) hz
  have hnotzero : ∀ z ∈ ball (0 : ℂ) (t + ε), ¬ (f =ᶠ[𝓝 z] 0) := by
    intro z hz hcon
    have hall := hanbig.eqOn_zero_of_preconnected_of_eventuallyEq_zero hballconn hz hcon
    have htmem : (t : ℂ) ∈ ball (0 : ℂ) (t + ε) := by
      rw [mem_ball_zero_iff]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
      linarith
    have : f (t : ℂ) = 0 := hall htmem
    exact hne (t : ℂ) (by simp [abs_of_pos ht]) this
  have horder : ∀ u : K, meromorphicOrderAt f u ≠ ⊤ := by
    rintro ⟨u, hu⟩
    intro hcon
    rw [meromorphicOrderAt_eq_top_iff] at hcon
    have huball : u ∈ ball (0 : ℂ) (t + ε) := hKsub hu
    refine hnotzero u huball ?_
    have hanu : AnalyticAt ℂ f u := hanbig u huball
    rcases hanu.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact h
    · exact absurd hcon (by
        intro hc
        exact (h.and hc).exists.elim fun z hz => hz.1 hz.2)
  have hfin : (MeromorphicOn.divisor f K).support.Finite :=
    (MeromorphicOn.divisor f K).finiteSupport (isCompact_closedBall 0 t₁)
  obtain ⟨g, hgan, hgne, hgeq⟩ := hmero.extract_zeros_poles horder hfin
  set D : ℂ → ℤ := fun u => MeromorphicOn.divisor f K u with hD
  set φ : ℂ → ℂ := ∏ᶠ u, (fun x : ℂ => x - u) ^ D u with hφ
  have hDnn : ∀ u : ℂ, 0 ≤ D u := fun u => MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanK u
  -- the zeros are all strictly inside the original circle
  have hDsupp : ∀ u ∈ hfin.toFinset, u ∈ ball (0 : ℂ) t := by
    intro u hu
    have hu' : D u ≠ 0 := by
      have : u ∈ (MeromorphicOn.divisor f K).support := by simpa using hu
      simpa [hD] using this
    have huK : u ∈ K := by
      by_contra hcon
      exact hu' ((MeromorphicOn.divisor f K).apply_eq_zero_of_notMem hcon)
    have hzero : f u = 0 := by
      by_contra hcon
      refine hu' ?_
      have hord : analyticOrderAt f u = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hcon)
      rw [hD]
      simp [MeromorphicOn.AnalyticOnNhd.divisor_apply hanK huK, hord]
    rw [mem_ball_zero_iff]
    by_contra hcon
    rw [not_lt] at hcon
    exact hannulus u hcon (by simpa [hK, mem_closedBall_zero_iff] using huK) hzero
  refine ⟨t₁, hfin.toFinset, fun u => (D u).toNat, g, ht₁, hballU, hDsupp, ?_, ?_, ?_⟩
  · exact fun z hz => (hgan z (ball_subset_closedBall hz)).differentiableAt.differentiableWithinAt
  · exact fun z hz => hgne ⟨z, ball_subset_closedBall hz⟩
  · intro z hz
    have hzK : z ∈ K := ball_subset_closedBall hz
    have hSmem : {w | f w = (φ • g) w} ∪ Kᶜ ∈ 𝓝[≠] z :=
      mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hgeq z hzK
    have hballmem : ball (0 : ℂ) t₁ ∈ 𝓝[≠] z :=
      nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz)
    have hev : ∀ᶠ w in 𝓝[≠] z, f w = (φ • g) w := by
      filter_upwards [hSmem, hballmem] with w hw hwb
      rcases hw with h | h
      · exact h
      · exact absurd (ball_subset_closedBall hwb) h
    have hφan : AnalyticAt ℂ φ z := Function.FactorizedRational.analyticAt (hDnn z)
    have hgz : AnalyticAt ℂ g z := hgan z hzK
    have hfz : AnalyticAt ℂ f z := hanK z hzK
    have h1 : Filter.Tendsto f (𝓝[≠] z) (𝓝 (f z)) :=
      hfz.continuousAt.continuousWithinAt.tendsto
    have h2 : Filter.Tendsto (φ • g) (𝓝[≠] z) (𝓝 ((φ • g) z)) :=
      ((hφan.continuousAt.smul hgz.continuousAt)).continuousWithinAt.tendsto
    have heq : f z = (φ • g) z := tendsto_nhds_unique_of_eventuallyEq h1 h2 hev
    have hφval : φ z = ∏ u ∈ hfin.toFinset, (z - u) ^ (D u).toNat := by
      have hfs : Function.HasFiniteSupport D := hfin
      rw [hφ, Function.FactorizedRational.finprod_eq_fun hfs]
      show ∏ᶠ u : ℂ, (z - u) ^ D u = ∏ u ∈ hfin.toFinset, (z - u) ^ (D u).toNat
      rw [finprod_eq_prod_of_mulSupport_subset (fun u => (z - u) ^ D u) (s := hfin.toFinset) ?_]
      · refine Finset.prod_congr rfl fun u _ => ?_
        rw [← zpow_natCast, Int.toNat_of_nonneg (hDnn u)]
      · intro u hu
        simp only [Function.mem_mulSupport] at hu
        have : D u ≠ 0 := by
          intro h0
          exact hu (by rw [h0, zpow_zero])
        simpa [hD] using this
    rw [heq]
    show φ z * g z = (∏ u ∈ hfin.toFinset, (z - u) ^ (D u).toNat) * g z
    rw [hφval]

/-- **The weighted argument principle on a disc, unconditionally.**  For a function holomorphic on
a neighbourhood of a closed disc and nonvanishing on the bounding circle there is a finite family
of zeros with multiplicities, all strictly inside, whose power sums are computed by the weighted
logarithmic-derivative integrals. -/
theorem circleIntegral_weighted_logDeriv_eq_powerSum
    {t : ℝ} (ht : 0 < t) {U : Set ℂ} (hU : IsOpen U) (hsub : closedBall (0 : ℂ) t ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hne : ∀ ζ ∈ sphere (0 : ℂ) t, f ζ ≠ 0) :
    ∃ (s : Finset ℂ) (m : ℂ → ℕ), (∀ u ∈ s, u ∈ ball (0 : ℂ) t) ∧
      ∀ p : ℕ, (∮ ζ in C(0, t), ζ ^ p * logDeriv f ζ)
        = (2 * (Real.pi : ℂ) * Complex.I) * ∑ u ∈ s, (m u : ℂ) * u ^ p := by
  obtain ⟨t₁, s, m, g, ht₁, hballU, hs, hgd, hgne, heq⟩ :=
    exists_factorization_of_analytic_disc ht hU hsub hf hne
  refine ⟨s, m, hs, fun p => ?_⟩
  have hcircle : ∀ ζ ∈ sphere (0 : ℂ) t,
      ζ ^ p * logDeriv f ζ
        = ζ ^ p * logDeriv (fun z => (∏ u ∈ s, (z - u) ^ m u) * g z) ζ := by
    intro ζ hζ
    have hζt : ‖ζ‖ = t := by simpa using mem_sphere_iff_norm.1 hζ
    have hζball : ζ ∈ ball (0 : ℂ) t₁ := by
      rw [mem_ball_zero_iff, hζt]
      exact ht₁
    have hev : f =ᶠ[𝓝 ζ] fun z => (∏ u ∈ s, (z - u) ^ m u) * g z :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hζball) heq
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [circleIntegral.integral_congr ht.le hcircle]
  exact circleIntegral_weighted_logDeriv_prod ht isOpen_ball
    (closedBall_subset_ball ht₁) s m hs hgd hgne p

end HTGeometry
