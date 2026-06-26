/-
# The natural-boundary contradiction, assembled (dendrite case)

The capstone of the natural-boundary route to Böttcher transcendence: it composes the local algebraic
branch (`AlgebraicBranch.exists_analyticAt_branch_poly`), the basin-side matching
(`AlgebraicBranch.branch_unique_poly_within`), and the boundary engine
(`DendriteBoundary.no_continuation_dendrite`) into a single `False` from the basin-branch data.

Given a Julia point `z₀` in the empty-interior (dendrite) case and a basin Böttcher branch `β` that
(i) tends to a simple root `w₀` of the relation along the basin, (ii) satisfies the relation, and
(iii) carries the genuine modulus `‖β‖ = exp(G_c)`, the algebraic branch `g` analytic across `z₀` must
equal `β` on the basin side, inheriting the modulus — which `no_continuation_dendrite` forbids.

This isolates the **entire** remaining content of the connected-case transcendence into the existence of
such a `β` (the single-valued basin Böttcher branch tending to a simple root at a dendrite Julia point —
the trivial-dyadic-monodromy / connected-`J_c` input owned by the basin-construction lane). Everything
that consumes it is now verified.
-/
import GaloisForLFunctions.Bottcher.AlgebraicBranch
import GaloisForLFunctions.Bottcher.DendriteBoundary
import GaloisForLFunctions.Bottcher.ResonanceOrder
import GaloisForLFunctions.Bottcher.CoverConstruction
import Mathlib.Analysis.Analytic.Uniqueness

open Filter Topology Metric Set

namespace Bottcher

/-- **Assembly capstone (dendrite case): the basin branch forces `False`.** Given a Julia point `z₀` in
the empty-interior (dendrite) case, the simple-root data of a polynomial relation at `(z₀, w₀)`, and a
basin Böttcher branch `β` (defined on the basin side `(filledJulia c)ᶜ`, tending to `w₀`, satisfying the
relation, with the genuine modulus `‖β‖ = exp(G_c)`), one derives `False`. The algebraic branch `g` from
`exists_analyticAt_branch_poly` is analytic across `z₀`; `branch_unique_poly_within` matches `g = β` on
the basin side, so `g` inherits the Böttcher modulus there; `no_continuation_dendrite` closes it. -/
theorem false_of_basin_branch_dendrite {c z₀ w₀ d : ℂ} {r : ℝ}
    (P : Polynomial (Polynomial ℂ))
    (hr : 0 < r) (hz₀ : z₀ ∈ filledJulia c)
    (hempty : ball z₀ r ∩ interior (filledJulia c) = ∅)
    (hroot : ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w₀ ^ i = 0)
    (hpartial : HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) d w₀) (hd : d ≠ 0)
    {β : ℂ → ℂ}
    (hβlim : Tendsto β (𝓝[(filledJulia c)ᶜ] z₀) (𝓝 w₀))
    (hβrel : ∀ᶠ z in 𝓝[(filledJulia c)ᶜ] z₀, ∑ i ∈ P.support, (P.coeff i).aeval z * (β z) ^ i = 0)
    (hβmod : ∀ᶠ z in 𝓝[(filledJulia c)ᶜ] z₀, ‖β z‖ = Real.exp (greenFunctionDyn c z)) :
    False := by
  -- the basin meets every neighbourhood of `z₀` (it is not in the interior of `K_c`)
  have hz₀int : z₀ ∉ interior (filledJulia c) := fun h => by
    have : z₀ ∈ ball z₀ r ∩ interior (filledJulia c) := ⟨mem_ball_self hr, h⟩
    rwa [hempty] at this
  have hNeBot : (𝓝[(filledJulia c)ᶜ] z₀).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (by rw [closure_compl]; exact hz₀int)
  obtain ⟨g, hgAt, hgz₀, hgrel⟩ := exists_analyticAt_branch_poly P hroot hpartial hd
  have hmatch := branch_unique_poly_within P hpartial hd hgAt.continuousAt hgz₀ hβlim
    (hgrel.filter_mono nhdsWithin_le_nhds) hβrel
  have hgmod : ∀ᶠ z in 𝓝[(filledJulia c)ᶜ] z₀, ‖g z‖ = Real.exp (greenFunctionDyn c z) := by
    filter_upwards [hmatch, hβmod] with z hz hzm; rw [hz, hzm]
  obtain ⟨ε₁, hε₁, hgan1⟩ := Metric.eventually_nhds_iff.mp hgAt.eventually_analyticAt
  obtain ⟨U, hUopen, hz₀U, hUsub⟩ := mem_nhdsWithin.mp hgmod
  obtain ⟨ε₂, hε₂, hUball⟩ := Metric.isOpen_iff.mp hUopen z₀ hz₀U
  set r' := min r (min ε₁ ε₂) with hr'def
  have hr' : 0 < r' := lt_min hr (lt_min hε₁ hε₂)
  have hr'r : r' ≤ r := min_le_left _ _
  have hr'1 : r' ≤ ε₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hr'2 : r' ≤ ε₂ := le_trans (min_le_right _ _) (min_le_right _ _)
  refine no_continuation_dendrite (g := g) hr' ?_ hz₀ ?_ ?_ ?_
  · intro z hz
    exact hgan1 (lt_of_lt_of_le (mem_ball.mp hz) hr'1)
  · refine eq_empty_of_subset_empty ?_
    rw [← hempty]
    exact inter_subset_inter_left _ (Metric.ball_subset_ball hr'r)
  · intro z hz hzK
    exact hUsub ⟨hUball (Metric.ball_subset_ball hr'2 hz), hzK⟩
  · obtain ⟨z, hz1, hz2⟩ :=
      hNeBot.nonempty_of_mem (inter_mem_nhdsWithin _ (ball_mem_nhds z₀ hr'))
    exact ⟨z, hz2, hz1⟩

/-- **Resonance-route finisher (the clean uniform contradiction).** If a single-valued branch `g` is
analytic on a preconnected open `V`, satisfies the Böttcher functional equation `g ∘ f_c^[p] = g^{2^p}` on
`V`, passes through a non-resonant periodic point `z₀ ∈ V` (`f_c^[p] z₀ = z₀`, multiplier `λ` with
`λ^m ≠ 2^p` for all `m ≥ 1`) with `g z₀ ≠ 0`, and is non-constant on `V`, then `False`. By
`ResonanceOrder.const_of_no_resonance` the functional equation + non-resonance force `g` locally constant at
`z₀`, hence (identity theorem) constant on the connected `V` — contradicting non-constancy.

Unlike `false_of_basin_branch_dendrite`, this needs **no** boundary-case split and **no**
`‖g‖ = exp(G_c)` on `K_c`-interior: it is the uniform finisher for the connected-case transcendence. The
remaining inputs are exactly the single shared bottleneck — the continuation `g` (single-valued branch of
`φ_c`, carrying the functional equation via `TranscendenceReduction.eqOn_funEq_of_eventuallyEq` and
non-constant since `|g| = exp G_c`) reaching a non-resonant repelling periodic point (dense in `J_c`). -/
theorem false_of_funEq_at_nonresonant {c lam : ℂ} {p : ℕ} {V : Set ℂ} {g : ℂ → ℂ} {z₀ : ℂ}
    (hVc : IsPreconnected V) (hVo : IsOpen V) (hz₀V : z₀ ∈ V)
    (hgan : AnalyticOnNhd ℂ g V)
    (hgfe : Set.EqOn (fun z => g ((quadratic c)^[p] z)) (fun z => (g z) ^ (2 ^ p)) V)
    (hFz : (quadratic c)^[p] z₀ = z₀) (hlam : HasDerivAt ((quadratic c)^[p]) lam z₀)
    (hζ0 : g z₀ ≠ 0)
    (hres : ∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))
    (hnoncon : ∃ z ∈ V, g z ≠ g z₀) :
    False := by
  have hd1 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  have hFAt : AnalyticAt ℂ ((quadratic c)^[p]) z₀ :=
    analyticOnNhd_quadratic_iterate c p z₀ (mem_univ _)
  have hgAt : AnalyticAt ℂ g z₀ := hgan z₀ hz₀V
  have hζd : (g z₀) ^ (2 ^ p) = g z₀ := by
    have h := hgfe hz₀V
    simp only [hFz] at h
    exact h.symm
  have heq : (fun z => g ((quadratic c)^[p] z)) =ᶠ[𝓝 z₀] (fun z => (g z) ^ (2 ^ p)) :=
    hgfe.eventuallyEq_of_mem (hVo.mem_nhds hz₀V)
  have hconst : ∀ᶠ z in 𝓝 z₀, g z = g z₀ :=
    const_of_no_resonance hd1 hFAt hgAt hFz hlam rfl hζ0 hζd heq hres
  have hgV : Set.EqOn g (fun _ => g z₀) V :=
    hgan.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hVc hz₀V hconst
  obtain ⟨z, hzV, hzne⟩ := hnoncon
  exact hzne (hgV hzV)

/-- **Resonance finisher from only the local (`∀ᶠ`) functional equation.** The divisibility-route form:
no global continuation domain `V`, no preconnectedness, no `EqOn`. If `g` is analytic at a non-resonant
periodic point `z₀` (`f_c^[p] z₀ = z₀`, multiplier `λ` with `λ^m ≠ 2^p` for `m ≥ 1`), `g z₀ ≠ 0`, the
Böttcher functional equation `g(f_c^[p] z) = (g z)^{2^p}` holds in a *neighbourhood* of `z₀`, and `g` is
not locally constant at `z₀`, then `False`. `const_of_no_resonance` forces `∀ᶠ z, g z = g z₀`, contradicting
non-local-constancy. The `∀ᶠ` functional equation is exactly what `BranchContinuation.funEq_of_branch`
produces from the algebraic branch + the `P ∣ P(f^[p]·, ·^{2^p})` divisibility gateway — so this is the
finisher the divisibility route feeds, with the genuinely dynamical residue isolated to: *a non-resonant
periodic point that is a simple root of the relation, with non-locally-constant branch*. -/
theorem false_of_eventually_funEq_at_nonresonant {c lam : ℂ} {p : ℕ} {g : ℂ → ℂ} {z₀ : ℂ}
    (hgAt : AnalyticAt ℂ g z₀)
    (heq : (fun z => g ((quadratic c)^[p] z)) =ᶠ[𝓝 z₀] (fun z => (g z) ^ (2 ^ p)))
    (hFz : (quadratic c)^[p] z₀ = z₀) (hlam : HasDerivAt ((quadratic c)^[p]) lam z₀)
    (hζ0 : g z₀ ≠ 0) (hres : ∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))
    (hnoncon : ¬ (∀ᶠ z in 𝓝 z₀, g z = g z₀)) :
    False := by
  have hd1 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  have hFAt : AnalyticAt ℂ ((quadratic c)^[p]) z₀ :=
    analyticOnNhd_quadratic_iterate c p z₀ (mem_univ _)
  have hζd : (g z₀) ^ (2 ^ p) = g z₀ := by
    have h := heq.eq_of_nhds
    simp only [hFz] at h; exact h.symm
  exact hnoncon (const_of_no_resonance hd1 hFAt hgAt hFz hlam rfl hζ0 hζd heq hres)

end Bottcher
