import GaloisForLFunctions.Bottcher.RhoPathLift
import GaloisForLFunctions.Bottcher.BasinColimit
import GaloisForLFunctions.Bottcher.BasinConnected
import GaloisForLFunctions.Bottcher.GlobalBasinBranch
import GaloisForLFunctions.Bottcher.ConnectedRepellingFibreInput

/-!
# The Böttcher modulus is automatic in the connected case

The connected-case repelling-cycle contradiction `false_of_repelling_branch_global_modulus`
consumes three facts about the basin branch `β`: it is analytic on `(K_c)ᶜ`, it agrees with the
Böttcher coordinate on `escapeOpen c`, and it carries the Böttcher **modulus**
`‖β z‖ = exp(G_c z)`.  For `c ∈ mandelbrot` the modulus fact is not an independent hypothesis: the
unconditional connected branch produced by the ρ-tower path lift
(`exists_global_branch_modulus_of_mem_mandelbrot`) already carries it, the basin `(K_c)ᶜ` is
preconnected (`isPreconnected_compl_filledJulia`, unconditional), and any two analytic branches
anchored on `escapeOpen c` agree on the whole basin by the identity theorem.  Hence the modulus of
*every* escapeOpen-anchored analytic basin branch is forced.

`branch_modulus_of_mem_mandelbrot` records this, and `false_of_repelling_branch_mem_mandelbrot`
feeds it in, so the connected repelling contradiction no longer needs the modulus hypothesis for
`c ∈ mandelbrot` — it follows from membership alone.  Axiom-clean.
-/

open Bottcher Set Filter Topology

namespace Bottcher

/-- **The Böttcher modulus is forced for any connected basin branch (`c ∈ mandelbrot`).**  If `β` is
analytic on `(K_c)ᶜ` and equals `bottcherCoord c` on `escapeOpen c`, then `‖β‖ = exp(G_c)` on the
whole basin.  Proof: the ρ-tower branch `β₀` (`exists_global_branch_modulus_of_mem_mandelbrot`)
carries the modulus; `β` and `β₀` both agree with `bottcherCoord c` on the open set `escapeOpen c`,
so they are eventually equal at a deep point, and the identity theorem on the preconnected basin
`(isPreconnected_compl_filledJulia)` forces `β = β₀` throughout. -/
theorem branch_modulus_of_mem_mandelbrot {c : ℂ} (hc : c ∈ mandelbrot) {β : ℂ → ℂ}
    (hβan : AnalyticOnNhd ℂ β (filledJulia c)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c, β z = bottcherCoord c z) :
    ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z) := by
  obtain ⟨β₀, hβ₀an, hβ₀esc, _hne, hβ₀mod, _, _, _⟩ :=
    exists_global_branch_modulus_of_mem_mandelbrot c hc
  set z₀ : ℂ := (↑(max 2 ‖c‖ + 1) : ℂ) with hz₀def
  have hz₀ : z₀ ∈ escapeOpen c := deepPoint_mem_escapeOpen c
  have heq : Set.EqOn β β₀ (filledJulia c)ᶜ := by
    refine hβan.eqOn_of_preconnected_of_eventuallyEq hβ₀an
      (isPreconnected_compl_filledJulia c) (escapeOpen_subset_compl_filledJulia c hz₀) ?_
    have hop : (escapeOpen c) ∈ 𝓝 z₀ := (isOpen_escapeOpen c).mem_nhds hz₀
    filter_upwards [hop] with z hz
    rw [hβesc z hz, hβ₀esc z hz]
  intro z hz
  rw [heq hz]; exact hβ₀mod z hz

/-- **Connected repelling-cycle contradiction without the modulus hypothesis (`c ∈ mandelbrot`).**
Same as `false_of_repelling_branch_global_modulus`, but the Böttcher-modulus hypothesis `hβmod` is
discharged internally from `c ∈ mandelbrot` via `branch_modulus_of_mem_mandelbrot`.  So a downstream
supplier of the connected transcendence contradiction only has to produce the analytic
escapeOpen-anchored branch and the repelling non-resonant periodic datum — never the modulus. -/
theorem false_of_repelling_branch_mem_mandelbrot {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {c₁ : ℂ}
    {z₀ w₀ d lam : ℂ} {p : ℕ} {β : ℂ → ℂ}
    (hc₁ : c₁ ∈ mandelbrot)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (ha : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀)
    (hroot : ∑ i ∈ s, a i z₀ * w₀ ^ i = 0)
    (hpartial : HasDerivAt (fun w => ∑ i ∈ s, a i z₀ * w ^ i) d w₀) (hd : d ≠ 0)
    (hz₀ : z₀ ∈ filledJulia c₁)
    (hNeBot : (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot)
    (hβlim : Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀))
    (hβrel : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, ∑ i ∈ s, a i z * (β z) ^ i = 0)
    (hβne : ∃ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, β z ≠ w₀)
    (hFz : (quadratic c₁)^[p] z₀ = z₀)
    (hlam : HasDerivAt ((quadratic c₁)^[p]) lam z₀)
    (hres : ∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ)) :
    False :=
  false_of_repelling_branch_global_modulus hβan hβesc
    (branch_modulus_of_mem_mandelbrot hc₁ hβan hβesc)
    ha hroot hpartial hd hz₀ hNeBot hβlim hβrel hβne hFz hlam hres

/-- **Non-resonance is automatic for a strongly repelling multiplier.**  If the periodic multiplier
`lam` satisfies `2^p < ‖lam‖` (strongly repelling for period `p`), then `lam^m ≠ 2^p` for every
`m ≥ 1`.  Indeed `‖lam^m‖ > 2^{pm} ≥ 2^p = ‖(2^p : ℂ)‖`, so the two can never be equal.  This turns the
resonance-avoidance clause `hres` into the single scalar inequality `2^p < ‖lam‖`. -/
theorem resonance_free_of_strongly_repelling {lam : ℂ} {p : ℕ} (h : (2 ^ p : ℝ) < ‖lam‖) :
    ∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ) := by
  intro m hm hcontra
  have h1 : (2 ^ (p * m) : ℝ) < ‖lam ^ m‖ := strong_repelling_norm_pow hm h
  rw [hcontra] at h1
  have hnorm : ‖((2 ^ p : ℕ) : ℂ)‖ = (2 ^ p : ℝ) := by
    rw [Complex.norm_natCast]; push_cast; ring
  rw [hnorm] at h1
  have hle : (2 ^ p : ℝ) ≤ (2 ^ (p * m) : ℝ) :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_mul_of_pos_right p (by omega))
  linarith

/-- **Connected repelling-cycle contradiction from a strongly repelling cycle (`c ∈ mandelbrot`).**
Combines `false_of_repelling_branch_mem_mandelbrot` with `resonance_free_of_strongly_repelling`: the
resonance-avoidance hypothesis is replaced by the single inequality `2^p < ‖lam‖`.  So the entire
connected repelling contradiction is now driven by: the analytic escapeOpen-anchored branch, the
periodic point data, and the *strong* repulsion of its multiplier — exactly the `strong` density lane
(`dense_strongly_repelling_periodic_of_forall_frontier_ball`).  The modulus and non-resonance
obligations are both discharged here. -/
theorem false_of_strongly_repelling_branch_mem_mandelbrot {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {c₁ : ℂ}
    {z₀ w₀ d lam : ℂ} {p : ℕ} {β : ℂ → ℂ}
    (hc₁ : c₁ ∈ mandelbrot)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (ha : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀)
    (hroot : ∑ i ∈ s, a i z₀ * w₀ ^ i = 0)
    (hpartial : HasDerivAt (fun w => ∑ i ∈ s, a i z₀ * w ^ i) d w₀) (hd : d ≠ 0)
    (hz₀ : z₀ ∈ filledJulia c₁)
    (hNeBot : (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot)
    (hβlim : Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀))
    (hβrel : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, ∑ i ∈ s, a i z * (β z) ^ i = 0)
    (hβne : ∃ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, β z ≠ w₀)
    (hFz : (quadratic c₁)^[p] z₀ = z₀)
    (hlam : HasDerivAt ((quadratic c₁)^[p]) lam z₀)
    (hstrong : (2 ^ p : ℝ) < ‖lam‖) :
    False :=
  false_of_repelling_branch_mem_mandelbrot hc₁ hβan hβesc ha hroot hpartial hd hz₀ hNeBot
    hβlim hβrel hβne hFz hlam (resonance_free_of_strongly_repelling hstrong)

end Bottcher
