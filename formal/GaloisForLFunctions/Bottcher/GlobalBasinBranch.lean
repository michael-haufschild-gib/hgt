/-
# The global basin Böttcher branch closes the connected dendrite case

`GreenLogDeriv.exists_fullBottcherBranch_rightHalfplane` constructs the continued Böttcher coordinate
`β` (with modulus `‖β‖ = exp G_c` and the hypothetical algebraic relation) UNCONDITIONALLY on the convex
right half-plane `R = {Re z > M}` — the `hF`/primitive hypothesis is eliminated there. The remaining gap
to a *closed* connected-case contradiction is purely geometric: a single-valued analytic `β` on the WHOLE
(now known preconnected) basin `Ω_c = (K_c)ᶜ`, reaching a dendrite Julia point along a connected basin
sector.

This file does the entire assembly that consumes such a `β`. It shows: once `β` is analytic and
nonvanishing on `Ω_c` and merely matches the Böttcher modulus / relation on the **far field**
`escapeOpen` (where `β = φ_c`), then
  * the modulus `‖β‖ = exp G_c` spreads to ALL of `Ω_c` — `norm_eq_exp_green_of_eqOn_open` over the
    preconnected basin `isPreconnected_compl_filledJulia`;
  * the relation spreads to ALL of `Ω_c` — the analytic identity theorem on the preconnected basin;
  * at a **dendrite tip** `z₀` (a Julia point with empty `K_c`-interior nearby whose punctured basin
    sectors `ball z₀ ρ ∩ Ω_c` are connected) `β` follows one analytic root-branch of the relation
    (`dendrite_branch_limit`), giving the boundary limit `w₀`, a simple root;
  * `false_of_basin_branch_dendrite` (the Green-modulus natural boundary) closes it.

So the connected dendrite sub-case is reduced to exactly two clean inputs, both stated here as hypotheses
of `false_of_global_basin_branch`:
  (G) a global single-valued analytic nonvanishing `β` on `Ω_c` (the basin-wide continuation of `φ_c`),
  (T) a dendrite tip `z₀` whose small punctured basin neighbourhoods are preconnected,
together with the generic fibre nondegeneracy at `z₀` (full degree + separable — automatic off the finite
discriminant locus, hence on the uncountable dendrite). Everything between those inputs and `False` is now
machine-checked.
-/
import GaloisForLFunctions.Bottcher.ConnectedTranscendence
import GaloisForLFunctions.Bottcher.GreenLogDeriv
import GaloisForLFunctions.Bottcher.BasinConnected

open Complex Set Topology Filter Metric

namespace Bottcher

/-- `escapeOpen c ⊆ (K_c)ᶜ`: the far field is in the basin. -/
theorem escapeOpen_subset_compl_filledJulia (c : ℂ) : escapeOpen c ⊆ (filledJulia c)ᶜ := by
  intro z hz
  exact not_mem_filledJulia (mem_escapeOpen_regime hz).1 (mem_escapeOpen_regime hz).2

/-- A concrete far-field point `R₀ := max 2 ‖c‖ + 1 ∈ escapeOpen c` (real, large). -/
theorem deepPoint_mem_escapeOpen (c : ℂ) :
    ((max 2 ‖c‖ + 1 : ℝ) : ℂ) ∈ escapeOpen c := by
  show max 2 ‖c‖ < ‖((max 2 ‖c‖ + 1 : ℝ) : ℂ)‖
  have hpos : 0 ≤ max 2 ‖c‖ + 1 := by have : (0:ℝ) ≤ max 2 ‖c‖ := le_trans (by norm_num) (le_max_left _ _); linarith
  rw [Complex.norm_real, Real.norm_of_nonneg hpos]; linarith

/-- **Global modulus from the far field.** A `β` analytic and nonvanishing on the basin `Ω_c`, with the
Böttcher modulus `‖β‖ = exp G_c` merely on `escapeOpen`, has it on ALL of `Ω_c`. (`log‖β‖ − G_c` is
harmonic, vanishes on the open far field, so by the identity theorem over the preconnected basin
`isPreconnected_compl_filledJulia` it vanishes everywhere on `Ω_c`.) -/
theorem norm_eq_exp_green_basin {c : ℂ} {β : ℂ → ℂ}
    (hβan : AnalyticOnNhd ℂ β (filledJulia c)ᶜ) (hβ0 : ∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0)
    (hβmodE : ∀ z ∈ escapeOpen c, ‖β z‖ = Real.exp (greenFunctionDyn c z)) :
    ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenLimit c z) := by
  refine norm_eq_exp_green_of_eqOn_open (isPreconnected_compl_filledJulia c) (subset_refl _)
    hβan hβ0 (isOpen_escapeOpen c) (escapeOpen_subset_compl_filledJulia c)
    (deepPoint_mem_escapeOpen c) ?_
  intro z hz
  rw [hβmodE z hz, greenFunctionDyn, if_neg (escapeOpen_subset_compl_filledJulia c hz)]

/-- **Global relation from the far field.** A `β` analytic on the basin satisfying the algebraic relation
`∑ᵢ (P.coeff i)(z)·(β z)ⁱ = 0` on `escapeOpen` satisfies it on ALL of `Ω_c` — the relation function is
analytic (`analyticOnNhd_relation`), vanishes on the open far field, hence by the identity theorem on the
preconnected basin vanishes everywhere on `Ω_c`. -/
theorem relation_eq_zero_basin {c : ℂ} {β : ℂ → ℂ} (P : Polynomial (Polynomial ℂ))
    (hβan : AnalyticOnNhd ℂ β (filledJulia c)ᶜ)
    (hβrelE : ∀ z ∈ escapeOpen c, ∑ i ∈ P.support, (P.coeff i).aeval z * (β z) ^ i = 0) :
    ∀ z ∈ (filledJulia c)ᶜ, ∑ i ∈ P.support, (P.coeff i).aeval z * (β z) ^ i = 0 := by
  have hrelan : AnalyticOnNhd ℂ
      (fun z => ∑ i ∈ P.support, (P.coeff i).aeval z * (β z) ^ i) (filledJulia c)ᶜ :=
    analyticOnNhd_relation hβan P
  have hev : (fun z => ∑ i ∈ P.support, (P.coeff i).aeval z * (β z) ^ i) =ᶠ[𝓝 ((max 2 ‖c‖ + 1 : ℝ) : ℂ)]
      (fun _ => (0 : ℂ)) := by
    filter_upwards [(isOpen_escapeOpen c).mem_nhds (deepPoint_mem_escapeOpen c)] with z hz
    exact hβrelE z hz
  intro z hz
  exact (hrelan.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    (isPreconnected_compl_filledJulia c)
    (escapeOpen_subset_compl_filledJulia c (deepPoint_mem_escapeOpen c)) hev) hz

/-- **The connected dendrite sub-case is closed by a global basin branch.** Suppose, for a relation `P`:

* `(G)` `β` is analytic and nonvanishing on the basin `Ω_c = (K_c)ᶜ`, matching the Böttcher modulus and
  the relation on the far field `escapeOpen` (i.e. `β` is the basin-wide single-valued continuation of
  `φ_c` — the genuine remaining analytic input, an unconditional half-plane version of which is
  `exists_fullBottcherBranch_rightHalfplane`);
* `(T)` `z₀` is a dendrite Julia point (`z₀ ∈ K_c`, `ball z₀ r ∩ interior K_c = ∅`) that is a **tip**: its
  small punctured basin neighbourhoods `ball z₀ ρ ∩ Ω_c` are preconnected (`htip`);
* the fibre `P.map(eval z₀)` is nondegenerate (full degree `hlead` and separable `hsep`) — automatic off
  the finite discriminant locus, hence at uncountably many dendrite points.

Then `False`. The modulus and relation spread from `escapeOpen` to all of `Ω_c`
(`norm_eq_exp_green_basin`, `relation_eq_zero_basin`); on a connected basin sector at `z₀` the branch
family (`exists_branch_family`) and `dendrite_branch_limit` give `β` a definite analytic branch and a
simple-root boundary limit `w₀`; `false_of_basin_branch_dendrite` then derives `False` from the
Green-modulus natural boundary. -/
theorem false_of_global_basin_branch {c : ℂ} (P : Polynomial (Polynomial ℂ))
    {β : ℂ → ℂ}
    (hβan : AnalyticOnNhd ℂ β (filledJulia c)ᶜ) (hβ0 : ∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0)
    (hβmodE : ∀ z ∈ escapeOpen c, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    (hβrelE : ∀ z ∈ escapeOpen c, ∑ i ∈ P.support, (P.coeff i).aeval z * (β z) ^ i = 0)
    {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (hz₀ : z₀ ∈ filledJulia c)
    (hempty : Metric.ball z₀ r ∩ interior (filledJulia c) = ∅)
    (htip : ∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c)ᶜ))
    (hN1 : 1 ≤ P.natDegree)
    (hlead : (P.coeff P.natDegree).eval z₀ ≠ 0)
    (hsep : (P.map (Polynomial.evalRingHom z₀)).Separable) :
    False := by
  -- modulus & relation, spread to the whole basin
  have hmodG : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenLimit c z) :=
    norm_eq_exp_green_basin hβan hβ0 hβmodE
  have hmod_basin : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z) := by
    intro z hz; rw [hmodG z hz, greenFunctionDyn, if_neg hz]
  have hrel_basin : ∀ z ∈ (filledJulia c)ᶜ, ∑ i ∈ P.support, (P.coeff i).aeval z * (β z) ^ i = 0 :=
    relation_eq_zero_basin P hβan hβrelE
  -- the basin is dense at `z₀` (it is a Julia point not in the interior of `K_c`)
  have hz₀int : z₀ ∉ interior (filledJulia c) := fun h => by
    have : z₀ ∈ Metric.ball z₀ r ∩ interior (filledJulia c) := ⟨mem_ball_self hr, h⟩
    rwa [hempty] at this
  have hNeBot : (𝓝[(filledJulia c)ᶜ] z₀).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (by rw [closure_compl]; exact hz₀int)
  -- the analytic branch family of the separable fibre at `z₀`
  obtain ⟨r', w, hr', hwc, hwsep, hwdeg, hwrel⟩ := exists_branch_family hN1 hlead hsep
  -- work on a connected basin sector inside both balls
  set ρ : ℝ := min r r' with hρdef
  have hρ : 0 < ρ := lt_min hr hr'
  have hρr' : ρ ≤ r' := min_le_right _ _
  set U : Set ℂ := Metric.ball z₀ ρ ∩ (filledJulia c)ᶜ with hUdef
  have hUball : U ⊆ Metric.ball z₀ r' := fun z hz => Metric.ball_subset_ball hρr' hz.1
  have hUbasin : U ⊆ (filledJulia c)ᶜ := inter_subset_right
  have hUc : IsPreconnected U := htip ρ hρ
  have hUnhds : U ∈ 𝓝[(filledJulia c)ᶜ] z₀ := by
    have h := inter_mem_nhdsWithin ((filledJulia c)ᶜ) (Metric.ball_mem_nhds z₀ hρ)
    rwa [inter_comm] at h
  have hβcU : ContinuousOn β U := hβan.continuousOn.mono hUbasin
  have hβrelU : ∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (β z) ^ i = 0 :=
    fun z hz => hrel_basin z (hUbasin hz)
  obtain ⟨z₁, hz₁⟩ := hNeBot.nonempty_of_mem hUnhds
  -- the boundary limit along the basin
  obtain ⟨w₀, d, hroot, hpart, hd, htend⟩ :=
    dendrite_branch_limit hN1 hr' hsep w hwc hwsep hwdeg hwrel hUball hUbasin hUc hUnhds hβcU
      hβrelU hz₁
  -- the filter forms of the relation and modulus along `𝓝[basin] z₀`
  have hβrel_filt : ∀ᶠ z in 𝓝[(filledJulia c)ᶜ] z₀,
      ∑ i ∈ P.support, (P.coeff i).aeval z * (β z) ^ i = 0 :=
    Filter.eventually_of_mem self_mem_nhdsWithin hrel_basin
  have hβmod_filt : ∀ᶠ z in 𝓝[(filledJulia c)ᶜ] z₀, ‖β z‖ = Real.exp (greenFunctionDyn c z) :=
    Filter.eventually_of_mem self_mem_nhdsWithin hmod_basin
  exact false_of_basin_branch_dendrite P hr hz₀ hempty hroot hpart hd htend hβrel_filt hβmod_filt

end Bottcher
