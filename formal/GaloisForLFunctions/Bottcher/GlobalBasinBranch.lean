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

/-- **Unconditional full Böttcher branch on the half-plane to the right of a given maximiser.** If `z₀`
maximises `Re` over `K_c`, then `R = {Re z > z₀.re}` is convex and disjoint from `K_c`; the convex Poincaré
lemma builds the `ω`-primitive on `R` with NO hypothesis, giving a branch `β` with the Böttcher modulus and
(anchored on an escape ball in `R`) the relation. This is `exists_fullBottcherBranch_rightHalfplane` with the
threshold pinned to the chosen anchor `z₀.re` — eliminating the global-branch input `(G)` for the maximiser. -/
theorem exists_fullBottcherBranch_halfplane_at (c : ℂ) (P : Polynomial (Polynomial ℂ))
    (hrel : ∀ z ∈ escapeOpen c ∩ Complex.slitPlane,
        ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
    {z₀ : ℂ} (hz₀max : ∀ w ∈ filledJulia c, w.re ≤ z₀.re) :
    ∃ β : ℂ → ℂ,
      AnalyticOnNhd ℂ β {z | z₀.re < z.re} ∧ (∀ z, z₀.re < z.re → β z ≠ 0) ∧
      (∀ z, z₀.re < z.re → ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      (∀ z, z₀.re < z.re → ∑ i ∈ P.support, (P.coeff i).aeval z * (β z) ^ i = 0) := by
  set M : ℝ := z₀.re with hM
  set R : Set ℂ := {z | M < z.re} with hR
  have hRconv : Convex ℝ R := convex_halfSpace_re_gt M
  have hRo : IsOpen R := isOpen_lt continuous_const Complex.continuous_re
  have hRb : R ⊆ (filledJulia c)ᶜ := fun z hz hzK => absurd (hz₀max z hzK) (not_le.mpr hz)
  set MM : ℝ := max 2 ‖c‖ with hMM
  set T : ℝ := max M MM + 1 with hT
  have hTM : M < T := by have := le_max_left M MM; rw [hT]; linarith
  have hTMM : MM < T := by have := le_max_right M MM; rw [hT]; linarith
  have hTpos : 0 < T := by
    have h2 : (2 : ℝ) ≤ MM := le_max_left 2 ‖c‖
    have := le_max_right M MM; rw [hT]; linarith
  have hTmem : (T : ℂ) ∈ R ∩ escapeOpen c ∩ Complex.slitPlane := by
    refine ⟨⟨?_, ?_⟩, ofReal_mem_slitPlane.mpr hTpos⟩
    · show M < ((T : ℝ) : ℂ).re; rw [Complex.ofReal_re]; exact hTM
    · show MM < ‖((T : ℝ) : ℂ)‖; rw [Complex.norm_real, Real.norm_of_nonneg hTpos.le]; exact hTMM
  have hOpen : IsOpen (R ∩ escapeOpen c ∩ Complex.slitPlane) :=
    (hRo.inter (isOpen_escapeOpen c)).inter Complex.isOpen_slitPlane
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hOpen _ hTmem
  have hωdiff : DifferentiableOn ℂ (greenLogDeriv c) R := (differentiableOn_greenLogDeriv c).mono hRb
  obtain ⟨F, hF'⟩ := hRconv.exists_forall_hasDerivWithinAt hωdiff
  have hF : ∀ z ∈ R, HasDerivAt F (greenLogDeriv c z) z :=
    fun z hz => (hF' z hz).hasDerivAt (hRo.mem_nhds hz)
  obtain ⟨β, hβan, hβ0, hβmod, hβrel⟩ := exists_fullBottcherBranch_of_primitive hRo
    hRconv.isPreconnected hRb hF (E := Metric.ball (T : ℂ) ρ)
    (fun z hz => ((hball hz).1).1) (fun z hz => ⟨((hball hz).1).2, (hball hz).2⟩)
    Metric.isOpen_ball (convex_ball _ _).isPreconnected (Metric.mem_ball_self hρ) P
    (fun z hz => hrel z ⟨((hball hz).1).2, (hball hz).2⟩)
  exact ⟨β, hβan, hβ0, hβmod, hβrel⟩

/-- **The connected dendrite case, closed by the UNCONDITIONAL half-plane branch — no global branch.**
At the rightmost point `z₀` of `K_c` (`hz₀max`), in the dendrite case (`hempty`), assuming `z₀` is a tip
(its punctured basin neighbourhoods `ball z₀ ρ ∩ Ω_c` are preconnected, `htip`) and the fibre `P.map(eval z₀)`
is nondegenerate (`hlead`, `hsep`), the algebraic relation `P(z, φ_c) = 0` is impossible. Mechanism: the
unconditional half-plane branch `β` (`exists_fullBottcherBranch_halfplane_at`) lives on `R = {Re z > z₀.re}`;
on the convex sector `UR = R ∩ ball z₀ r₁` it follows one analytic root-branch `w k` of the relation
(`eqOn_branch_of_relation`), giving a boundary value `w₀ = w k z₀` with `‖w₀‖ ≥ 1 > 0`; the algebraic branch
`g` across `z₀` (`exists_analyticAt_branch_poly`) matches `β` on an open piece of `UR`
(`branch_unique_poly_within`), so `‖g‖ = exp G_c` there, and `norm_eq_exp_green_of_eqOn_open` spreads this
across the preconnected basin sector `ball z₀ r₀ ∩ Ω_c`; `no_continuation_dendrite` (Green-modulus natural
boundary) closes it. This discharges the connected dendrite sub-case to PURELY geometric inputs
(`hempty`, `htip`) plus generic fibre nondegeneracy — the analytic primitive `hF` is gone. -/
theorem false_of_halfplane_dendrite (c : ℂ) (P : Polynomial (Polynomial ℂ))
    (hrelE : ∀ z ∈ escapeOpen c ∩ Complex.slitPlane,
        ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
    {z₀ : ℂ} (hz₀K : z₀ ∈ filledJulia c) (hz₀max : ∀ w ∈ filledJulia c, w.re ≤ z₀.re)
    {r : ℝ} (hr : 0 < r)
    (hempty : Metric.ball z₀ r ∩ interior (filledJulia c) = ∅)
    (htip : ∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c)ᶜ))
    (hN1 : 1 ≤ P.natDegree)
    (hlead : (P.coeff P.natDegree).eval z₀ ≠ 0)
    (hsep : (P.map (Polynomial.evalRingHom z₀)).Separable) :
    False := by
  classical
  obtain ⟨β, hβan, hβ0, hβmod, hβrel⟩ := exists_fullBottcherBranch_halfplane_at c P hrelE hz₀max
  set M : ℝ := z₀.re with hM
  set R : Set ℂ := {z | M < z.re} with hRdef
  have hRo : IsOpen R := isOpen_lt continuous_const Complex.continuous_re
  have hRconv : Convex ℝ R := convex_halfSpace_re_gt M
  have hRbasin : R ⊆ (filledJulia c)ᶜ := fun z hz hzK => absurd (hz₀max z hzK) (not_le.mpr hz)
  have sector_pt : ∀ (W : Set ℂ) (ρ : ℝ), z₀ ∈ W → IsOpen W → 0 < ρ →
      ∃ p, p ∈ W ∧ p ∈ ball z₀ ρ ∧ M < p.re := by
    intro W ρ hzW hWo hρ
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hWo z₀ hzW
    set s : ℝ := min ε ρ / 2 with hsdef
    have hspos : 0 < s := by rw [hsdef]; positivity
    have hsnorm : ‖(z₀ + (s : ℂ)) - z₀‖ = s := by
      rw [show z₀ + (s : ℂ) - z₀ = (s : ℂ) by ring, Complex.norm_real, Real.norm_of_nonneg hspos.le]
    refine ⟨z₀ + (s : ℂ), ?_, ?_, ?_⟩
    · refine hεW ?_
      rw [mem_ball, dist_eq_norm, hsnorm, hsdef]; have := min_le_left ε ρ; linarith
    · rw [mem_ball, dist_eq_norm, hsnorm, hsdef]; have := min_le_right ε ρ; linarith
    · show M < (z₀ + (s : ℂ)).re
      rw [Complex.add_re, Complex.ofReal_re]; linarith
  obtain ⟨rbf, w, hrbf, hwc, hwsep, hwdeg, hwrel⟩ := exists_branch_family hN1 hlead hsep
  set r₁ : ℝ := min r rbf with hr1def
  have hr1 : 0 < r₁ := lt_min hr hrbf
  have hr1r : r₁ ≤ r := min_le_left _ _
  have hr1bf : r₁ ≤ rbf := min_le_right _ _
  set UR : Set ℂ := R ∩ ball z₀ r₁ with hURdef
  have hURc : IsPreconnected UR := (hRconv.inter (convex_ball _ _)).isPreconnected
  have hURball : UR ⊆ ball z₀ rbf := fun z hz => ball_subset_ball hr1bf hz.2
  obtain ⟨z₁, _, hz₁ball, hz₁R⟩ := sector_pt univ r₁ (mem_univ _) isOpen_univ hr1
  have hz₁UR : z₁ ∈ UR := ⟨hz₁R, hz₁ball⟩
  have hwcUR : ∀ k, ContinuousOn (w k) UR := fun k => (hwc k).mono hURball
  have hwsepUR : ∀ z ∈ UR, ∀ k l, k ≠ l → w k z ≠ w l z := fun z hz => hwsep z (hURball hz)
  have hwdegUR : ∀ z ∈ UR, (P.map (Polynomial.evalRingHom z)).natDegree = P.natDegree :=
    fun z hz => hwdeg z (hURball hz)
  have hwrelUR : ∀ k, ∀ z ∈ UR, ∑ i ∈ P.support, (P.coeff i).aeval z * (w k z) ^ i = 0 :=
    fun k z hz => hwrel k z (hURball hz)
  have hβrelUR : ∀ z ∈ UR, ∑ i ∈ P.support, (P.coeff i).aeval z * (β z) ^ i = 0 :=
    fun z hz => hβrel z hz.1
  have hβcUR : ContinuousOn β UR := hβan.continuousOn.mono (fun z hz => hz.1)
  obtain ⟨k, hk⟩ :=
    eqOn_branch_of_relation hN1 w β hURc hwcUR hβcUR hwsepUR hwdegUR hwrelUR hβrelUR hz₁UR
  set w₀ : ℂ := w k z₀ with hw0def
  have hz0ballbf : z₀ ∈ ball z₀ rbf := mem_ball_self hrbf
  have hwkAt : ContinuousAt (w k) z₀ := (hwc k).continuousAt (ball_mem_nhds z₀ hrbf)
  have htend : Tendsto β (𝓝[UR] z₀) (𝓝 w₀) := tendsto_within_of_eqOn hwkAt hk
  have hz0clUR : z₀ ∈ closure UR := by
    rw [Metric.mem_closure_iff]
    intro δ hδ
    obtain ⟨p, _, hpball, hpR⟩ := sector_pt univ (min δ r₁) (mem_univ _) isOpen_univ (lt_min hδ hr1)
    exact ⟨p, ⟨hpR, ball_subset_ball (min_le_right δ r₁) hpball⟩, by
      rw [dist_comm]; exact lt_of_lt_of_le (mem_ball.mp hpball) (min_le_left δ r₁)⟩
  haveI hURne : (𝓝[UR] z₀).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hz0clUR
  have hβmodge : ∀ᶠ z in 𝓝[UR] z₀, (1 : ℝ) ≤ ‖β z‖ :=
    Filter.eventually_of_mem self_mem_nhdsWithin (fun z hz => by
      rw [hβmod z hz.1]; exact Real.one_le_exp (greenFunctionDyn_nonneg c z))
  have hw0ge : (1 : ℝ) ≤ ‖w₀‖ := ge_of_tendsto htend.norm hβmodge
  have hw0ne : w₀ ≠ 0 := fun h => by rw [h, norm_zero] at hw0ge; linarith
  have hrootQ : (P.map (Polynomial.evalRingHom z₀)).eval w₀ = 0 := by
    rw [← relation_eq_eval_map]; exact hwrel k z₀ hz0ballbf
  have hroot : ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w₀ ^ i = 0 := by
    rw [relation_eq_eval_map]; exact hrootQ
  have hpart : HasDerivAt (fun y => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * y ^ i)
      ((P.map (Polynomial.evalRingHom z₀)).derivative.eval w₀) w₀ := relation_hasDerivAt_w P z₀ w₀
  have hd : (P.map (Polynomial.evalRingHom z₀)).derivative.eval w₀ ≠ 0 :=
    eval_derivative_ne_zero_of_separable hsep hrootQ
  obtain ⟨g, hgAt, hgz₀, hgrel⟩ := exists_analyticAt_branch_poly P hroot hpart hd
  have hg1t : ContinuousAt g z₀ := hgAt.continuousAt
  have hrel1 : ∀ᶠ z in 𝓝[UR] z₀, ∑ i ∈ P.support, (P.coeff i).aeval z * (g z) ^ i = 0 :=
    hgrel.filter_mono nhdsWithin_le_nhds
  have hrel2 : ∀ᶠ z in 𝓝[UR] z₀, ∑ i ∈ P.support, (P.coeff i).aeval z * (β z) ^ i = 0 :=
    Filter.eventually_of_mem self_mem_nhdsWithin hβrelUR
  have hmatch : ∀ᶠ z in 𝓝[UR] z₀, g z = β z :=
    branch_unique_poly_within P hpart hd hg1t hgz₀ htend hrel1 hrel2
  have hgz0ne : g z₀ ≠ 0 := by rw [hgz₀]; exact hw0ne
  obtain ⟨rg, hrg, hgne⟩ := Metric.eventually_nhds_iff.mp (hg1t.eventually_ne hgz0ne)
  obtain ⟨ra, hra, hgan1⟩ := Metric.eventually_nhds_iff.mp hgAt.eventually_analyticAt
  set r₀ : ℝ := min r₁ (min rg ra) with hr0def
  have hr0 : 0 < r₀ := lt_min hr1 (lt_min hrg hra)
  have hr0r₁ : r₀ ≤ r₁ := min_le_left _ _
  have hr0rg : r₀ ≤ rg := le_trans (min_le_right _ _) (min_le_left _ _)
  have hr0ra : r₀ ≤ ra := le_trans (min_le_right _ _) (min_le_right _ _)
  have hr0r : r₀ ≤ r := le_trans hr0r₁ hr1r
  have hgan0 : AnalyticOnNhd ℂ g (ball z₀ r₀) := fun z hz =>
    hgan1 (lt_of_lt_of_le (mem_ball.mp hz) hr0ra)
  have hg0ball : ∀ z ∈ ball z₀ r₀, g z ≠ 0 := fun z hz =>
    hgne (lt_of_lt_of_le (mem_ball.mp hz) hr0rg)
  obtain ⟨O, hOo, hz₀O, hOsub⟩ := mem_nhdsWithin.mp hmatch
  set V : Set ℂ := (O ∩ ball z₀ r₀) ∩ R with hVdef
  have hVo : IsOpen V := (hOo.inter isOpen_ball).inter hRo
  have hVsubUR : V ⊆ UR := fun z hz => ⟨hz.2, ball_subset_ball hr0r₁ hz.1.2⟩
  have hVeqgβ : ∀ z ∈ V, g z = β z := fun z hz => hOsub ⟨hz.1.1, hVsubUR hz⟩
  obtain ⟨v, hvW, _, hvR⟩ := sector_pt (O ∩ ball z₀ r₀) r₀
    ⟨hz₀O, mem_ball_self hr0⟩ (hOo.inter isOpen_ball) hr0
  have hvV : v ∈ V := ⟨hvW, hvR⟩
  have hVmod : ∀ z ∈ V, ‖g z‖ = Real.exp (greenLimit c z) := by
    intro z hz
    rw [hVeqgβ z hz, hβmod z hz.2, greenFunctionDyn, if_neg (hRbasin hz.2)]
  set Ubig : Set ℂ := ball z₀ r₀ ∩ (filledJulia c)ᶜ with hUbigdef
  have hUbigc : IsPreconnected Ubig := htip r₀ hr0
  have hUbigbasin : Ubig ⊆ (filledJulia c)ᶜ := inter_subset_right
  have hganUbig : AnalyticOnNhd ℂ g Ubig := hgan0.mono inter_subset_left
  have hg0Ubig : ∀ z ∈ Ubig, g z ≠ 0 := fun z hz => hg0ball z (inter_subset_left hz)
  have hVUbig : V ⊆ Ubig := fun z hz => ⟨hz.1.2, hRbasin hz.2⟩
  have hmodG : ∀ z ∈ Ubig, ‖g z‖ = Real.exp (greenLimit c z) :=
    norm_eq_exp_green_of_eqOn_open hUbigc hUbigbasin hganUbig hg0Ubig hVo hVUbig hvV hVmod
  have hempty0 : ball z₀ r₀ ∩ interior (filledJulia c) = ∅ := by
    refine eq_empty_of_subset_empty ?_
    rw [← hempty]
    exact inter_subset_inter_left _ (ball_subset_ball hr0r)
  have hmod_basin : ∀ z ∈ ball z₀ r₀, z ∉ filledJulia c →
      ‖g z‖ = Real.exp (greenFunctionDyn c z) := by
    intro z hz hzK
    rw [hmodG z ⟨hz, hzK⟩, greenFunctionDyn, if_neg hzK]
  have hbasin : ∃ z ∈ ball z₀ r₀, z ∉ filledJulia c :=
    ⟨v, (hVUbig hvV).1, (hVUbig hvV).2⟩
  exact no_continuation_dendrite hr0 hgan0 hz₀K hempty0 hmod_basin hbasin

/-- **The half-plane dendrite contradiction with the rightmost anchor created internally.** The caller no
longer chooses the anchor point: compactness of `K_c` gives a rightmost point, and
`false_of_halfplane_dendrite` builds the unconditional half-plane branch from that point.  The remaining
input is exactly the local dendrite-tip and fibre-nondegeneracy package at whichever rightmost point Lean
selects. -/
theorem false_of_rightmost_halfplane_dendrite (c : ℂ) (P : Polynomial (Polynomial ℂ))
    (hrelE : ∀ z ∈ escapeOpen c ∩ Complex.slitPlane,
        ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
    (hN1 : 1 ≤ P.natDegree)
    (hinput : ∀ z₀ : ℂ, z₀ ∈ filledJulia c →
        (∀ w ∈ filledJulia c, w.re ≤ z₀.re) →
        ∃ r : ℝ, 0 < r ∧
          Metric.ball z₀ r ∩ interior (filledJulia c) = ∅ ∧
          (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c)ᶜ)) ∧
          (P.coeff P.natDegree).eval z₀ ≠ 0 ∧
          (P.map (Polynomial.evalRingHom z₀)).Separable) :
    False := by
  obtain ⟨z₀, hz₀K, hz₀max⟩ := exists_rightmost_filledJulia c
  obtain ⟨r, hr, hempty, htip, hlead, hsep⟩ := hinput z₀ hz₀K hz₀max
  exact false_of_halfplane_dendrite c P hrelE hz₀K hz₀max hr hempty htip hN1 hlead hsep

/-- **Rightmost half-plane dendrite contradiction in the empty-interior case.** This creates the local
dendrite ball and the frontier fact internally: the chosen rightmost point is on `frontier K_c`, and
`interior K_c = ∅` gives `ball z₀ 1 ∩ interior K_c = ∅`.  The remaining caller input is only the punctured
basin-sector preconnectedness and fibre nondegeneracy at that rightmost frontier point. -/
theorem false_of_rightmost_halfplane_dendrite_emptyInterior (c : ℂ)
    (P : Polynomial (Polynomial ℂ))
    (hrelE : ∀ z ∈ escapeOpen c ∩ Complex.slitPlane,
        ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
    (hempty : interior (filledJulia c) = ∅)
    (hN1 : 1 ≤ P.natDegree)
    (hinput : ∀ z₀ : ℂ, z₀ ∈ frontier (filledJulia c) →
        (∀ w ∈ filledJulia c, w.re ≤ z₀.re) →
        (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c)ᶜ)) ∧
          (P.coeff P.natDegree).eval z₀ ≠ 0 ∧
          (P.map (Polynomial.evalRingHom z₀)).Separable) :
    False := by
  refine false_of_rightmost_halfplane_dendrite c P hrelE hN1 ?_
  intro z₀ hz₀K hz₀max
  have hfront : z₀ ∈ frontier (filledJulia c) :=
    rightmost_mem_frontier_filledJulia hz₀K hz₀max
  obtain ⟨htip, hlead, hsep⟩ := hinput z₀ hfront hz₀max
  refine ⟨1, by norm_num, ?_, htip, hlead, hsep⟩
  rw [hempty, inter_empty]

end Bottcher
