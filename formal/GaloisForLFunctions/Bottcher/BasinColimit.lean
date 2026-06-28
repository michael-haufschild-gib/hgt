/-
# Basin-branch colimit assembly: from the far-field anchor toward the cycle point

The index route consumes, on a basin sector at a repelling cycle point, a single branch `β` of `φ_c`
carrying the Böttcher functional equation `β(f^[p] z) = (β z)^{2^p}` and the algebraic relation. The
local form is `BasinBranchGlue.explicitBranch_FE_relation_of_anchor`, which needs an OPEN far-field
anchor `W ⊆ V` where `explicitBranch c n = explicitBranch c (n+p) = bottcherCoord c` (the `ζ = 1`
sheet). `PolyAsymptotic.eventually_explicitBranch_eq_bottcherCoord_real` gives that equality along the
real ray; here it is upgraded to an **open ball** anchor.

* `exists_farfield_anchor_ball` — a ball around a far real point inside `explicitDomain c n ∩
  explicitDomain c (n+p) ∩ escapeOpen c` where both levels equal `bottcherCoord c`.

New file (hRigid / connected lane, the basin-branch colimit launch pad).
-/
import GaloisForLFunctions.Bottcher.PolyAsymptotic
import GaloisForLFunctions.Bottcher.BasinBranchGlue
import GaloisForLFunctions.Bottcher.GlobalBasinBranch
import GaloisForLFunctions.Bottcher.Winding
import GaloisForLFunctions.Bottcher.RelativeBasinBranch
import GaloisForLFunctions.Bottcher.RelativeBranchFamily
import GaloisForLFunctions.Bottcher.BasinConnected
import GaloisForLFunctions.Bottcher.GreenContinuity
import GaloisForLFunctions.Bottcher.AnalyticRoot

open Complex Set Filter Topology Bornology Metric

namespace Bottcher

/-- **An open far-field anchor ball.** There is a real far point `(t:ℂ)` and a ball around it inside
`explicitDomain c n ∩ explicitDomain c (n+p) ∩ escapeOpen c` on which BOTH levels `n` and `n+p` of the
explicit branch equal `bottcherCoord c`. This discharges the open-anchor inputs (`hWo`, `hanchorN`,
`hanchorNP`) of `explicitBranch_FE_relation_of_anchor` with a genuinely open, preconnected `W`: pick a
far real `t` satisfying all five eventually-facts (both domains, escape, both branch equalities); the
intersection is open, so a ball fits; `explicitBranch_eq_bottcherCoord_of_anchor` spreads each
equality across the (convex, hence preconnected) ball from its centre. -/
theorem exists_farfield_anchor_ball (c : ℂ) (n p : ℕ) :
    ∃ (z₁ : ℂ) (ρ : ℝ), 0 < ρ ∧ IsPreconnected (Metric.ball z₁ ρ) ∧
      Metric.ball z₁ ρ ⊆ explicitDomain c n ∧
      Metric.ball z₁ ρ ⊆ explicitDomain c (n + p) ∧
      Metric.ball z₁ ρ ⊆ escapeOpen c ∧
      (∀ z ∈ Metric.ball z₁ ρ, explicitBranch c n z = bottcherCoord c z) ∧
      (∀ z ∈ Metric.ball z₁ ρ, explicitBranch c (n + p) z = bottcherCoord c z) := by
  have hesc : ∀ᶠ t : ℝ in atTop, (t : ℂ) ∈ escapeOpen c := by
    filter_upwards [eventually_gt_atTop (max 2 ‖c‖), eventually_gt_atTop (0:ℝ)] with t ht htpos
    show max 2 ‖c‖ < ‖(t:ℂ)‖
    rwa [Complex.norm_real, Real.norm_of_nonneg htpos.le]
  obtain ⟨t, hdn, hdnp, hesct, hebn, hebnp⟩ :=
    ((eventually_ofReal_mem_explicitDomain c n).and
     ((eventually_ofReal_mem_explicitDomain c (n + p)).and
      (hesc.and
       ((eventually_explicitBranch_eq_bottcherCoord_real c n).and
        (eventually_explicitBranch_eq_bottcherCoord_real c (n + p)))))).exists
  set O : Set ℂ := explicitDomain c n ∩ explicitDomain c (n + p) ∩ escapeOpen c with hOdef
  have hOopen : IsOpen O :=
    ((isOpen_explicitDomain c n).inter (isOpen_explicitDomain c (n + p))).inter (isOpen_escapeOpen c)
  have htO : (t : ℂ) ∈ O := ⟨⟨hdn, hdnp⟩, hesct⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hOopen _ htO
  have hballPc : IsPreconnected (Metric.ball (t:ℂ) ρ) := (convex_ball _ _).isPreconnected
  have hbn : Metric.ball (t:ℂ) ρ ⊆ explicitDomain c n := fun z hz => ((hball hz).1).1
  have hbnp : Metric.ball (t:ℂ) ρ ⊆ explicitDomain c (n + p) := fun z hz => ((hball hz).1).2
  have hbe : Metric.ball (t:ℂ) ρ ⊆ escapeOpen c := fun z hz => (hball hz).2
  have ht1mem : (t:ℂ) ∈ Metric.ball (t:ℂ) ρ := Metric.mem_ball_self hρ
  refine ⟨(t:ℂ), ρ, hρ, hballPc, hbn, hbnp, hbe, ?_, ?_⟩
  · exact explicitBranch_eq_bottcherCoord_of_anchor c n hballPc hbn hbe ht1mem hebn
  · exact explicitBranch_eq_bottcherCoord_of_anchor c (n + p) hballPc hbnp hbe ht1mem hebnp

/-- **Functional equation of a global single-valued basin branch.** If `β` is analytic on the basin
`Ω_c = (K_c)ᶜ` and equals `bottcherCoord c` on the far field `escapeOpen c`, then it satisfies the
Böttcher functional equation `β(f_c z) = (β z)²` everywhere on the basin. The difference `β∘f − β²` is
analytic on the basin, vanishes on `escapeOpen` (`β = φ_c` there and `φ_c(f z) = φ_c(z)²` by
`bottcherCoord_quadratic`), and the basin is preconnected, so the identity theorem spreads the
vanishing. **No winding argument is needed**: single-valuedness of `β` is assumed (the connected-basin
input), and the FE is then a pure identity-theorem consequence — the FE is *proven from* the branch,
not assumed alongside it. -/
theorem bottcherFE_of_global_branch {c : ℂ} {β : ℂ → ℂ}
    (hβan : AnalyticOnNhd ℂ β (filledJulia c)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c, β z = bottcherCoord c z) :
    ∀ z ∈ (filledJulia c)ᶜ, β (quadratic c z) = (β z) ^ 2 := by
  have hfbasin : ∀ z ∈ (filledJulia c)ᶜ, quadratic c z ∈ (filledJulia c)ᶜ := by
    intro z hz hcon; exact hz ((mem_filledJulia_iff_quadratic_mem c z).mpr hcon)
  set D : ℂ → ℂ := fun z => β (quadratic c z) - (β z) ^ 2 with hDdef
  have hcomp : AnalyticOnNhd ℂ (fun z => β (quadratic c z)) (filledJulia c)ᶜ := by
    intro z hz
    exact (hβan _ (hfbasin z hz)).comp (analyticAt_quadratic c z)
  have hDan : AnalyticOnNhd ℂ D (filledJulia c)ᶜ := hcomp.sub (hβan.pow 2)
  have hDesc : ∀ z ∈ escapeOpen c, D z = 0 := by
    intro z hz
    have hfz : quadratic c z ∈ escapeOpen c := by
      have := escapeOpen_iterate hz 1; rwa [Function.iterate_one] at this
    obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime hz
    show β (quadratic c z) - (β z) ^ 2 = 0
    rw [hβesc _ hfz, hβesc _ hz, bottcherCoord_quadratic hc hz2, sub_self]
  have hev : D =ᶠ[𝓝 ((max 2 ‖c‖ + 1 : ℝ) : ℂ)] (fun _ => (0 : ℂ)) := by
    filter_upwards [(isOpen_escapeOpen c).mem_nhds (deepPoint_mem_escapeOpen c)] with z hz
    exact hDesc z hz
  intro z hz
  have hDz : D z = 0 :=
    (hDan.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      (isPreconnected_compl_filledJulia c)
      (escapeOpen_subset_compl_filledJulia c (deepPoint_mem_escapeOpen c)) hev) hz
  exact sub_eq_zero.mp hDz

/-- **Iterated functional equation** `β(f^[p] z) = (β z)^{2^p}` of a global single-valued basin branch,
by induction on `p` from the one-step FE `bottcherFE_of_global_branch`. -/
theorem bottcherFE_iterate_of_global_branch {c : ℂ} {β : ℂ → ℂ}
    (hβan : AnalyticOnNhd ℂ β (filledJulia c)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c, β z = bottcherCoord c z) (p : ℕ) :
    ∀ z ∈ (filledJulia c)ᶜ, β ((quadratic c)^[p] z) = (β z) ^ (2 ^ p) := by
  have hfbasin : ∀ z ∈ (filledJulia c)ᶜ, quadratic c z ∈ (filledJulia c)ᶜ := by
    intro z hz hcon; exact hz ((mem_filledJulia_iff_quadratic_mem c z).mpr hcon)
  have hFE := bottcherFE_of_global_branch hβan hβesc
  induction p with
  | zero => intro z hz; simp
  | succ k ih =>
    intro z hz
    rw [Function.iterate_succ_apply, ih (quadratic c z) (hfbasin z hz), hFE z hz, ← pow_mul]
    congr 1
    rw [pow_succ]; ring

/-- **Analytic-coefficient relation spreads from the far field to the basin.** Identity theorem on the
preconnected basin (mirror of `GlobalBasinBranch.relation_eq_zero_basin` with analytic coefficients
`aᵢ` rather than polynomial `(P.coeff i)`). -/
theorem relation_eq_zero_basin_analytic {c : ℂ} {β : ℂ → ℂ} {a : ℕ → ℂ → ℂ} {s : Finset ℕ}
    (ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c)ᶜ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c)ᶜ)
    (harel : ∀ z ∈ escapeOpen c, ∑ i ∈ s, a i z * (β z) ^ i = 0) :
    ∀ z ∈ (filledJulia c)ᶜ, ∑ i ∈ s, a i z * (β z) ^ i = 0 := by
  have hrelan := analyticOnNhd_relation_analytic ha hβan
  have hev : (fun z => ∑ i ∈ s, a i z * (β z) ^ i) =ᶠ[𝓝 ((max 2 ‖c‖ + 1 : ℝ) : ℂ)]
      (fun _ => (0:ℂ)) := by
    filter_upwards [(isOpen_escapeOpen c).mem_nhds (deepPoint_mem_escapeOpen c)] with z hz
    exact harel z hz
  intro z hz
  exact (hrelan.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    (isPreconnected_compl_filledJulia c)
    (escapeOpen_subset_compl_filledJulia c (deepPoint_mem_escapeOpen c)) hev) hz

/-- **The FE + relation filter facts at a Julia point, from a global single-valued branch.** Both the
period-`p` Böttcher functional equation and the algebraic relation hold throughout the basin (FE from
`bottcherFE_iterate_of_global_branch`, relation from `relation_eq_zero_basin_analytic`); since the basin
is in `𝓝[(K_c)ᶜ] z₀`, both hold on that basin-side filter — exactly the two `∀ᶠ` facts the index
route's `hinput` consumes at each cycle point. The remaining per-point datum is the boundary limit
`Tendsto β (𝓝[basin] z₀) (𝓝 w₀)` and the simple-root structure. -/
theorem index_FE_relation_filters_of_global_branch {c : ℂ} {β : ℂ → ℂ}
    {a : ℕ → ℂ → ℂ} {s : Finset ℕ}
    (hβan : AnalyticOnNhd ℂ β (filledJulia c)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c, β z = bottcherCoord c z)
    (ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c)ᶜ)
    (harel : ∀ z ∈ escapeOpen c, ∑ i ∈ s, a i z * (β z) ^ i = 0)
    (z₀ : ℂ) (p : ℕ) :
    (∀ᶠ z in 𝓝[(filledJulia c)ᶜ] z₀, ∑ i ∈ s, a i z * (β z) ^ i = 0) ∧
    (∀ᶠ z in 𝓝[(filledJulia c)ᶜ] z₀, β ((quadratic c)^[p] z) = (β z) ^ (2 ^ p)) :=
  ⟨Filter.eventually_of_mem self_mem_nhdsWithin
      (relation_eq_zero_basin_analytic ha hβan harel),
   Filter.eventually_of_mem self_mem_nhdsWithin
      (bottcherFE_iterate_of_global_branch hβan hβesc p)⟩

/-- **The index-domination (small-mass) estimate, for large period.** For a finite set `B` of repelling
points (`1 < ‖2z‖`, the period-`1` multiplier), the exceptional-mass bound
`(2^p − 1)·∑_{z∈B}(‖2z‖^p − 1)⁻¹ < 2^p − |B|` holds for all large `p`. Mechanism: the bulk count grows
like `2^p` while the `B`-contribution `g(p) = ∑(‖2z‖^p−1)⁻¹ → 0` (each `‖2z‖ > 1`), so once `g(p) ≤ ½`
and `2|B| ≤ 2^p` the estimate closes by `(2^p−1)·g ≤ (2^p−1)/2 < 2^p − |B|`. This is the quantitative
heart of the index route: the index identity `∑ 1/(1−λ) = 0` then forces a non-pinned bulk cycle point.
At a separable period-`p` fibre (`|roots.toFinset| = 2^p`, `B ⊆ roots`) the RHS `2^p − |B|` equals
`|roots.toFinset \ B|`, matching `false_of_relative_bulk_branches`'s `hsmall`. -/
theorem eventually_index_small_mass {B : Finset ℂ} (hBrep : ∀ z ∈ B, 1 < ‖2 * z‖) :
    ∀ᶠ p : ℕ in atTop,
      ((2:ℝ)^p - 1) * ∑ z ∈ B, (‖2 * z‖^p - 1)⁻¹ < ((2:ℝ)^p - B.card) := by
  have hg0 : Tendsto (fun p : ℕ => ∑ z ∈ B, (‖2 * z‖^p - 1)⁻¹) atTop (𝓝 0) := by
    have hsum : Tendsto (fun p : ℕ => ∑ z ∈ B, (‖2 * z‖^p - 1)⁻¹) atTop (𝓝 (∑ _z ∈ B, (0:ℝ))) := by
      apply tendsto_finsetSum
      intro z hz
      have hμ : (1:ℝ) < ‖2 * z‖ := hBrep z hz
      have hpow : Tendsto (fun p : ℕ => ‖2 * z‖^p) atTop atTop :=
        tendsto_pow_atTop_atTop_of_one_lt hμ
      have hsub : Tendsto (fun p : ℕ => ‖2 * z‖^p - 1) atTop atTop := by
        simpa using hpow.atTop_add (tendsto_const_nhds (x := (-1:ℝ)))
      exact tendsto_inv_atTop_zero.comp hsub
    simpa using hsum
  have hgnn : ∀ p : ℕ, 0 ≤ ∑ z ∈ B, (‖2 * z‖^p - 1)⁻¹ := by
    intro p
    apply Finset.sum_nonneg
    intro z hz
    have hμ : (1:ℝ) < ‖2 * z‖ := hBrep z hz
    have h1 : (1:ℝ) ≤ ‖2 * z‖^p := one_le_pow₀ hμ.le
    exact inv_nonneg.mpr (by linarith)
  have hghalf : ∀ᶠ p : ℕ in atTop, ∑ z ∈ B, (‖2 * z‖^p - 1)⁻¹ ≤ 1/2 :=
    hg0.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1/2))
  have hcard : ∀ᶠ p : ℕ in atTop, (2 * (B.card : ℝ)) ≤ (2:ℝ)^p :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2)).eventually_ge_atTop _
  filter_upwards [hghalf, hcard] with p hg hc
  have h2p1 : (0:ℝ) ≤ (2:ℝ)^p - 1 := by
    have : (1:ℝ) ≤ (2:ℝ)^p := one_le_pow₀ (by norm_num)
    linarith
  calc ((2:ℝ)^p - 1) * ∑ z ∈ B, (‖2 * z‖^p - 1)⁻¹
      ≤ ((2:ℝ)^p - 1) * (1/2) := mul_le_mul_of_nonneg_left hg h2p1
    _ < (2:ℝ)^p - B.card := by nlinarith [hc]

/-- **Single-point repelling obstruction with the functional equation DERIVED from the global branch.**
Same as `RelativeBranchFamily.false_of_repelling_branch_analytic` but with the Böttcher
functional-equation hypothesis `hβfe` removed: when `β` is the global single-valued basin branch
(analytic on `(K_{c₁})ᶜ`, equal to `bottcherCoord c₁` on `escapeOpen c₁`), the FE `β(f^[p]z)=(βz)^{2^p}`
holds throughout the basin (`bottcherFE_iterate_of_global_branch`), hence on the basin-side filter at
`z₀` — so it need not be assumed. This shrinks the rigidity datum: the FE is now a *theorem about* the
branch, not an input. The remaining per-point hypotheses are the genuine dynamical residue — a
non-resonant repelling cycle point `z₀ ∈ J_{c₁}∖K_{c₂}` (`ha` needs `z₀` in `c₂`'s basin), a simple
root `(w₀,d)` of the relation fibre, the basin boundary limit `hβlim`, and non-resonance `hres`. -/
theorem false_of_repelling_branch_global {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {c₁ : ℂ}
    {z₀ w₀ d lam : ℂ} {p : ℕ} {β : ℂ → ℂ}
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (ha : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀)
    (hroot : ∑ i ∈ s, a i z₀ * w₀ ^ i = 0)
    (hpartial : HasDerivAt (fun w => ∑ i ∈ s, a i z₀ * w ^ i) d w₀) (hd : d ≠ 0)
    (hw₀ : w₀ ≠ 0) (hz₀ : z₀ ∈ filledJulia c₁)
    (hNeBot : (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot)
    (hβlim : Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀))
    (hβrel : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, ∑ i ∈ s, a i z * (β z) ^ i = 0)
    (hβne : ∃ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, β z ≠ w₀)
    (hFz : (quadratic c₁)^[p] z₀ = z₀)
    (hlam : HasDerivAt ((quadratic c₁)^[p]) lam z₀)
    (hres : ∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ)) :
    False :=
  false_of_repelling_branch_analytic ha hroot hpartial hd hw₀ hz₀ hNeBot hβlim hβrel
    (Filter.eventually_of_mem self_mem_nhdsWithin
      (bottcherFE_iterate_of_global_branch hβan hβesc p))
    hβne hFz hlam hres

/-- Escape levels are nested: `escapeLevel c n ⊆ escapeLevel c (n+1)` (forward invariance of escape). -/
theorem escapeLevel_subset_succ (c : ℂ) (n : ℕ) :
    escapeLevel c n ⊆ escapeLevel c (n + 1) := by
  intro z hz
  show (quadratic c)^[n+1] z ∈ escapeOpen c
  rw [Function.iterate_succ_apply']
  have := escapeOpen_iterate (show (quadratic c)^[n] z ∈ escapeOpen c from hz) 1
  rwa [Function.iterate_one] at this

/-- Escape levels are monotone: `n ≤ m ⟹ escapeLevel c n ⊆ escapeLevel c m`. -/
theorem escapeLevel_subset_of_le (c : ℂ) {n m : ℕ} (h : n ≤ m) :
    escapeLevel c n ⊆ escapeLevel c m := by
  induction m with
  | zero => simpa using (Nat.le_zero.mp h) ▸ subset_refl _
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h' | h'
    · exact (ih (Nat.lt_succ_iff.mp h')).trans (escapeLevel_subset_succ c k)
    · exact h' ▸ subset_refl _

/-- Each escape level is open (preimage of the open escape set under the entire iterate). -/
theorem isOpen_escapeLevel (c : ℂ) (n : ℕ) : IsOpen (escapeLevel c n) := by
  have hcont : Continuous ((quadratic c)^[n]) :=
    continuousOn_univ.mp (analyticOnNhd_quadratic_iterate c n).continuousOn
  exact hcont.isOpen_preimage _ (isOpen_escapeOpen c)

/-- **Global single-valued basin branch from a coherent family of level branches.** Given analytic
`βlev n` on each (connected, open, nested) escape level `escapeLevel c n`, agreeing across adjacent
levels (`βlev (n+1) = βlev n` on `escapeLevel c n`) and anchored at `bottcherCoord c` on level `0`
(`= escapeOpen c`), the pointwise colimit `β z = βlev (least level of z) z` is a single global branch:
analytic on the whole basin `(K_c)ᶜ = ⋃ₙ escapeLevel c n`, equal to `bottcherCoord c` on `escapeOpen c`.
This REDUCES the connected Böttcher uniformization (the `(hβan, hβesc)` input of
`bottcherFE_of_global_branch` and `false_of_repelling_branch_global`) to the per-level single-valued
`2ⁿ`-th-root branches — the remaining winding/monodromy construction. -/
theorem exists_global_branch_of_coherent_levels (c : ℂ) (βlev : ℕ → ℂ → ℂ)
    (hanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c n))
    (hcoherent : ∀ n, ∀ z ∈ escapeLevel c n, βlev (n + 1) z = βlev n z)
    (hanchor : ∀ z ∈ escapeOpen c, βlev 0 z = bottcherCoord c z) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) := by
  have hcoh_le : ∀ {n m : ℕ}, n ≤ m → ∀ z ∈ escapeLevel c n, βlev m z = βlev n z := by
    intro n m h
    induction m with
    | zero => intro z hz; simp [Nat.le_zero.mp h]
    | succ k ih =>
      intro z hz
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h' | h'
      · have hk : n ≤ k := Nat.lt_succ_iff.mp h'
        rw [hcoherent k z (escapeLevel_subset_of_le c hk hz), ih hk z hz]
      · subst h'; rfl
  classical
  set β : ℂ → ℂ := fun z => if h : ∃ n, z ∈ escapeLevel c n then βlev (Nat.find h) z else 0 with hβdef
  have hβval : ∀ z (n : ℕ), z ∈ escapeLevel c n → β z = βlev n z := by
    intro z n hz
    have hex : ∃ k, z ∈ escapeLevel c k := ⟨n, hz⟩
    have hfind : Nat.find hex ≤ n := Nat.find_le hz
    have hzfind : z ∈ escapeLevel c (Nat.find hex) := Nat.find_spec hex
    rw [hβdef]; simp only [dif_pos hex]
    rw [hcoh_le hfind z hzfind]
  refine ⟨β, ?_, ?_⟩
  · intro z hz
    rw [compl_filledJulia_eq_iUnion_level, Set.mem_iUnion] at hz
    obtain ⟨n, hzn⟩ := hz
    have hloc : β =ᶠ[𝓝 z] βlev n := by
      filter_upwards [(isOpen_escapeLevel c n).mem_nhds hzn] with w hw
      exact hβval w n hw
    exact (hanalytic n z hzn).congr hloc.symm
  · intro z hz
    have hz0 : z ∈ escapeLevel c 0 := by rw [escapeLevel_zero]; exact hz
    rw [hβval z 0 hz0, hanchor z hz]

/-- Each escape level is connected (nonempty — the deep point — and preconnected by Riemann–Hurwitz). -/
theorem isConnected_escapeLevel (c : ℂ) (n : ℕ) : IsConnected (escapeLevel c n) := by
  induction n with
  | zero => rw [escapeLevel_zero]; exact isConnected_escapeOpen c
  | succ k ih =>
    exact ⟨⟨_, deep_mem_escapeLevel c (k + 1)⟩, isPreconnected_preimage_escapeLevel c k ih⟩

/-- **Coherence of a level-branch family of `2ⁿ`-th roots.** If each `βlev n` is analytic and nonzero on
`escapeLevel c n` with `(βlev n)^{2ⁿ} = bottcherCoord c ∘ f^[n]`, anchored at `bottcherCoord c` on the far
field `escapeOpen c`, then adjacent levels agree: `βlev (n+1) = βlev n` on `escapeLevel c n`. The ratio is
a `2^{n+1}`-th root of unity — both sides' `2^{n+1}`-th powers equal `(bottcherCoord∘f^[n])²` via
`bottcherCoord_quadratic` — continuous on the connected level, pinned to `1` at the deep anchor where both
equal `bottcherCoord`. This is the coherence input of `exists_global_branch_of_coherent_levels`. -/
theorem levelBranch_coherent_of_pow (c : ℂ) (βlev : ℕ → ℂ → ℂ)
    (hanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c n))
    (hpow : ∀ n, ∀ z ∈ escapeLevel c n, (βlev n z) ^ (2 ^ n) = bottcherCoord c ((quadratic c)^[n] z))
    (hne : ∀ n, ∀ z ∈ escapeLevel c n, βlev n z ≠ 0)
    (hanchorEsc : ∀ n, ∀ z ∈ escapeOpen c, βlev n z = bottcherCoord c z) :
    ∀ n, ∀ z ∈ escapeLevel c n, βlev (n + 1) z = βlev n z := by
  intro n
  set V : Set ℂ := escapeLevel c n with hVdef
  have hVc : IsPreconnected V := (isConnected_escapeLevel c n).isPreconnected
  have hsub : V ⊆ escapeLevel c (n + 1) := escapeLevel_subset_succ c n
  set ξ : ℂ → ℂ := fun z => βlev (n + 1) z / βlev n z with hξdef
  have hpow1 : ∀ z ∈ V, ξ z ^ (2 ^ (n + 1)) = 1 := by
    intro z hz
    have hzn1 : z ∈ escapeLevel c (n + 1) := hsub hz
    have hfn : (quadratic c)^[n] z ∈ escapeOpen c := hz
    obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime hfn
    have hnum : (βlev (n + 1) z) ^ (2 ^ (n + 1)) = bottcherCoord c ((quadratic c)^[n] z) ^ 2 := by
      rw [hpow (n + 1) z hzn1]
      rw [show (quadratic c)^[n + 1] z = quadratic c ((quadratic c)^[n] z) from
        Function.iterate_succ_apply' (quadratic c) n z]
      exact bottcherCoord_quadratic hc hz2
    have hden : (βlev n z) ^ (2 ^ (n + 1)) = bottcherCoord c ((quadratic c)^[n] z) ^ 2 := by
      rw [show (2:ℕ) ^ (n + 1) = 2 ^ n * 2 from by rw [pow_succ], pow_mul, hpow n z hz]
    rw [hξdef]; simp only
    rw [div_pow, hnum, hden, div_self]
    exact pow_ne_zero _ (bottcherCoord_ne_zero c _)
  have hξc : ContinuousOn ξ V := by
    apply ContinuousOn.div
    · exact ((hanalytic (n + 1)).continuousOn).mono hsub
    · exact (hanalytic n).continuousOn
    · exact fun z hz => hne n z hz
  have hdeep : ((max 2 ‖c‖ + 1 : ℝ) : ℂ) ∈ V := deep_mem_escapeLevel c n
  have hdeepEsc : ((max 2 ‖c‖ + 1 : ℝ) : ℂ) ∈ escapeOpen c := by
    have := deep_mem_escapeLevel c 0; rwa [escapeLevel_zero] at this
  have hξdeep : ξ ((max 2 ‖c‖ + 1 : ℝ) : ℂ) = 1 := by
    rw [hξdef]; simp only
    rw [hanchorEsc (n + 1) _ hdeepEsc, hanchorEsc n _ hdeepEsc, div_self (bottcherCoord_ne_zero c _)]
  intro z hz
  have hconst : ξ z = ξ ((max 2 ‖c‖ + 1 : ℝ) : ℂ) :=
    const_of_pow_eq_one hVc hξc (by positivity) hpow1 hz hdeep
  rw [hξdeep] at hconst
  have hone : βlev (n + 1) z / βlev n z = 1 := hconst
  exact (div_eq_one_iff_eq (hne n z hz)).mp hone

/-- **The connected Böttcher uniformization reduced to per-level single-valued roots.** Combining the
coherence (`levelBranch_coherent_of_pow`) with the colimit gluing
(`exists_global_branch_of_coherent_levels`): a family of single-valued analytic nonzero `2ⁿ`-th-root
branches `βlev n` on the connected escape levels, each restricting to `bottcherCoord c` on the far field,
assembles into the **global single-valued basin branch** `β` (analytic on `(K_c)ᶜ`, `= bottcherCoord c`
on `escapeOpen c`) — exactly the `(hβan, hβesc)` input of `bottcherFE_of_global_branch` and
`false_of_repelling_branch_global`. So the entire connected-case branch input is reduced to the per-level
winding construction: a single-valued `2ⁿ`-th root of `bottcherCoord∘f^[n]` on `escapeLevel c n`. -/
theorem exists_global_branch_of_level_roots (c : ℂ) (βlev : ℕ → ℂ → ℂ)
    (hanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c n))
    (hpow : ∀ n, ∀ z ∈ escapeLevel c n, (βlev n z) ^ (2 ^ n) = bottcherCoord c ((quadratic c)^[n] z))
    (hne : ∀ n, ∀ z ∈ escapeLevel c n, βlev n z ≠ 0)
    (hanchorEsc : ∀ n, ∀ z ∈ escapeOpen c, βlev n z = bottcherCoord c z) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) :=
  exists_global_branch_of_coherent_levels c βlev hanalytic
    (levelBranch_coherent_of_pow c βlev hanalytic hpow hne hanchorEsc)
    (fun z hz => hanchorEsc 0 z hz)

/-- **Square-root recursion ⟹ the `2ⁿ`-th-power property.** A family `βlev` with `βlev 0 = bottcherCoord`
on `escapeOpen` and, at each level, `(βlev (n+1))² = βlev n ∘ f` on `escapeLevel c (n+1)`, automatically
satisfies the `2ⁿ`-th-power law `(βlev n)^{2ⁿ} = bottcherCoord ∘ f^[n]` on every `escapeLevel c n`.
Induction: the base is the anchor; the step uses `(βlev(n+1))^{2^{n+1}} = ((βlev(n+1))²)^{2ⁿ} =
(βlev n ∘ f)^{2ⁿ}` and the IH at `f z ∈ escapeLevel c n`. Reduces the per-level root family to a single
SQUARE ROOT step `βlev (n+1) = √(βlev n ∘ f)`. -/
theorem hpow_of_sqrt_family (c : ℂ) (βlev : ℕ → ℂ → ℂ)
    (hanchor0 : ∀ z ∈ escapeOpen c, βlev 0 z = bottcherCoord c z)
    (hsqrt : ∀ n, ∀ z ∈ escapeLevel c (n + 1), (βlev (n + 1) z) ^ 2 = βlev n (quadratic c z)) :
    ∀ n, ∀ z ∈ escapeLevel c n, (βlev n z) ^ (2 ^ n) = bottcherCoord c ((quadratic c)^[n] z) := by
  intro n
  induction n with
  | zero =>
    intro z hz
    rw [escapeLevel_zero] at hz
    simp only [pow_zero, pow_one, Function.iterate_zero, id_eq]
    exact hanchor0 z hz
  | succ k ih =>
    intro z hz
    have hfz : quadratic c z ∈ escapeLevel c k := by
      show (quadratic c)^[k] (quadratic c z) ∈ escapeOpen c
      rw [← Function.iterate_succ_apply]; exact hz
    have hstep : (βlev (k + 1) z) ^ (2 ^ (k + 1)) = (βlev k (quadratic c z)) ^ (2 ^ k) := by
      rw [show (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k from by rw [pow_succ]; ring, pow_mul, hsqrt k z hz]
    rw [hstep, ih (quadratic c z) hfz, ← Function.iterate_succ_apply]

/-- **The global branch from a square-root family.** Combining `hpow_of_sqrt_family` with
`exists_global_branch_of_level_roots`: a family of analytic nowhere-zero `βlev n` on the escape levels,
anchored to `bottcherCoord c` on `escapeOpen c`, with `(βlev (n+1))² = βlev n ∘ f` at each level,
assembles into the global single-valued basin branch. The cleanest reduction of the connected Böttcher
uniformization: the only remaining atom is a single-valued analytic **square root** of `βlev n ∘ f` on
the connected `escapeLevel c (n+1)` (the winding identification), iterated. -/
theorem exists_global_branch_of_sqrt_family (c : ℂ) (βlev : ℕ → ℂ → ℂ)
    (hanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c n))
    (hne : ∀ n, ∀ z ∈ escapeLevel c n, βlev n z ≠ 0)
    (hanchorEsc : ∀ n, ∀ z ∈ escapeOpen c, βlev n z = bottcherCoord c z)
    (hsqrt : ∀ n, ∀ z ∈ escapeLevel c (n + 1), (βlev (n + 1) z) ^ 2 = βlev n (quadratic c z)) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) :=
  exists_global_branch_of_level_roots c βlev hanalytic
    (hpow_of_sqrt_family c βlev (hanchorEsc 0) hsqrt) hne hanchorEsc

/-- **The basin boundary limit lands on the unit circle.** If a basin branch `β` carries the Böttcher
modulus `‖β‖ = exp(G_c)` on the basin and has a limit `w₀` along the basin at a Julia point `z₀ ∈ J_c`
(basin accumulating, `NeBot`), then `‖w₀‖ = 1` — hence `w₀ ≠ 0`. Mechanism: `‖β z‖ = exp(G_c z) →
exp(G_c z₀) = exp 0 = 1` (`tendsto_greenFunctionDyn_boundary` + `G_c = 0` on `K_c`) and `‖β z‖ → ‖w₀‖`
(norm continuous); unique limit on the `NeBot` filter. Supplies the `w₀ ≠ 0` datum of the
repelling-cycle input for free from the boundary limit. -/
theorem norm_boundary_limit_eq_one {c : ℂ} {β : ℂ → ℂ} {z₀ w₀ : ℂ}
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    (hz₀ : z₀ ∈ filledJulia c) (hNeBot : (𝓝[(filledJulia c)ᶜ] z₀).NeBot)
    (hβlim : Tendsto β (𝓝[(filledJulia c)ᶜ] z₀) (𝓝 w₀)) :
    ‖w₀‖ = 1 := by
  haveI := hNeBot
  have h1 : Tendsto (fun z => ‖β z‖) (𝓝[(filledJulia c)ᶜ] z₀) (𝓝 ‖w₀‖) :=
    (continuous_norm.continuousAt).tendsto.comp hβlim
  have h2 : Tendsto (fun z => ‖β z‖) (𝓝[(filledJulia c)ᶜ] z₀) (𝓝 1) := by
    have hgreen : Tendsto (fun z => Real.exp (greenFunctionDyn c z))
        (𝓝[(filledJulia c)ᶜ] z₀) (𝓝 1) := by
      have hg0 : Tendsto (greenFunctionDyn c) (𝓝[(filledJulia c)ᶜ] z₀) (𝓝 0) :=
        (tendsto_greenFunctionDyn_boundary hz₀).mono_left nhdsWithin_le_nhds
      have := (Real.continuous_exp.continuousAt).tendsto.comp hg0
      simpa using this
    exact hgreen.congr' (by filter_upwards [self_mem_nhdsWithin] with z hz; rw [hβmod z hz])
  exact tendsto_nhds_unique h1 h2

/-- `f` maps `escapeLevel c (n+1)` into `escapeLevel c n`. -/
theorem quadratic_mapsTo_escapeLevel (c : ℂ) (n : ℕ) :
    Set.MapsTo (quadratic c) (escapeLevel c (n + 1)) (escapeLevel c n) := by
  intro z hz
  show (quadratic c)^[n] (quadratic c z) ∈ escapeOpen c
  rw [← Function.iterate_succ_apply]; exact hz

/-- **Descent step on a simply-connected piece.** On any simply-connected open `V ⊆ escapeLevel c (n+1)`,
the pullback `βlev n ∘ f` is analytic and nowhere-zero (`f(V) ⊆ escapeLevel c n`, `βlev n` analytic
nonvanishing there), so it has an analytic SQUARE ROOT on `V` (`exists_analyticOnNhd_pow_eq`, `N = 2`).
This is the local form of `βlev (n+1)` — a single-valued analytic `s` with `s² = βlev n ∘ f` on each
simply-connected chart of the escape level. Gluing the charts across the connected (π₁=ℤ) level is the
remaining winding step. -/
theorem exists_sqrt_pullback_on_simplyConnected (c : ℂ) (n : ℕ) {V : Set ℂ}
    (hVsc : IsSimplyConnected V) (hVo : IsOpen V) (hVsub : V ⊆ escapeLevel c (n + 1))
    (βlevn : ℂ → ℂ) (hβan : AnalyticOnNhd ℂ βlevn (escapeLevel c n))
    (hβne : ∀ z ∈ escapeLevel c n, βlevn z ≠ 0) :
    ∃ s : ℂ → ℂ, AnalyticOnNhd ℂ s V ∧ ∀ z ∈ V, (s z) ^ 2 = βlevn (quadratic c z) := by
  have hmaps : Set.MapsTo (quadratic c) V (escapeLevel c n) :=
    (quadratic_mapsTo_escapeLevel c n).mono_left hVsub
  have hgan : AnalyticOnNhd ℂ (fun z => βlevn (quadratic c z)) V := by
    intro z hz
    exact (hβan _ (hmaps hz)).comp (analyticAt_quadratic c z)
  have hg0 : ∀ z ∈ V, βlevn (quadratic c z) ≠ 0 := fun z hz => hβne _ (hmaps hz)
  exact exists_analyticOnNhd_pow_eq hVsc hVo hgan hg0 (by norm_num : 1 ≤ 2)

/-- **Level branch from two simply-connected charts.** If the connected level `escapeLevel c (n+1)` is
covered by two open charts `V₁, V₂`, each carrying a square root `sᵢ` of `βlev n ∘ f` (from the descent
step `exists_sqrt_pullback_on_simplyConnected` on a simply-connected chart), and the two roots AGREE on
the overlap `V₁ ∩ V₂` (`hagree` — the single winding identification), then they glue
(`analyticOnNhd_glue_twoChart`) into a single-valued analytic `s` on all of `escapeLevel c (n+1)` with
`s² = βlev n ∘ f`. Everything is proven except `hagree`, which isolates the winding fact: the even
winding `2` of `βlev n ∘ f` forces the overlap roots to match. -/
theorem exists_levelBranch_succ_of_chart_agreement (c : ℂ) (n : ℕ)
    {V₁ V₂ : Set ℂ} (hV₁o : IsOpen V₁) (hV₂o : IsOpen V₂)
    (hcover : escapeLevel c (n + 1) ⊆ V₁ ∪ V₂)
    (βlevn : ℂ → ℂ) (s₁ s₂ : ℂ → ℂ)
    (hs₁an : AnalyticOnNhd ℂ s₁ V₁) (hs₂an : AnalyticOnNhd ℂ s₂ V₂)
    (hs₁sq : ∀ z ∈ V₁, (s₁ z) ^ 2 = βlevn (quadratic c z))
    (hs₂sq : ∀ z ∈ V₂, (s₂ z) ^ 2 = βlevn (quadratic c z))
    (hagree : EqOn s₁ s₂ (V₁ ∩ V₂)) :
    ∃ s : ℂ → ℂ, AnalyticOnNhd ℂ s (escapeLevel c (n + 1)) ∧
      (∀ z ∈ escapeLevel c (n + 1), (s z) ^ 2 = βlevn (quadratic c z)) := by
  obtain ⟨s, hsan, hs1, hs2⟩ := analyticOnNhd_glue_twoChart hV₁o hV₂o hs₁an hs₂an hagree
  refine ⟨s, hsan.mono hcover, ?_⟩
  intro z hz
  rcases hcover hz with hz1 | hz2
  · rw [hs1 hz1]; exact hs₁sq z hz1
  · rw [hs2 hz2]; exact hs₂sq z hz2

/-- **Two square roots agreeing at one point of a preconnected set agree throughout.** If `s₁, s₂` are
continuous on a preconnected `W` with `(s₁)² = (s₂)²` and `s₂ ≠ 0` there, and `s₁ z₀ = s₂ z₀` at one
point `z₀ ∈ W`, then `s₁ = s₂` on all of `W`. (The ratio `ξ = s₁/s₂` satisfies `ξ² = 1`, is continuous
root-of-unity-valued — hence constant on the preconnected `W` — pinned to `1` at `z₀`.) Per-component
agreement tool for the level-branch chart gluing: on each component of the chart overlap, both descent
roots equal the single-valued `bottcherCoord` on the far field, so they agree — **resolving the winding
via the far-field anchor** (`bottcherCoord` is already single-valued on `escapeOpen`, pinning both sides
of every seam). -/
theorem eqOn_sqrt_of_preconnected {W : Set ℂ} (hWc : IsPreconnected W) {s₁ s₂ : ℂ → ℂ}
    (hs₁ : ContinuousOn s₁ W) (hs₂ : ContinuousOn s₂ W)
    (hsq : ∀ z ∈ W, (s₁ z) ^ 2 = (s₂ z) ^ 2) (hs₂0 : ∀ z ∈ W, s₂ z ≠ 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ W) (hanchor : s₁ z₀ = s₂ z₀) :
    EqOn s₁ s₂ W := by
  set ξ : ℂ → ℂ := fun z => s₁ z / s₂ z with hξdef
  have hpow : ∀ z ∈ W, ξ z ^ 2 = 1 := by
    intro z hz
    rw [hξdef]; simp only
    rw [div_pow, hsq z hz, div_self (pow_ne_zero _ (hs₂0 z hz))]
  have hξc : ContinuousOn ξ W := hs₁.div hs₂ (fun z hz => hs₂0 z hz)
  intro z hz
  have hconst : ξ z = ξ z₀ := const_of_pow_eq_one hWc hξc (by norm_num) hpow hz hz₀
  have hξ1 : ξ z₀ = 1 := by
    rw [hξdef]; simp only; rw [hanchor, div_self (hs₂0 z₀ hz₀)]
  rw [hξ1] at hconst
  have hone : s₁ z / s₂ z = 1 := hconst
  exact (div_eq_one_iff_eq (hs₂0 z hz)).mp hone

/-- The reflected annular sector `{R < ‖z‖ ∧ -z ∈ slitPlane}` is simply connected (image of the
`slitPlane` sector under the negation homeomorphism). -/
theorem isSimplyConnected_neg_sector {R : ℝ} (hR : 0 < R) :
    IsSimplyConnected {z : ℂ | R < ‖z‖ ∧ -z ∈ slitPlane} := by
  have himg : {z : ℂ | R < ‖z‖ ∧ -z ∈ slitPlane}
      = (Homeomorph.neg ℂ) '' {z : ℂ | R < ‖z‖ ∧ z ∈ slitPlane} := by
    ext z
    simp only [mem_setOf_eq, Homeomorph.neg, mem_image]
    constructor
    · intro ⟨h1, h2⟩; exact ⟨-z, ⟨by simpa using h1, by simpa using h2⟩, by simp⟩
    · rintro ⟨w, ⟨h1, h2⟩, rfl⟩; exact ⟨by simpa using h1, by simpa using h2⟩
  rw [himg, Homeomorph.isSimplyConnected_image]
  exact isSimplyConnected_sector hR

/-- **The far field `escapeOpen` is covered by two simply-connected sectors.** Every point of
`escapeOpen c` avoids at least one of the two opposite rays `ℝ_{≤0}`, `ℝ_{≥0}`, so it lies in the
`slitPlane` sector or the reflected sector — both simply connected (`isSimplyConnected_sector`,
`isSimplyConnected_neg_sector`). The base case of the escape-level chart cover. -/
theorem escapeOpen_subset_sectors (c : ℂ) :
    escapeOpen c ⊆ {z : ℂ | max 2 ‖c‖ < ‖z‖ ∧ z ∈ slitPlane}
      ∪ {z : ℂ | max 2 ‖c‖ < ‖z‖ ∧ -z ∈ slitPlane} := by
  intro z hz
  have hznorm : max 2 ‖c‖ < ‖z‖ := hz
  have hz0 : z ≠ 0 := by rintro rfl; simp at hznorm; nlinarith [hznorm]
  by_cases him : z.im = 0
  · by_cases hre : 0 < z.re
    · exact Or.inl ⟨hznorm, by rw [Complex.mem_slitPlane_iff]; left; exact hre⟩
    · have hrn : z.re < 0 := by
        rcases lt_trichotomy z.re 0 with h | h | h
        · exact h
        · exact absurd (Complex.ext h him) hz0
        · exact absurd hre (not_not.mpr h)
      exact Or.inr ⟨hznorm, by rw [Complex.mem_slitPlane_iff]; left; simp; linarith⟩
  · exact Or.inl ⟨hznorm, by rw [Complex.mem_slitPlane_iff]; right; exact him⟩

/-- **The deck symmetry of `f = z²+c`:** `f z = f w ↔ z = w ∨ z = -w`. The two preimages of any value
are related by the deck involution `z ↦ -z` (the branched 2-to-1 structure, unbranched off the critical
point `0`). The foundation of the covering lift `escapeLevel c(n+1) → escapeLevel c n`. -/
theorem quadratic_eq_iff (c z w : ℂ) :
    quadratic c z = quadratic c w ↔ z = w ∨ z = -w := by
  unfold quadratic
  constructor
  · intro h
    have hz2 : z ^ 2 = w ^ 2 := by linear_combination h
    have hfac : (z - w) * (z + w) = 0 := by ring_nf; linear_combination hz2
    rcases mul_eq_zero.mp hfac with h1 | h1
    · left; linear_combination h1
    · right; linear_combination h1
  · rintro (rfl | rfl) <;> ring

/-- **An inverse branch of `f = z²+c` over a simply-connected region.** On a simply-connected open `U`
not containing the critical value `c`, there is an analytic `g` with `f(g w) = w` for all `w ∈ U` —
a single-valued branch of `√(w-c)` (existing because `w ↦ w-c` is nonvanishing on `U` and `U` is simply
connected, `exists_analyticOnNhd_pow_eq`). The building block of the covering lift
`escapeLevel c(n+1) → escapeLevel c n`: composing inverse branches lifts a simply-connected far-field
sector to a simply-connected sheet deep in the escape level. -/
theorem exists_quadratic_inverse_branch (c : ℂ) {U : Set ℂ}
    (hUsc : IsSimplyConnected U) (hUo : IsOpen U) (hc : c ∉ U) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧ ∀ w ∈ U, quadratic c (g w) = w := by
  have hne : ∀ w ∈ U, (fun w => w - c) w ≠ 0 := by
    intro w hw hzero
    exact hc (sub_eq_zero.mp hzero ▸ hw)
  have hsuban : AnalyticOnNhd ℂ (fun w => w - c) U := fun w _ => by fun_prop
  obtain ⟨g, hgan, hgsq⟩ := exists_analyticOnNhd_pow_eq hUsc hUo hsuban hne (by norm_num : 1 ≤ 2)
  refine ⟨g, hgan, fun w hw => ?_⟩
  have hs : (g w) ^ 2 = w - c := by simpa using hgsq w hw
  calc
    (g w) ^ 2 + c = (w - c) + c := by rw [hs]
    _ = w := by ring

end Bottcher

namespace Bottcher

/-- **Nonvanishing square-root descent on a simply-connected piece.** The local square root supplied by
`exists_sqrt_pullback_on_simplyConnected` is automatically nowhere zero when the previous level branch is
nowhere zero. This is the exact nonvanishing datum needed by the global level-root assembly. -/
theorem exists_sqrt_pullback_on_simplyConnected_nonzero (c : ℂ) (n : ℕ) {V : Set ℂ}
    (hVsc : IsSimplyConnected V) (hVo : IsOpen V) (hVsub : V ⊆ escapeLevel c (n + 1))
    (βlevn : ℂ → ℂ) (hβan : AnalyticOnNhd ℂ βlevn (escapeLevel c n))
    (hβne : ∀ z ∈ escapeLevel c n, βlevn z ≠ 0) :
    ∃ s : ℂ → ℂ, AnalyticOnNhd ℂ s V ∧
      (∀ z ∈ V, (s z) ^ 2 = βlevn (quadratic c z)) ∧
      (∀ z ∈ V, s z ≠ 0) := by
  obtain ⟨s, hsan, hsq⟩ :=
    exists_sqrt_pullback_on_simplyConnected c n hVsc hVo hVsub βlevn hβan hβne
  refine ⟨s, hsan, hsq, ?_⟩
  intro z hz hs0
  have hfz : quadratic c z ∈ escapeLevel c n := quadratic_mapsTo_escapeLevel c n (hVsub hz)
  have hzero : βlevn (quadratic c z) = 0 := by
    have hsqz := hsq z hz
    simpa [hs0] using hsqz.symm
  exact (hβne (quadratic c z) hfz) hzero

/-- **Normalized successor branch on a simply-connected escape level.** If the next escape level is
simply connected, the local square-root descent can be normalized by the far-field Böttcher sheet:
starting from a level branch `βlevn` anchored to `bottcherCoord` on `escapeOpen`, Lean constructs the
successor branch on `escapeLevel c (n+1)` with the square-root recursion, nonvanishing, and the same
far-field anchor.  This is the one-step constructor needed for an eventual recursive square-root tower. -/
theorem exists_sqrtLevel_succ_of_simplyConnected (c : ℂ) (n : ℕ)
    (hsc : IsSimplyConnected (escapeLevel c (n + 1)))
    (βlevn : ℂ → ℂ) (hβan : AnalyticOnNhd ℂ βlevn (escapeLevel c n))
    (hβne : ∀ z ∈ escapeLevel c n, βlevn z ≠ 0)
    (hβanchor : ∀ z ∈ escapeOpen c, βlevn z = bottcherCoord c z) :
    ∃ βnext : ℂ → ℂ,
      AnalyticOnNhd ℂ βnext (escapeLevel c (n + 1)) ∧
      (∀ z ∈ escapeLevel c (n + 1), βnext z ≠ 0) ∧
      (∀ z ∈ escapeLevel c (n + 1), (βnext z) ^ 2 = βlevn (quadratic c z)) ∧
      (∀ z ∈ escapeOpen c, βnext z = bottcherCoord c z) := by
  obtain ⟨s, hsan, hsq, hs0⟩ :=
    exists_sqrt_pullback_on_simplyConnected_nonzero c n hsc (isOpen_escapeLevel c (n + 1))
      (subset_refl _) βlevn hβan hβne
  let d : ℂ := ((max 2 ‖c‖ + 1 : ℝ) : ℂ)
  have hdlev : d ∈ escapeLevel c (n + 1) := by
    simpa [d] using deep_mem_escapeLevel c (n + 1)
  have hdesc : d ∈ escapeOpen c := by
    have := deep_mem_escapeLevel c 0
    simpa [d, escapeLevel_zero] using this
  have hfd : quadratic c d ∈ escapeOpen c := by
    have := escapeOpen_iterate hdesc 1
    simpa [Function.iterate_one] using this
  have hsd0 : s d ≠ 0 := hs0 d hdlev
  let η : ℂ := bottcherCoord c d / s d
  have hη2 : η ^ 2 = 1 := by
    rw [show η = bottcherCoord c d / s d from rfl, div_pow, hsq d hdlev,
      hβanchor (quadratic c d) hfd]
    obtain ⟨hc, hd2⟩ := mem_escapeOpen_regime hdesc
    rw [bottcherCoord_quadratic hc hd2,
      div_self (pow_ne_zero 2 (bottcherCoord_ne_zero c d))]
  let βnext : ℂ → ℂ := fun z => η * s z
  have hβnext_an : AnalyticOnNhd ℂ βnext (escapeLevel c (n + 1)) := by
    intro z hz
    exact analyticAt_const.mul (hsan z hz)
  have hβnext_ne : ∀ z ∈ escapeLevel c (n + 1), βnext z ≠ 0 := by
    intro z hz
    exact mul_ne_zero (by
      rw [show η = bottcherCoord c d / s d from rfl]
      exact div_ne_zero (bottcherCoord_ne_zero c d) hsd0) (hs0 z hz)
  have hβnext_sq : ∀ z ∈ escapeLevel c (n + 1), (βnext z) ^ 2 = βlevn (quadratic c z) := by
    intro z hz
    calc
      (βnext z) ^ 2 = η ^ 2 * (s z) ^ 2 := by simp [βnext, mul_pow]
      _ = βlevn (quadratic c z) := by rw [hη2, one_mul, hsq z hz]
  have hβnext_anchor : ∀ z ∈ escapeOpen c, βnext z = bottcherCoord c z := by
    have hanchor_d : βnext d = bottcherCoord c d := by
      dsimp [βnext, η]
      exact div_mul_cancel₀ (bottcherCoord c d) hsd0
    have hEq : EqOn βnext (bottcherCoord c) (escapeOpen c) := by
      refine eqOn_sqrt_of_preconnected (isConnected_escapeOpen c).isPreconnected
        (hβnext_an.continuousOn.mono ?_) (analyticOnNhd_bottcherCoord_full c).continuousOn ?_
        (fun z _ => bottcherCoord_ne_zero c z) hdesc hanchor_d
      · intro z hz
        exact escapeOpen_iterate hz (n + 1)
      · intro z hz
        have hzlev : z ∈ escapeLevel c (n + 1) := escapeOpen_iterate hz (n + 1)
        have hfz : quadratic c z ∈ escapeOpen c := by
          have := escapeOpen_iterate hz 1
          simpa [Function.iterate_one] using this
        obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime hz
        rw [hβnext_sq z hzlev, hβanchor (quadratic c z) hfz, bottcherCoord_quadratic hc hz2]
    intro z hz
    exact hEq hz
  exact ⟨βnext, hβnext_an, hβnext_ne, hβnext_sq, hβnext_anchor⟩

/-- **Recursive square-root tower from simply-connected escape levels.** The one-step normalized
successor constructor can be iterated: if every successor escape level is simply connected, Lean builds
the whole analytic nowhere-zero square-root family `βlev n`, anchored to the far-field Böttcher
coordinate, with `(βlev (n+1))² = βlev n ∘ f` on each next level. -/
theorem exists_sqrt_family_of_simplyConnected_levels (c : ℂ)
    (hsc : ∀ n, IsSimplyConnected (escapeLevel c (n + 1))) :
    ∃ βlev : ℕ → ℂ → ℂ,
      (∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c n)) ∧
      (∀ n, ∀ z ∈ escapeLevel c n, βlev n z ≠ 0) ∧
      (∀ n, ∀ z ∈ escapeOpen c, βlev n z = bottcherCoord c z) ∧
      (∀ n, ∀ z ∈ escapeLevel c (n + 1),
        (βlev (n + 1) z) ^ 2 = βlev n (quadratic c z)) := by
  classical
  let BranchData (n : ℕ) := {β : ℂ → ℂ //
    AnalyticOnNhd ℂ β (escapeLevel c n) ∧
    (∀ z ∈ escapeLevel c n, β z ≠ 0) ∧
    (∀ z ∈ escapeOpen c, β z = bottcherCoord c z)}
  have hbase : BranchData 0 := by
    refine ⟨bottcherCoord c, ?_, ?_, ?_⟩
    · simpa [escapeLevel_zero] using analyticOnNhd_bottcherCoord_full c
    · intro z _hz
      exact bottcherCoord_ne_zero c z
    · intro z _hz
      rfl
  have hsucc : ∀ n, (b : BranchData n) → ∃ bnext : BranchData (n + 1),
      ∀ z ∈ escapeLevel c (n + 1), (bnext.1 z) ^ 2 = b.1 (quadratic c z) := by
    intro n b
    obtain ⟨βnext, han, hne, hsqrt, hanchor⟩ :=
      exists_sqrtLevel_succ_of_simplyConnected c n (hsc n)
        b.1 b.2.1 b.2.2.1 b.2.2.2
    exact ⟨⟨βnext, han, hne, hanchor⟩, hsqrt⟩
  let data : ∀ n, BranchData n := Nat.rec hbase (fun n b => Classical.choose (hsucc n b))
  let βlev : ℕ → ℂ → ℂ := fun n => (data n).1
  refine ⟨βlev, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (data n).2.1
  · intro n
    exact (data n).2.2.1
  · intro n
    exact (data n).2.2.2
  · intro n z hz
    change ((data (n + 1)).1 z) ^ 2 = (data n).1 (quadratic c z)
    change ((Classical.choose (hsucc n (data n))).1 z) ^ 2 = (data n).1 (quadratic c z)
    exact (Classical.choose_spec (hsucc n (data n))) z hz

/-- **Two-chart successor level branch, with nonvanishing.** If two chart roots of `βlev n ∘ f` agree on
their overlap and are nowhere zero on their charts, their glued successor branch on
`escapeLevel c (n+1)` is also nowhere zero. This packages the analytic, square, and nonzero data required
for the next level of the connected Böttcher uniformization. -/
theorem exists_levelBranch_succ_of_chart_agreement_nonzero (c : ℂ) (n : ℕ)
    {V₁ V₂ : Set ℂ} (hV₁o : IsOpen V₁) (hV₂o : IsOpen V₂)
    (hcover : escapeLevel c (n + 1) ⊆ V₁ ∪ V₂)
    (βlevn : ℂ → ℂ) (s₁ s₂ : ℂ → ℂ)
    (hs₁an : AnalyticOnNhd ℂ s₁ V₁) (hs₂an : AnalyticOnNhd ℂ s₂ V₂)
    (hs₁sq : ∀ z ∈ V₁, (s₁ z) ^ 2 = βlevn (quadratic c z))
    (hs₂sq : ∀ z ∈ V₂, (s₂ z) ^ 2 = βlevn (quadratic c z))
    (hs₁0 : ∀ z ∈ V₁, s₁ z ≠ 0) (hs₂0 : ∀ z ∈ V₂, s₂ z ≠ 0)
    (hagree : EqOn s₁ s₂ (V₁ ∩ V₂)) :
    ∃ s : ℂ → ℂ, AnalyticOnNhd ℂ s (escapeLevel c (n + 1)) ∧
      (∀ z ∈ escapeLevel c (n + 1), (s z) ^ 2 = βlevn (quadratic c z)) ∧
      (∀ z ∈ escapeLevel c (n + 1), s z ≠ 0) := by
  obtain ⟨s, hsan, hs1, hs2⟩ := analyticOnNhd_glue_twoChart hV₁o hV₂o hs₁an hs₂an hagree
  refine ⟨s, hsan.mono hcover, ?_, ?_⟩
  · intro z hz
    rcases hcover hz with hz1 | hz2
    · rw [hs1 hz1]
      exact hs₁sq z hz1
    · rw [hs2 hz2]
      exact hs₂sq z hz2
  · intro z hz
    rcases hcover hz with hz1 | hz2
    · rw [hs1 hz1]
      exact hs₁0 z hz1
    · rw [hs2 hz2]
      exact hs₂0 z hz2

end Bottcher

namespace Bottcher

/-- **Two-chart successor from chart roots alone.** For chart roots of `βlev n ∘ f`, nonvanishing is not an
extra analytic hypothesis: it follows from the square identities and nonvanishing of `βlev n` on the
previous escape level. Thus a pair of agreeing chart roots glues directly into the full successor datum
`(analytic, square law, nonzero)` on `escapeLevel c (n+1)`. -/
theorem exists_levelBranch_succ_of_chart_roots (c : ℂ) (n : ℕ)
    {V₁ V₂ : Set ℂ} (hV₁o : IsOpen V₁) (hV₂o : IsOpen V₂)
    (hcover : escapeLevel c (n + 1) ⊆ V₁ ∪ V₂)
    (hV₁sub : V₁ ⊆ escapeLevel c (n + 1)) (hV₂sub : V₂ ⊆ escapeLevel c (n + 1))
    (βlevn : ℂ → ℂ) (hβne : ∀ z ∈ escapeLevel c n, βlevn z ≠ 0)
    (hroots : ∃ s₁ s₂ : ℂ → ℂ,
      AnalyticOnNhd ℂ s₁ V₁ ∧ AnalyticOnNhd ℂ s₂ V₂ ∧
      (∀ z ∈ V₁, (s₁ z) ^ 2 = βlevn (quadratic c z)) ∧
      (∀ z ∈ V₂, (s₂ z) ^ 2 = βlevn (quadratic c z)) ∧
      EqOn s₁ s₂ (V₁ ∩ V₂)) :
    ∃ s : ℂ → ℂ, AnalyticOnNhd ℂ s (escapeLevel c (n + 1)) ∧
      (∀ z ∈ escapeLevel c (n + 1), (s z) ^ 2 = βlevn (quadratic c z)) ∧
      (∀ z ∈ escapeLevel c (n + 1), s z ≠ 0) := by
  obtain ⟨s₁, s₂, hs₁an, hs₂an, hs₁sq, hs₂sq, hagree⟩ := hroots
  have hs₁0 : ∀ z ∈ V₁, s₁ z ≠ 0 := by
    intro z hz hs0
    have hfz : quadratic c z ∈ escapeLevel c n := quadratic_mapsTo_escapeLevel c n (hV₁sub hz)
    have hzero : βlevn (quadratic c z) = 0 := by
      have hsqz := hs₁sq z hz
      simpa [hs0] using hsqz.symm
    exact (hβne (quadratic c z) hfz) hzero
  have hs₂0 : ∀ z ∈ V₂, s₂ z ≠ 0 := by
    intro z hz hs0
    have hfz : quadratic c z ∈ escapeLevel c n := quadratic_mapsTo_escapeLevel c n (hV₂sub hz)
    have hzero : βlevn (quadratic c z) = 0 := by
      have hsqz := hs₂sq z hz
      simpa [hs0] using hsqz.symm
    exact (hβne (quadratic c z) hfz) hzero
  exact exists_levelBranch_succ_of_chart_agreement_nonzero c n hV₁o hV₂o hcover βlevn s₁ s₂
    hs₁an hs₂an hs₁sq hs₂sq hs₁0 hs₂0 hagree

end Bottcher

namespace Bottcher

/-- **Boundary limit nonzero.** The modulus identity on the basin and a basin-side limit at a Julia point
force the limiting value onto the unit circle, hence it is nonzero. -/
theorem boundary_limit_ne_zero {c : ℂ} {β : ℂ → ℂ} {z₀ w₀ : ℂ}
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    (hz₀ : z₀ ∈ filledJulia c) (hNeBot : (𝓝[(filledJulia c)ᶜ] z₀).NeBot)
    (hβlim : Tendsto β (𝓝[(filledJulia c)ᶜ] z₀) (𝓝 w₀)) :
    w₀ ≠ 0 := by
  intro hw
  have hnorm := norm_boundary_limit_eq_one hβmod hz₀ hNeBot hβlim
  rw [hw, norm_zero] at hnorm
  norm_num at hnorm

/-- **Single-point repelling obstruction with `w₀ ≠ 0` derived from the branch modulus.** This is the
modulus-strengthened form of `false_of_repelling_branch_global`: callers supply the genuine Böttcher
modulus on the basin, and the boundary limit's nonvanishing is proved internally. -/
theorem false_of_repelling_branch_global_modulus {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {c₁ : ℂ}
    {z₀ w₀ d lam : ℂ} {p : ℕ} {β : ℂ → ℂ}
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
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
    False := by
  have hw₀ : w₀ ≠ 0 := boundary_limit_ne_zero hβmod hz₀ hNeBot hβlim
  exact false_of_repelling_branch_global hβan hβesc ha hroot hpartial hd hw₀ hz₀ hNeBot
    hβlim hβrel hβne hFz hlam hres

end Bottcher

namespace Bottcher

/-- **Slit-free Böttcher modulus on the escape region.** The older modulus theorem is stated on
`escapeOpen c ∩ slitPlane`; the branch-free Green reconciliation gives the same identity on all of
`escapeOpen c`. -/
theorem norm_bottcherCoord_eq_exp_green_escape {c z : ℂ} (hz : z ∈ escapeOpen c) :
    ‖bottcherCoord c z‖ = Real.exp (greenLimit c z) := by
  calc
    ‖bottcherCoord c z‖ = Real.exp (greenLogNorm c z) := by
      rw [greenLogNorm, Real.exp_log (norm_pos_iff.mpr (bottcherCoord_ne_zero c z))]
    _ = Real.exp (greenLimit c z) := by
      rw [greenLogNorm_eq_greenLimit_escape hz]

/-- **Global branch from coherent levels, preserving nonvanishing.** This is the value-exposing version
of `exists_global_branch_of_coherent_levels`: the same least-level colimit is analytic and anchored on
`escapeOpen`, and because it agrees pointwise with some nonzero level branch at every basin point, it is
nonzero on the whole basin. -/
theorem exists_global_branch_of_coherent_levels_nonzero (c : ℂ) (βlev : ℕ → ℂ → ℂ)
    (hanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c n))
    (hcoherent : ∀ n, ∀ z ∈ escapeLevel c n, βlev (n + 1) z = βlev n z)
    (hanchor : ∀ z ∈ escapeOpen c, βlev 0 z = bottcherCoord c z)
    (hne : ∀ n, ∀ z ∈ escapeLevel c n, βlev n z ≠ 0) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0) := by
  have hcoh_le : ∀ {n m : ℕ}, n ≤ m → ∀ z ∈ escapeLevel c n, βlev m z = βlev n z := by
    intro n m h
    induction m with
    | zero => intro z hz; simp [Nat.le_zero.mp h]
    | succ k ih =>
      intro z hz
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h' | h'
      · have hk : n ≤ k := Nat.lt_succ_iff.mp h'
        rw [hcoherent k z (escapeLevel_subset_of_le c hk hz), ih hk z hz]
      · subst h'; rfl
  classical
  set β : ℂ → ℂ := fun z => if h : ∃ n, z ∈ escapeLevel c n then βlev (Nat.find h) z else 0 with hβdef
  have hβval : ∀ z (n : ℕ), z ∈ escapeLevel c n → β z = βlev n z := by
    intro z n hz
    have hex : ∃ k, z ∈ escapeLevel c k := ⟨n, hz⟩
    have hfind : Nat.find hex ≤ n := Nat.find_le hz
    have hzfind : z ∈ escapeLevel c (Nat.find hex) := Nat.find_spec hex
    rw [hβdef]
    simp only [dif_pos hex]
    rw [hcoh_le hfind z hzfind]
  refine ⟨β, ?_, ?_, ?_⟩
  · intro z hz
    rw [compl_filledJulia_eq_iUnion_level, Set.mem_iUnion] at hz
    obtain ⟨n, hzn⟩ := hz
    have hloc : β =ᶠ[𝓝 z] βlev n := by
      filter_upwards [(isOpen_escapeLevel c n).mem_nhds hzn] with w hw
      exact hβval w n hw
    exact (hanalytic n z hzn).congr hloc.symm
  · intro z hz
    have hz0 : z ∈ escapeLevel c 0 := by rw [escapeLevel_zero]; exact hz
    rw [hβval z 0 hz0, hanchor z hz]
  · intro z hz
    rw [compl_filledJulia_eq_iUnion_level, Set.mem_iUnion] at hz
    obtain ⟨n, hzn⟩ := hz
    rw [hβval z n hzn]
    exact hne n z hzn

/-- **Per-level roots assemble to a nonvanishing global branch.** This strengthens
`exists_global_branch_of_level_roots` by carrying the level-branch nonvanishing through the colimit. -/
theorem exists_global_branch_of_level_roots_nonzero (c : ℂ) (βlev : ℕ → ℂ → ℂ)
    (hanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c n))
    (hpow : ∀ n, ∀ z ∈ escapeLevel c n, (βlev n z) ^ (2 ^ n) = bottcherCoord c ((quadratic c)^[n] z))
    (hne : ∀ n, ∀ z ∈ escapeLevel c n, βlev n z ≠ 0)
    (hanchorEsc : ∀ n, ∀ z ∈ escapeOpen c, βlev n z = bottcherCoord c z) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0) :=
  exists_global_branch_of_coherent_levels_nonzero c βlev hanalytic
    (levelBranch_coherent_of_pow c βlev hanalytic hpow hne hanchorEsc)
    (fun z hz => hanchorEsc 0 z hz) hne

/-- **Per-level roots assemble to a modulus-carrying global branch.** The nonvanishing colimit plus the
far-field anchor lets `GlobalBasinBranch.norm_eq_exp_green_basin` spread the Böttcher modulus from
`escapeOpen` to the whole basin. -/
theorem exists_global_branch_of_level_roots_modulus (c : ℂ) (βlev : ℕ → ℂ → ℂ)
    (hanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c n))
    (hpow : ∀ n, ∀ z ∈ escapeLevel c n, (βlev n z) ^ (2 ^ n) = bottcherCoord c ((quadratic c)^[n] z))
    (hne : ∀ n, ∀ z ∈ escapeLevel c n, βlev n z ≠ 0)
    (hanchorEsc : ∀ n, ∀ z ∈ escapeOpen c, βlev n z = bottcherCoord c z) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) := by
  obtain ⟨β, hβan, hβesc, hβ0⟩ :=
    exists_global_branch_of_level_roots_nonzero c βlev hanalytic hpow hne hanchorEsc
  have hβmodE : ∀ z ∈ escapeOpen c, ‖β z‖ = Real.exp (greenFunctionDyn c z) := by
    intro z hz
    rw [hβesc z hz, greenFunctionDyn, if_neg (escapeOpen_subset_compl_filledJulia c hz)]
    exact norm_bottcherCoord_eq_exp_green_escape hz
  have hmodG : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenLimit c z) :=
    norm_eq_exp_green_basin hβan hβ0 hβmodE
  refine ⟨β, hβan, hβesc, hβ0, ?_⟩
  intro z hz
  rw [hmodG z hz, greenFunctionDyn, if_neg hz]

/-- **Square-root families assemble to a modulus-carrying global branch.** This is the strongest
branch constructor needed by the connected hRigid lane: the caller supplies only the coherent square-root
recursion, and Lean creates the `2^n` power law, the nonvanishing global branch, and the basin-wide
Böttcher modulus. -/
theorem exists_global_branch_of_sqrt_family_modulus (c : ℂ) (βlev : ℕ → ℂ → ℂ)
    (hanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c n))
    (hne : ∀ n, ∀ z ∈ escapeLevel c n, βlev n z ≠ 0)
    (hanchorEsc : ∀ n, ∀ z ∈ escapeOpen c, βlev n z = bottcherCoord c z)
    (hsqrt : ∀ n, ∀ z ∈ escapeLevel c (n + 1), (βlev (n + 1) z) ^ 2 = βlev n (quadratic c z)) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) :=
  exists_global_branch_of_level_roots_modulus c βlev hanalytic
    (hpow_of_sqrt_family c βlev (hanchorEsc 0) hsqrt) hne hanchorEsc

/-- **Global modulus branch from simply-connected escape levels.** This combines the recursive
square-root tower constructor with the colimit/modulus assembly: under the concrete geometric input
that each successor escape level is simply connected, Lean constructs the global single-valued
nonvanishing Böttcher branch on the basin and proves its modulus identity. -/
theorem exists_global_branch_of_simplyConnected_levels_modulus (c : ℂ)
    (hsc : ∀ n, IsSimplyConnected (escapeLevel c (n + 1))) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) := by
  obtain ⟨βlev, hanalytic, hne, hanchorEsc, hsqrt⟩ :=
    exists_sqrt_family_of_simplyConnected_levels c hsc
  exact exists_global_branch_of_sqrt_family_modulus c βlev hanalytic hne hanchorEsc hsqrt

end Bottcher

namespace Bottcher

/-- **The boundary-limit exclusion is automatic from modulus.** If `β` has the Böttcher modulus on the
basin and tends to `w₀` at a Julia boundary point, then basin values are frequently different from `w₀`.
Indeed `‖w₀‖ = 1` by the boundary-limit modulus theorem, while every basin point has
`‖β z‖ = exp(G_c z)` with `G_c z ≠ 0`; equality to `w₀` would force `z ∈ K_c`. -/
theorem frequently_ne_boundary_limit_of_modulus {c : ℂ} {β : ℂ → ℂ} {z₀ w₀ : ℂ}
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    (hz₀ : z₀ ∈ filledJulia c) (hNeBot : (𝓝[(filledJulia c)ᶜ] z₀).NeBot)
    (hβlim : Tendsto β (𝓝[(filledJulia c)ᶜ] z₀) (𝓝 w₀)) :
    ∃ᶠ z in 𝓝[(filledJulia c)ᶜ] z₀, β z ≠ w₀ := by
  haveI := hNeBot
  have hw_norm : ‖w₀‖ = 1 := norm_boundary_limit_eq_one hβmod hz₀ hNeBot hβlim
  have hpoint : ∀ z ∈ (filledJulia c)ᶜ, β z ≠ w₀ := by
    intro z hz heq
    have hG0 : greenFunctionDyn c z = 0 := by
      apply Real.exp_injective
      calc
        Real.exp (greenFunctionDyn c z) = ‖β z‖ := by rw [hβmod z hz]
        _ = ‖w₀‖ := by rw [heq]
        _ = 1 := hw_norm
        _ = Real.exp 0 := by rw [Real.exp_zero]
    exact hz ((greenFunctionDyn_eq_zero_iff c z).mp hG0)
  exact (Filter.eventually_of_mem self_mem_nhdsWithin hpoint).frequently

/-- **Single-point repelling obstruction with both boundary side conditions derived from modulus.** This
strengthens `false_of_repelling_branch_global_modulus`: neither `w₀ ≠ 0` nor
`∃ᶠ z, β z ≠ w₀` is an input. Both follow from the basin-wide Böttcher modulus and the basin-side
boundary limit. -/
theorem false_of_repelling_branch_global_modulus_auto_ne {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {c₁ : ℂ}
    {z₀ w₀ d lam : ℂ} {p : ℕ} {β : ℂ → ℂ}
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (ha : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀)
    (hroot : ∑ i ∈ s, a i z₀ * w₀ ^ i = 0)
    (hpartial : HasDerivAt (fun w => ∑ i ∈ s, a i z₀ * w ^ i) d w₀) (hd : d ≠ 0)
    (hz₀ : z₀ ∈ filledJulia c₁)
    (hNeBot : (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot)
    (hβlim : Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀))
    (hβrel : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, ∑ i ∈ s, a i z * (β z) ^ i = 0)
    (hFz : (quadratic c₁)^[p] z₀ = z₀)
    (hlam : HasDerivAt ((quadratic c₁)^[p]) lam z₀)
    (hres : ∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ)) :
    False := by
  have hβne : ∃ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, β z ≠ w₀ :=
    frequently_ne_boundary_limit_of_modulus hβmod hz₀ hNeBot hβlim
  exact false_of_repelling_branch_global_modulus hβan hβesc hβmod ha hroot hpartial hd hz₀ hNeBot
    hβlim hβrel hβne hFz hlam hres

end Bottcher

namespace Bottcher

/-- **Analytic-coefficient relation spreads from any open basin witness.** If the relation function
`∑ᵢ aᵢ(z) β(z)^i` is analytic on the basin and vanishes on a nonempty open subset of the basin, then it
vanishes on the whole basin. This is the open-witness version of `relation_eq_zero_basin_analytic`, used
when the far-field relation is initially known only on the carrier `U`. -/
theorem relation_eq_zero_basin_analytic_of_open {c : ℂ} {β : ℂ → ℂ} {a : ℕ → ℂ → ℂ}
    {s : Finset ℕ} {U : Set ℂ}
    (hUo : IsOpen U) (hUne : U.Nonempty) (hUbasin : U ⊆ (filledJulia c)ᶜ)
    (ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c)ᶜ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c)ᶜ)
    (hrelU : ∀ z ∈ U, ∑ i ∈ s, a i z * (β z) ^ i = 0) :
    ∀ z ∈ (filledJulia c)ᶜ, ∑ i ∈ s, a i z * (β z) ^ i = 0 := by
  have hrelan := analyticOnNhd_relation_analytic ha hβan
  obtain ⟨u, hu⟩ := hUne
  have hev : (fun z => ∑ i ∈ s, a i z * (β z) ^ i) =ᶠ[𝓝 u] (fun _ => (0 : ℂ)) := by
    filter_upwards [hUo.mem_nhds hu] with z hz
    exact hrelU z hz
  intro z hz
  exact (hrelan.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    (isPreconnected_compl_filledJulia c) (hUbasin hu) hev) hz

end Bottcher

namespace Bottcher

/-- **Basin modulus implies nonvanishing.** A branch carrying the Böttcher modulus on the basin is nowhere
zero there, since `Real.exp (G_c z)` is strictly positive. -/
theorem branch_ne_zero_of_modulus {c : ℂ} {β : ℂ → ℂ}
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) :
    ∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0 := by
  intro z hz hzero
  have hnorm := hβmod z hz
  rw [hzero, norm_zero] at hnorm
  exact (ne_of_gt (Real.exp_pos (greenFunctionDyn c z))) hnorm.symm

end Bottcher
