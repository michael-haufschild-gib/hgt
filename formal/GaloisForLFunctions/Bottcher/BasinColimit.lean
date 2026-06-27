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

end Bottcher
