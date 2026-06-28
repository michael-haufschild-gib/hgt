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
import GaloisForLFunctions.Bottcher.InteriorBoundary
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
    nhdsWithin_compl_filledJulia_neBot_of_not_mem_interior hz₀int
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

/-- **Interior-case natural-boundary contradiction** (complement to `false_of_basin_branch_dendrite`). A
modulus-preserving branch `g` analytic on a ball around a Julia point `z₀` whose ball meets the interior of
`K_c` (the nonempty-interior case), with `‖g‖ = exp(G_c)` and a basin point in the ball, gives `False`: on
the `K_c`-interior `G_c = 0` so `‖g‖ = 1`, while at the basin point `‖g‖ = exp(G_c) > 1`
(`greenLimit_pos_basin`); `InteriorBoundary.no_unit_modulus_open_continuation` (max-modulus) closes it.
Together with the dendrite case this forbids ANY modulus-preserving continuation of `φ_c` across `J_c` for
every connected `c` — the full natural-boundary obstruction, requiring NO multiplier-spectrum input. -/
theorem false_of_basin_branch_interior {c z₀ : ℂ} {r : ℝ} (_hr : 0 < r)
    {g : ℂ → ℂ} (hgan : AnalyticOnNhd ℂ g (Metric.ball z₀ r))
    (hmod : ∀ z ∈ Metric.ball z₀ r, ‖g z‖ = Real.exp (greenFunctionDyn c z))
    (hint : ∃ z ∈ Metric.ball z₀ r, z ∈ interior (filledJulia c))
    (hbasin : ∃ z ∈ Metric.ball z₀ r, z ∉ filledJulia c) :
    False := by
  obtain ⟨zi, hzi_ball, hzi_int⟩ := hint
  refine no_unit_modulus_open_continuation hgan
    (V := interior (filledJulia c) ∩ Metric.ball z₀ r)
    (isOpen_interior.inter Metric.isOpen_ball) Set.inter_subset_right ⟨hzi_int, hzi_ball⟩ ?_ ?_
  · intro z hz
    rw [hmod z hz.2]
    have hg0 : greenFunctionDyn c z = 0 := by
      unfold greenFunctionDyn; rw [if_pos (interior_subset hz.1)]
    rw [hg0, Real.exp_zero]
  · obtain ⟨zb, hzb_ball, hzb_basin⟩ := hbasin
    refine ⟨zb, hzb_ball, ?_⟩
    rw [hmod zb hzb_ball]
    have hgpos : 0 < greenFunctionDyn c zb := by
      unfold greenFunctionDyn; rw [if_neg hzb_basin]; exact greenLimit_pos_basin hzb_basin
    rw [ne_eq, Real.exp_eq_one_iff]; linarith

/-- **Unified natural-boundary obstruction.** ANY branch `g` analytic on a ball around `z₀ ∈ K_c`, with
`‖g‖ = exp(G_c)` on the ball and a basin point in the ball, gives `False` — case-splitting on
`ball ∩ interior(K_c)`: empty ⟹ `no_continuation_dendrite`, nonempty ⟹ `false_of_basin_branch_interior`.
The complete natural-boundary obstruction with NO multiplier-spectrum input. (Usable directly where `‖g‖ =
exp(G_c)` holds on the whole ball — the dendrite/empty-`K_c`-interior case, where it reduces to
`no_continuation_dendrite` using only the basin-side modulus; the `K_c`-interior case additionally needs the
modulus to persist on the interior.) -/
theorem false_of_modulus_branch {c z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    {g : ℂ → ℂ} (hgan : AnalyticOnNhd ℂ g (Metric.ball z₀ r)) (hz₀ : z₀ ∈ filledJulia c)
    (hmod : ∀ z ∈ Metric.ball z₀ r, ‖g z‖ = Real.exp (greenFunctionDyn c z))
    (hbasin : ∃ z ∈ Metric.ball z₀ r, z ∉ filledJulia c) :
    False := by
  by_cases hempty : Metric.ball z₀ r ∩ interior (filledJulia c) = ∅
  · exact no_continuation_dendrite hr hgan hz₀ hempty (fun z hz _ => hmod z hz) hbasin
  · obtain ⟨zi, hzi⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    exact false_of_basin_branch_interior hr hgan hmod ⟨zi, hzi.1, hzi.2⟩ hbasin

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

/-- **Branch following.** A continuous `β` on a preconnected `U`, valued pointwise in a finite family of
pairwise-*separated* continuous branches `w i` (`w i z ≠ w j z` for `i ≠ j`), equals a single branch
`w i₀` on all of `U`. The branch-membership sets partition `U` into finitely many relatively-closed sets,
hence each is relatively clopen; preconnectedness forces the one containing a base point to be all of `U`.
This is the boundary-limit core of the dendrite route: the basin Böttcher branch `β` satisfies the relation
`P(z, β z) = 0`, so it is valued in the (locally separated) root-branches of `P`; on the connected basin
side of a dendrite Julia point it must follow exactly one, giving it a definite boundary value. -/
theorem eq_one_branch_of_valued_in_separated {X : Type*} [TopologicalSpace X] {U : Set X}
    (hUc : IsPreconnected U) {n : ℕ} (w : Fin n → X → ℂ) (β : X → ℂ)
    (hwc : ∀ i, ContinuousOn (w i) U) (hβc : ContinuousOn β U)
    (hsep : ∀ z ∈ U, ∀ i j, i ≠ j → w i z ≠ w j z)
    (hval : ∀ z ∈ U, ∃ i, β z = w i z) {z₀ : X} (hz₀ : z₀ ∈ U) :
    ∃ i, ∀ z ∈ U, β z = w i z := by
  classical
  have hpre : PreconnectedSpace ↥U := (isPreconnected_iff_preconnectedSpace).mp hUc
  set βs : ↥U → ℂ := fun x => β x.val with hβs
  set ws : Fin n → ↥U → ℂ := fun i x => w i x.val with hws
  have hβcont : Continuous βs := continuousOn_iff_continuous_restrict.mp hβc
  have hwcont : ∀ i, Continuous (ws i) := fun i => continuousOn_iff_continuous_restrict.mp (hwc i)
  set S : Fin n → Set ↥U := fun i => {x | βs x = ws i x} with hS
  have hSclosed : ∀ i, IsClosed (S i) := fun i => isClosed_eq hβcont (hwcont i)
  have hpart : ∀ x : ↥U, ∃ i, x ∈ S i := fun x => by
    obtain ⟨i, hi⟩ := hval x.val x.2; exact ⟨i, hi⟩
  have huniq : ∀ x : ↥U, ∀ i j, x ∈ S i → x ∈ S j → i = j := by
    intro x i j hi hj
    by_contra hne
    exact hsep x.val x.2 i j hne (hi.symm.trans hj)
  have hSopen : ∀ i, IsOpen (S i) := by
    intro i
    rw [← isClosed_compl_iff]
    have hcompl : (S i)ᶜ = ⋃ j ∈ ({i}ᶜ : Set (Fin n)), S j := by
      ext x
      simp only [mem_compl_iff, mem_iUnion, mem_compl_iff, mem_singleton_iff, exists_prop]
      constructor
      · intro hx
        obtain ⟨j, hj⟩ := hpart x
        exact ⟨j, fun hji => hx (hji ▸ hj), hj⟩
      · rintro ⟨j, hji, hj⟩ hi
        exact hji (huniq x j i hj hi)
    rw [hcompl]
    exact Set.Finite.isClosed_biUnion (Set.toFinite _) (fun j _ => hSclosed j)
  have hSclopen : ∀ i, IsClopen (S i) := fun i => ⟨hSclosed i, hSopen i⟩
  obtain ⟨i, hi⟩ := hpart ⟨z₀, hz₀⟩
  refine ⟨i, fun z hz => ?_⟩
  have hsub : (univ : Set ↥U) ⊆ S i :=
    isPreconnected_univ.subset_isClopen (hSclopen i) ⟨⟨z₀, hz₀⟩, mem_univ _, hi⟩
  exact hsub (mem_univ (⟨z, hz⟩ : ↥U))

/-- If `β = w` on `U` and `w` is continuous at `z₀`, then `β → w z₀` along `𝓝[U] z₀`. The bridge that turns
`eq_one_branch_of_valued_in_separated` (β follows the analytic root-branch `w` on the basin side) into the
`Tendsto β (𝓝[basin] z₀) (𝓝 w₀)` datum `hβlim` of `false_of_basin_branch_dendrite`, with `w₀ = w z₀` the
limiting (simple) root. -/
theorem tendsto_within_of_eqOn {X : Type*} [TopologicalSpace X] {U : Set X} {z₀ : X} {w β : X → ℂ}
    (hw : ContinuousAt w z₀) (hβw : Set.EqOn β w U) :
    Tendsto β (𝓝[U] z₀) (𝓝 (w z₀)) := by
  have hmem : ∀ᶠ z in 𝓝[U] z₀, z ∈ U := self_mem_nhdsWithin
  have hcongr : w =ᶠ[𝓝[U] z₀] β := hmem.mono (fun z hz => (hβw hz).symm)
  exact (hw.tendsto.mono_left nhdsWithin_le_nhds).congr' hcongr

/-- **Root exhaustion.** A degree-`d` polynomial over `ℂ` (`d ≥ 1`) with `d` known distinct roots `g k`
has no other roots: every root equals some `g k`. (The `d` distinct roots fill `roots.toFinset`, whose card
is `≤ natDegree = d`, so the image of `g` *is* the whole root set.) The combinatorial heart of "the analytic
branches exhaust the fiber roots": with it, `β` (satisfying the relation, hence valued in the fiber roots of
`P`) is seen to be valued in the separated branch family, feeding `eq_one_branch_of_valued_in_separated`. -/
theorem root_eq_of_card_branches {q : Polynomial ℂ} {d : ℕ} (hd1 : 1 ≤ d) (hd : q.natDegree = d)
    (g : Fin d → ℂ) (hginj : Function.Injective g) (hgroot : ∀ k, q.eval (g k) = 0)
    {ζ : ℂ} (hζ : q.eval ζ = 0) : ∃ k, ζ = g k := by
  classical
  have hq0 : q ≠ 0 := fun h => by rw [h, Polynomial.natDegree_zero] at hd; omega
  have himg : (Finset.univ.image g) ⊆ q.roots.toFinset := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨k, rfl⟩ := hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hq0]
    exact hgroot k
  have hcardimg : (Finset.univ.image g).card = d := by
    rw [Finset.card_image_of_injective _ hginj, Finset.card_univ, Fintype.card_fin]
  have hcardroots : q.roots.toFinset.card ≤ d := by
    calc q.roots.toFinset.card ≤ Multiset.card q.roots := Multiset.toFinset_card_le _
      _ ≤ q.natDegree := q.card_roots'
      _ = d := hd
  have heq : Finset.univ.image g = q.roots.toFinset :=
    Finset.eq_of_subset_of_card_le himg (by rw [hcardimg]; exact hcardroots)
  have hζmem : ζ ∈ q.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hq0]; exact hζ
  rw [← heq] at hζmem
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hζmem
  obtain ⟨k, hk⟩ := hζmem
  exact ⟨k, hk.symm⟩

/-- **Modulus propagation (analytic, constant modulus).** If `h` is analytic on a preconnected open `U`
and `‖h‖ = 1` on a nonempty open `V ⊆ U`, then `‖h‖ = 1` on all of `U`. (A unit-modulus point of an open
set is a local max of `‖h‖`, so `h` is locally constant there by `eventually_eq_of_isLocalMax_norm`, hence
constant on the connected `U` by the identity theorem.) The core that propagates a *ratio* modulus
`‖g/h‖ = 1` — i.e. `‖g‖ = ‖h‖` — from the escape region across a whole connected basin neighbourhood:
apply to `g/h` with `g, h` two nonvanishing branches agreeing in modulus on the deep-exterior overlap. -/
theorem norm_eq_one_of_open {h : ℂ → ℂ} {U : Set ℂ} (hUc : IsPreconnected U) (hUo : IsOpen U)
    (hh : AnalyticOnNhd ℂ h U) {V : Set ℂ} (hVo : IsOpen V) (hVsub : V ⊆ U) {v : ℂ} (hvV : v ∈ V)
    (hV1 : ∀ z ∈ V, ‖h z‖ = 1) : ∀ z ∈ U, ‖h z‖ = 1 := by
  have hlm : IsLocalMax (norm ∘ h) v := by
    filter_upwards [hVo.mem_nhds hvV] with z hz
    show ‖h z‖ ≤ ‖h v‖
    rw [hV1 z hz, hV1 v hvV]
  have hdiff : ∀ᶠ z in 𝓝 v, DifferentiableAt ℂ h z := by
    filter_upwards [hUo.mem_nhds (hVsub hvV)] with z hz
    exact (hh z hz).differentiableAt
  have hconst : ∀ᶠ z in 𝓝 v, h z = h v := Complex.eventually_eq_of_isLocalMax_norm hdiff hlm
  have hEq : Set.EqOn h (fun _ => h v) U :=
    hh.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hUc (hVsub hvV) hconst
  intro z hz; rw [hEq hz, hV1 v hvV]

/-- **Modulus matching across a connected basin neighbourhood.** Two nonvanishing analytic branches
`g, h` on a preconnected open `U`, agreeing in modulus (`‖g‖ = ‖h‖`) on a nonempty open `V ⊆ U`, agree in
modulus on all of `U`. This is the form the natural-boundary route consumes: `g` the algebraic branch and
`h` a single-valued Böttcher branch (`‖h‖ = exp G_c`) anchored on the deep-exterior overlap `V`; the
conclusion transports `‖g‖ = exp G_c` inward to the Julia boundary, supplying the `hβmod` datum of
`false_of_basin_branch_dendrite`. Proof: `g/h` is analytic, nonzero, unit-modulus on `V`; apply
`norm_eq_one_of_open`. -/
theorem norm_eq_of_norm_eq_on_open {g h : ℂ → ℂ} {U : Set ℂ} (hUc : IsPreconnected U) (hUo : IsOpen U)
    (hg : AnalyticOnNhd ℂ g U) (hh : AnalyticOnNhd ℂ h U) (hh0 : ∀ z ∈ U, h z ≠ 0)
    {V : Set ℂ} (hVo : IsOpen V) (hVsub : V ⊆ U) {v : ℂ} (hvV : v ∈ V)
    (hV : ∀ z ∈ V, ‖g z‖ = ‖h z‖) : ∀ z ∈ U, ‖g z‖ = ‖h z‖ := by
  have hratio : ∀ z ∈ U, ‖(fun w => g w / h w) z‖ = ‖g z‖ / ‖h z‖ := fun z _ => by
    rw [norm_div]
  have hV1 : ∀ z ∈ V, ‖(fun w => g w / h w) z‖ = 1 := by
    intro z hz
    rw [hratio z (hVsub hz), hV z hz, div_self (by
      have := hh0 z (hVsub hz); simpa [norm_eq_zero] using this)]
  have hdiv : AnalyticOnNhd ℂ (fun w => g w / h w) U := fun z hz =>
    (hg z hz).div (hh z hz) (hh0 z hz)
  have hall := norm_eq_one_of_open hUc hUo hdiv hVo hVsub hvV hV1
  intro z hz
  have hz1 := hall z hz
  rw [hratio z hz] at hz1
  rw [div_eq_one_iff_eq (by have := hh0 z hz; simpa [norm_eq_zero] using this)] at hz1
  exact hz1

end Bottcher
