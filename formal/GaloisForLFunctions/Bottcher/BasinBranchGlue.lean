/-
# Connected sheet-selection: the explicit basin branch satisfies the Böttcher functional equation

The index route needs, on a basin sector at a cycle point, a single branch `β` of `φ_{c}` with the
**Böttcher functional equation** `β(f^[p] z) = (β z)^{2^p}` (not the modulus). The explicit branches
`explicitBranch c n` (`ExplicitBranch.lean`) carry the modulus but, at a fixed level `n`,
`explicitBranch c n (f^[p] z)` and `(explicitBranch c n z)^{2^p}` agree only up to a `2^n`-th **root of
unity** — the dyadic monodromy sheet. The functional equation holds exactly on the sheet where that root of
unity is `1`.

This file closes that gap on a **connected** basin region: the root-of-unity discrepancy is a continuous
function into a finite (discrete) set, hence constant on a connected region, hence `≡ 1` once it is `1` at a
single anchor point. So `explicitBranch c n` satisfies the functional equation on a connected basin region
anchored at a point where it agrees with `bottcherCoord`.

* `explicitBranch_FE_pow` — the `2^n`-th powers of the two sides agree (unconditional algebra);
* `const_of_pow_eq_one` — a continuous root-of-unity-valued function on a preconnected set is constant;
* `explicitBranch_FE_of_anchor` — the functional equation on a connected region with a `1`-anchor.

New file (hRigid / connected lane, the basin-branch functional equation = the connected sheet selection).
-/
import GaloisForLFunctions.Bottcher.ExplicitBranch

open Complex Set Filter Topology Bornology

namespace Bottcher

/-- Adjacent explicit levels have equal `2^{n+1}`-th powers (both equal `bottcherCoord (f^[n+1] z)`). -/
theorem explicitBranch_pow_succ_eq (c : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ explicitDomain c n) :
    explicitBranch c (n + 1) z ^ (2 ^ (n + 1)) = explicitBranch c n z ^ (2 ^ (n + 1)) := by
  have hfn : (quadratic c)^[n] z ∈ escapeOpen c := hz.1
  obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime hfn
  rw [explicitBranch_pow c (n + 1) z,
    show (2 : ℕ) ^ (n + 1) = 2 ^ n * 2 from by rw [pow_succ], pow_mul, explicitBranch_pow c n z,
    show (quadratic c)^[n + 1] z = quadratic c ((quadratic c)^[n] z) from
      Function.iterate_succ_apply' (quadratic c) n z]
  exact bottcherCoord_quadratic hc hz2

/-- The adjacent-level ratio is a `2^{n+1}`-th root of unity (pointwise on `explicitDomain c n`). -/
theorem explicitBranch_succ_div_pow_eq_one (c : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ explicitDomain c n) :
    (explicitBranch c (n + 1) z / explicitBranch c n z) ^ (2 ^ (n + 1)) = 1 := by
  have hne : explicitBranch c n z ^ (2 ^ (n + 1)) ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  rw [div_pow, explicitBranch_pow_succ_eq c n hz, div_self hne]

/-- **The functional-equation discrepancy is a root of unity (power form).** For `z` with `f^[n] z` in the
escape regime, the `2^n`-th powers of `explicitBranch c n (f^[p] z)` and `(explicitBranch c n z)^{2^p}`
agree (both equal `bottcherCoord (f^[n+p] z)`). Unconditional `bottcherCoord` algebra. -/
theorem explicitBranch_FE_pow (c : ℂ) (n p : ℕ) {z : ℂ}
    (hz : (quadratic c)^[n] z ∈ escapeOpen c) :
    explicitBranch c n ((quadratic c)^[p] z) ^ (2 ^ n)
      = (explicitBranch c n z ^ (2 ^ p)) ^ (2 ^ n) := by
  obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime hz
  rw [explicitBranch_pow c n ((quadratic c)^[p] z),
    ← Function.iterate_add_apply (quadratic c) n p z,
    ← pow_mul (explicitBranch c n z) (2 ^ p) (2 ^ n), mul_comm (2 ^ p) (2 ^ n),
    pow_mul, explicitBranch_pow c n z,
    show n + p = p + n from Nat.add_comm n p, Function.iterate_add_apply (quadratic c) p n z]
  exact bottcherCoord_iterate hc hz2 p

/-- **A continuous root-of-unity-valued function on a preconnected set is constant.** The `N`-th roots of
unity form a finite (discrete) set, so a continuous `ξ` with `ξ^N ≡ 1` maps the preconnected `V` into a
discrete set and is therefore constant (`IsPreconnected.constant_of_mapsTo`). -/
theorem const_of_pow_eq_one {V : Set ℂ} (hVc : IsPreconnected V)
    {ξ : ℂ → ℂ} (hξc : ContinuousOn ξ V) {N : ℕ} (hN : 0 < N)
    (hpow : ∀ z ∈ V, ξ z ^ N = 1) {a b : ℂ} (ha : a ∈ V) (hb : b ∈ V) :
    ξ a = ξ b := by
  have hTfin : {w : ℂ | w ^ N = 1}.Finite := by
    have hpne : (Polynomial.X ^ N - 1 : Polynomial ℂ) ≠ 0 := by
      have := Polynomial.X_pow_sub_C_ne_zero hN (1 : ℂ); simpa using this
    have heq : {w : ℂ | w ^ N = 1} = {w | (Polynomial.X ^ N - 1 : Polynomial ℂ).IsRoot w} := by
      ext w; simp [Polynomial.IsRoot, sub_eq_zero]
    rw [heq]; exact Polynomial.finite_setOf_isRoot hpne
  exact hVc.constant_of_mapsTo hTfin.isDiscrete hξc (fun z hz => hpow z hz) ha hb

/-- **The explicit branch satisfies the Böttcher functional equation on a connected basin region.** Let `V`
be a preconnected region on which `explicitBranch c n` and its `f^[p]`-pullback are nonzero and on which the
discrepancy `ξ(z) = explicitBranch c n (f^[p] z) / (explicitBranch c n z)^{2^p}` is continuous and avoids `0`
(`hξ`), with `f^[n] z ∈ escapeOpen c` throughout (`hesc`). If at a single anchor `z₁ ∈ V` the functional
equation already holds (`hanchor`), then it holds on all of `V`: the discrepancy is a `2^n`-th root of unity
(`explicitBranch_FE_pow`), continuous, hence constant on `V` (`const_of_pow_eq_one`), pinned to `1` by the
anchor. This is the connected sheet-selection delivering the functional equation `β(f^[p] z) = (β z)^{2^p}`
for `β = explicitBranch c n`. -/
theorem explicitBranch_FE_of_anchor (c : ℂ) (n p : ℕ) {V : Set ℂ} (hVc : IsPreconnected V)
    (hesc : ∀ z ∈ V, (quadratic c)^[n] z ∈ escapeOpen c)
    (hne : ∀ z ∈ V, explicitBranch c n z ≠ 0)
    {ξ : ℂ → ℂ}
    (hξdef : ∀ z ∈ V, ξ z = explicitBranch c n ((quadratic c)^[p] z) / (explicitBranch c n z) ^ (2 ^ p))
    (hξc : ContinuousOn ξ V)
    {z₁ : ℂ} (hz₁ : z₁ ∈ V)
    (hanchor : explicitBranch c n ((quadratic c)^[p] z₁) = (explicitBranch c n z₁) ^ (2 ^ p)) :
    ∀ z ∈ V, explicitBranch c n ((quadratic c)^[p] z) = (explicitBranch c n z) ^ (2 ^ p) := by
  -- ξ is a 2^n-th root of unity on V
  have hpow : ∀ z ∈ V, ξ z ^ (2 ^ n) = 1 := by
    intro z hz
    rw [hξdef z hz, div_pow, explicitBranch_FE_pow c n p (hesc z hz),
      div_self (pow_ne_zero _ (pow_ne_zero _ (hne z hz)))]
  -- ξ z₁ = 1 (anchor)
  have hξ1 : ξ z₁ = 1 := by
    rw [hξdef z₁ hz₁, hanchor, div_self (pow_ne_zero _ (hne z₁ hz₁))]
  -- ξ is constant = 1 on V
  intro z hz
  have hconst : ξ z = ξ z₁ :=
    const_of_pow_eq_one hVc hξc (by positivity) hpow hz hz₁
  rw [hξ1] at hconst
  have hzval := hξdef z hz
  rw [hconst] at hzval
  -- hzval : 1 = explicitBranch c n (f^[p] z) / (explicitBranch c n z)^{2^p}
  exact (div_eq_one_iff_eq (pow_ne_zero _ (hne z hz))).mp hzval.symm

/-- **ζ = 1 sheet selection.** On a preconnected far-field region `V ⊆ explicitDomain c n ∩ escapeOpen c`
anchored at a point `z₁` where `explicitBranch c n z₁ = bottcherCoord c z₁`, the explicit branch *equals*
`bottcherCoord c` throughout `V`. (On `escapeOpen` the discrepancy `explicitBranch c n / bottcherCoord c` is
a `2^n`-th root of unity, continuous, hence constant, pinned to `1` by the anchor.) On this sheet the
explicit branch carries `φ_c`'s relation and is the canonical functional-equation anchor — it ties the
explicit branch to the genuine `φ_c` on the far field, from which the relation spreads into the basin by the
identity theorem (`GlobalBasinBranch.relation_eq_zero_basin`). -/
theorem explicitBranch_eq_bottcherCoord_of_anchor (c : ℂ) (n : ℕ) {V : Set ℂ}
    (hVc : IsPreconnected V) (hVdom : V ⊆ explicitDomain c n) (hVesc : V ⊆ escapeOpen c)
    {z₁ : ℂ} (hz₁ : z₁ ∈ V) (hanchor : explicitBranch c n z₁ = bottcherCoord c z₁) :
    ∀ z ∈ V, explicitBranch c n z = bottcherCoord c z := by
  set ξ : ℂ → ℂ := fun z => explicitBranch c n z / bottcherCoord c z with hξdef
  have hpow : ∀ z ∈ V, ξ z ^ (2 ^ n) = 1 := by
    intro z hz
    obtain ⟨ζ, hζ, hsmul⟩ := explicitBranch_isRootOfUnity_smul c n (hVesc hz)
    show (explicitBranch c n z / bottcherCoord c z) ^ (2 ^ n) = 1
    rw [hsmul, mul_div_assoc, div_self (bottcherCoord_ne_zero c z), mul_one, hζ]
  have hξc : ContinuousOn ξ V := by
    apply ContinuousOn.div
    · exact ((analyticOnNhd_explicitBranch c n).continuousOn).mono hVdom
    · exact (differentiableOn_bottcherCoord c).continuousOn.mono hVesc
    · exact fun z _ => bottcherCoord_ne_zero c z
  intro z hz
  have hconst : ξ z = ξ z₁ := const_of_pow_eq_one hVc hξc (by positivity) hpow hz hz₁
  have hξ1 : ξ z₁ = 1 := by
    show explicitBranch c n z₁ / bottcherCoord c z₁ = 1
    rw [hanchor, div_self (bottcherCoord_ne_zero c z₁)]
  rw [hξ1] at hconst
  show explicitBranch c n z = bottcherCoord c z
  have : explicitBranch c n z / bottcherCoord c z = 1 := hconst
  exact (div_eq_one_iff_eq (bottcherCoord_ne_zero c z)).mp this

/-- **Adjacent levels agree on a connected anchored region.** On a preconnected region `V` contained in both
`explicitDomain c n` and `explicitDomain c (n+1)`, anchored at `z₁` where `explicitBranch c (n+1) z₁ =
explicitBranch c n z₁`, the two levels coincide throughout `V`. (Their ratio is a `2^{n+1}`-th root of unity,
continuous, hence constant, pinned to `1` by the anchor.) This is the level-gluing step: chaining it across
levels assembles the single-valued basin branch `β` (the connected Böttcher continuation) from the explicit
per-level pieces. -/
theorem explicitBranch_succ_eq_of_anchor (c : ℂ) (n : ℕ) {V : Set ℂ} (hVc : IsPreconnected V)
    (hVn : V ⊆ explicitDomain c n) (hVn1 : V ⊆ explicitDomain c (n + 1))
    {z₁ : ℂ} (hz₁ : z₁ ∈ V)
    (hanchor : explicitBranch c (n + 1) z₁ = explicitBranch c n z₁) :
    ∀ z ∈ V, explicitBranch c (n + 1) z = explicitBranch c n z := by
  set ξ : ℂ → ℂ := fun z => explicitBranch c (n + 1) z / explicitBranch c n z with hξdef
  have hpow : ∀ z ∈ V, ξ z ^ (2 ^ (n + 1)) = 1 := fun z hz =>
    explicitBranch_succ_div_pow_eq_one c n (hVn hz)
  have hξc : ContinuousOn ξ V := by
    apply ContinuousOn.div
    · exact ((analyticOnNhd_explicitBranch c (n + 1)).continuousOn).mono hVn1
    · exact ((analyticOnNhd_explicitBranch c n).continuousOn).mono hVn
    · exact fun z _ => Complex.exp_ne_zero _
  intro z hz
  have hne1 : explicitBranch c n z₁ ≠ 0 := Complex.exp_ne_zero _
  have hnez : explicitBranch c n z ≠ 0 := Complex.exp_ne_zero _
  have hconst : ξ z = ξ z₁ := const_of_pow_eq_one hVc hξc (by positivity) hpow hz hz₁
  have hξ1 : ξ z₁ = 1 := by
    show explicitBranch c (n + 1) z₁ / explicitBranch c n z₁ = 1
    rw [hanchor, div_self hne1]
  rw [hξ1] at hconst
  have heqv : explicitBranch c (n + 1) z / explicitBranch c n z = 1 := hconst
  exact (div_eq_one_iff_eq hnez).mp heqv

/-- **Multi-level power equality.** For `n ≤ m` and `z ∈ explicitDomain c n`, the levels `m` and `n` have
equal `2^m`-th powers: both equal `bottcherCoord (f^[m] z)` (using `bottcherCoord_iterate` to relate
`f^[m] z` and `f^[n] z`). Generalises `explicitBranch_pow_succ_eq` to arbitrary level gaps. -/
theorem explicitBranch_pow_eq_of_le (c : ℂ) {n m : ℕ} (hnm : n ≤ m) {z : ℂ}
    (hz : z ∈ explicitDomain c n) :
    explicitBranch c m z ^ (2 ^ m) = explicitBranch c n z ^ (2 ^ m) := by
  have hfn : (quadratic c)^[n] z ∈ escapeOpen c := hz.1
  obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime hfn
  have hiter : (quadratic c)^[m] z = (quadratic c)^[m - n] ((quadratic c)^[n] z) := by
    rw [← Function.iterate_add_apply]; congr 1; omega
  rw [explicitBranch_pow c m z, hiter, bottcherCoord_iterate hc hz2 (m - n),
    ← explicitBranch_pow c n z, ← pow_mul]
  congr 1
  rw [← pow_add]; congr 1; omega

/-- The level-`m`/level-`n` ratio (`n ≤ m`) is a `2^m`-th root of unity on `explicitDomain c n`. -/
theorem explicitBranch_div_pow_eq_one_le (c : ℂ) {n m : ℕ} (hnm : n ≤ m) {z : ℂ}
    (hz : z ∈ explicitDomain c n) :
    (explicitBranch c m z / explicitBranch c n z) ^ (2 ^ m) = 1 := by
  have hne : explicitBranch c n z ^ (2 ^ m) ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  rw [div_pow, explicitBranch_pow_eq_of_le c hnm hz, div_self hne]

/-- **Multi-level gluing on a connected anchored region.** For `n ≤ m`, on a preconnected `V` contained in
both `explicitDomain c n` and `explicitDomain c m`, anchored at `z₁` where the levels agree, levels `m` and
`n` coincide throughout `V`. (The ratio is a `2^m`-th root of unity, continuous, hence constant, pinned by
the anchor.) Chaining this from a far-field anchor — where every level equals `bottcherCoord` — across the
connected basin is the colimit that assembles the single-valued basin branch `β`. -/
theorem explicitBranch_eq_of_anchor_le (c : ℂ) {n m : ℕ} (hnm : n ≤ m) {V : Set ℂ}
    (hVc : IsPreconnected V) (hVn : V ⊆ explicitDomain c n) (hVm : V ⊆ explicitDomain c m)
    {z₁ : ℂ} (hz₁ : z₁ ∈ V) (hanchor : explicitBranch c m z₁ = explicitBranch c n z₁) :
    ∀ z ∈ V, explicitBranch c m z = explicitBranch c n z := by
  set ξ : ℂ → ℂ := fun z => explicitBranch c m z / explicitBranch c n z with hξdef
  have hpow : ∀ z ∈ V, ξ z ^ (2 ^ m) = 1 := fun z hz =>
    explicitBranch_div_pow_eq_one_le c hnm (hVn hz)
  have hξc : ContinuousOn ξ V := by
    apply ContinuousOn.div
    · exact ((analyticOnNhd_explicitBranch c m).continuousOn).mono hVm
    · exact ((analyticOnNhd_explicitBranch c n).continuousOn).mono hVn
    · exact fun z _ => Complex.exp_ne_zero _
  intro z hz
  have hnez : explicitBranch c n z ≠ 0 := Complex.exp_ne_zero _
  have hne1 : explicitBranch c n z₁ ≠ 0 := Complex.exp_ne_zero _
  have hconst : ξ z = ξ z₁ := const_of_pow_eq_one hVc hξc (by positivity) hpow hz hz₁
  have hξ1 : ξ z₁ = 1 := by
    show explicitBranch c m z₁ / explicitBranch c n z₁ = 1
    rw [hanchor, div_self hne1]
  rw [hξ1] at hconst
  exact (div_eq_one_iff_eq hnez).mp hconst

/-- **Composition–level identity (unconditional).** `explicitBranch c n (f^[p] z) = (explicitBranch c (n+p)
z)^{2^p}`: both equal `exp(2⁻ⁿ · bottcherLog (f^[n+p] z))` (`f^[n](f^[p] z) = f^[n+p] z` and the exponent
algebra `2⁻ⁿ = 2^p · 2^{-(n+p)}`). Pure `exp`-algebra. This ties the Böttcher functional equation directly to
the level-gluing: `eb(n)∘f^[p] = (eb(n+p))^{2^p}`, so where `eb(n+p) = eb(n)` the functional equation holds. -/
theorem explicitBranch_comp_iterate (c : ℂ) (n p : ℕ) (z : ℂ) :
    explicitBranch c n ((quadratic c)^[p] z) = (explicitBranch c (n + p) z) ^ (2 ^ p) := by
  rw [explicitBranch, explicitBranch, ← Complex.exp_nat_mul,
    show (quadratic c)^[n] ((quadratic c)^[p] z) = (quadratic c)^[n + p] z from
      (Function.iterate_add_apply (quadratic c) n p z).symm]
  congr 1
  push_cast
  rw [pow_add]
  field_simp

/-- **Multi-level gluing, symmetric form.** For *any* levels `n, m` (no order hypothesis): on a preconnected
`V` in both domains, anchored where the levels agree, levels coincide on `V`. -/
theorem explicitBranch_eq_of_anchor (c : ℂ) (n m : ℕ) {V : Set ℂ}
    (hVc : IsPreconnected V) (hVn : V ⊆ explicitDomain c n) (hVm : V ⊆ explicitDomain c m)
    {z₁ : ℂ} (hz₁ : z₁ ∈ V) (hanchor : explicitBranch c m z₁ = explicitBranch c n z₁) :
    ∀ z ∈ V, explicitBranch c m z = explicitBranch c n z := by
  rcases le_total n m with h | h
  · exact explicitBranch_eq_of_anchor_le c h hVc hVn hVm hz₁ hanchor
  · intro z hz
    exact (explicitBranch_eq_of_anchor_le c h hVc hVm hVn hz₁ hanchor.symm z hz).symm

/-- **The Böttcher functional equation from the level-gluing.** On a preconnected `V ⊆ explicitDomain c n ∩
explicitDomain c (n+p)` anchored at `z₁` where `eb(n+p) = eb(n)`, the explicit level-`n` branch satisfies
`eb(n)(f^[p] z) = (eb(n) z)^{2^p}` throughout `V`. (By `explicitBranch_comp_iterate`, `eb(n)(f^[p] z) =
(eb(n+p) z)^{2^p}`, and `eb(n+p)=eb(n)` on `V` by `explicitBranch_eq_of_anchor_le`.) This is the clean form
of the functional equation for the basin branch — it follows directly from gluing levels `n` and `n+p`. -/
theorem explicitBranch_FE_of_glue (c : ℂ) (n p : ℕ) {V : Set ℂ}
    (hVc : IsPreconnected V) (hVn : V ⊆ explicitDomain c n) (hVnp : V ⊆ explicitDomain c (n + p))
    {z₁ : ℂ} (hz₁ : z₁ ∈ V)
    (hanchor : explicitBranch c (n + p) z₁ = explicitBranch c n z₁) :
    ∀ z ∈ V, explicitBranch c n ((quadratic c)^[p] z) = (explicitBranch c n z) ^ (2 ^ p) := by
  have hglue : ∀ z ∈ V, explicitBranch c (n + p) z = explicitBranch c n z :=
    explicitBranch_eq_of_anchor_le c (Nat.le_add_right n p) hVc hVn hVnp hz₁ hanchor
  intro z hz
  rw [explicitBranch_comp_iterate c n p z, hglue z hz]

/-- **Relation continuation by the identity theorem (analytic coefficients).** A relation
`∑ a_i(z)·(β z)^i` with `a_i, β` analytic on a preconnected `V` that vanishes on a nonempty open subset
`W ⊆ V` vanishes on all of `V`. (The relation function is analytic on `V`; vanishing on the open `W` spreads
across the preconnected `V` by the identity theorem.) This carries the relation from a far-field anchor open
set into the basin region for the explicit branch. -/
theorem relation_zero_of_eqOn_open {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {β : ℂ → ℂ} {V W : Set ℂ}
    (hVc : IsPreconnected V)
    (ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) V) (hβ : AnalyticOnNhd ℂ β V)
    (hWo : IsOpen W) (hWsub : W ⊆ V) {z₀ : ℂ} (hz₀ : z₀ ∈ W)
    (hWrel : ∀ z ∈ W, ∑ i ∈ s, a i z * (β z) ^ i = 0) :
    ∀ z ∈ V, ∑ i ∈ s, a i z * (β z) ^ i = 0 := by
  have hrelan : AnalyticOnNhd ℂ (fun z => ∑ i ∈ s, a i z * (β z) ^ i) V := by
    have heq : (fun z => ∑ i ∈ s, a i z * (β z) ^ i)
        = ∑ i ∈ s, (fun z => a i z * (β z) ^ i) := by funext z; rw [Finset.sum_apply]
    rw [heq]
    exact Finset.analyticOnNhd_sum s (fun i hi => (ha i hi).mul (hβ.pow i))
  have hev : (fun z => ∑ i ∈ s, a i z * (β z) ^ i) =ᶠ[𝓝 z₀] (fun _ => (0 : ℂ)) := by
    filter_upwards [hWo.mem_nhds hz₀] with z hz
    exact hWrel z hz
  intro z hz
  exact (hrelan.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hVc (hWsub hz₀) hev) hz

/-- **`bottcherLog` is asymptotic to `Complex.log` at `∞`:** `bottcherLog c z − Complex.log z → 0` as
`z → ∞`, from the bound `‖bottcherLog c z − log z‖ ≤ 2‖c‖/‖z‖² → 0`. The seed for the far-field anchor
`eb(n) = bottcherCoord` (pinning the ζ=1 principal sheet). -/
theorem tendsto_bottcherLog_sub_log (c : ℂ) :
    Tendsto (fun z => bottcherLog c z - Complex.log z) (cobounded ℂ) (𝓝 0) := by
  have hnorm : Tendsto (fun z : ℂ => ‖z‖) (cobounded ℂ) atTop := tendsto_norm_cobounded_atTop
  have hbd : Tendsto (fun z : ℂ => 2 * ‖c‖ / ‖z‖ ^ 2) (cobounded ℂ) (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp hnorm)
  refine squeeze_zero_norm' ?_ hbd
  filter_upwards [hnorm.eventually_gt_atTop (max 2 ‖c‖)] with z hz
  have hc : ‖c‖ ≤ ‖z‖ := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hz)
  have hz2 : 2 < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hz
  exact norm_bottcherLog_sub_log_le hc hz2

/-- **Basin branch with functional equation AND relation, on a connected region.** Assembles the basin
branch `β = explicitBranch c n` carrying *both* the Böttcher functional equation `β(f^[p]z)=(βz)^{2^p}` and
the algebraic relation `∑ a_i(z)(βz)^i=0` on a preconnected `V ⊆ explicitDomain c n ∩ explicitDomain c (n+p)`,
from a single **far-field anchor** `W ⊆ V` where `eb(n)=eb(n+p)=bottcherCoord` and the relation holds for
`bottcherCoord`. (The anchor pins the level-gluing for the functional equation — `explicitBranch_FE_of_glue` —
and provides the relation's vanishing seed for the identity theorem — `relation_zero_of_eqOn_open`.) This is
the local form of the basin branch the index route consumes; the remaining inputs are the geometric ones: a
connected region reaching from a far-field anchor to the cycle point, and the anchor itself
(`eb(n)=bottcherCoord`, the ζ=1 sheet on the principal far field). -/
theorem explicitBranch_FE_relation_of_anchor (c : ℂ) (n p : ℕ) {V W : Set ℂ}
    {a : ℕ → ℂ → ℂ} {s : Finset ℕ}
    (hVc : IsPreconnected V) (hVn : V ⊆ explicitDomain c n) (hVnp : V ⊆ explicitDomain c (n + p))
    (ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) V)
    (hWo : IsOpen W) (hWsub : W ⊆ V) {z₁ : ℂ} (hz₁W : z₁ ∈ W)
    (hanchorN : ∀ z ∈ W, explicitBranch c n z = bottcherCoord c z)
    (hanchorNP : ∀ z ∈ W, explicitBranch c (n + p) z = bottcherCoord c z)
    (hWrel : ∀ z ∈ W, ∑ i ∈ s, a i z * (bottcherCoord c z) ^ i = 0) :
    (∀ z ∈ V, explicitBranch c n ((quadratic c)^[p] z) = (explicitBranch c n z) ^ (2 ^ p)) ∧
      (∀ z ∈ V, ∑ i ∈ s, a i z * (explicitBranch c n z) ^ i = 0) := by
  have hanchor : explicitBranch c (n + p) z₁ = explicitBranch c n z₁ := by
    rw [hanchorNP z₁ hz₁W, hanchorN z₁ hz₁W]
  refine ⟨explicitBranch_FE_of_glue c n p hVc hVn hVnp (hWsub hz₁W) hanchor, ?_⟩
  have hβan : AnalyticOnNhd ℂ (explicitBranch c n) V := (analyticOnNhd_explicitBranch c n).mono hVn
  have hWrel' : ∀ z ∈ W, ∑ i ∈ s, a i z * (explicitBranch c n z) ^ i = 0 := by
    intro z hz
    rw [show (fun i => a i z * (explicitBranch c n z) ^ i)
        = (fun i => a i z * (bottcherCoord c z) ^ i) from by funext i; rw [hanchorN z hz]]
    exact hWrel z hz
  exact relation_zero_of_eqOn_open hVc ha hβan hWo hWsub hz₁W hWrel'

end Bottcher
