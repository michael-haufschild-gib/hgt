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

open Complex Set Filter Topology

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

end Bottcher
