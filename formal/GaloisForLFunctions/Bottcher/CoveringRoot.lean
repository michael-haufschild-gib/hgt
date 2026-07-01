/-
# Holomorphic `n`-th roots from the covering-space lifting criterion (answer 04, forward direction)

`AnalyticRoot.lean` produces analytic `n`-th roots on **simply-connected** regions
(`exists_analyticOnNhd_pow_eq`, via Mathlib's `exists_continuousOn_pow_eq`) and glues sector roots
once they are *matched* on the overlap (`exists_pow_eq_exterior_of_sectorRoots_match`). The matching —
equivalently, the existence of a single-valued root across a hole — is governed by the **winding
number**: on a non-simply-connected region a nowhere-zero `g` has a single-valued `n`-th root iff the
winding number of `g` around each hole is divisible by `n` (docs/reports/open-problems/04).

This file proves the **forward direction** of that lemma — the genuinely missing analytic content,
which is not in Mathlib — directly from covering-space theory, with no winding integral:

* `Complex.isCoveringMap_npow` : `(· ^ n) : ℂ* → ℂ*` is a covering map.
* `IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le` : the lifting criterion
  `f₊ π₁(A) ≤ p₊ π₁(E)`.

For `p = (· ^ n)` the subgroup `p₊ π₁(ℂ*, e₀)` is exactly the `n`-th powers in `π₁(ℂ*) ≅ ℤ` — i.e. the
multiples of `n`. So the criterion `g₊ π₁(A) ≤ p₊ π₁(ℂ*)` is precisely *winding number divisible by
`n`*, and the lift `F` it produces is a continuous `n`-th root `F^n = g`. The analyticity upgrade
(`analyticOnNhd_of_continuousOn_pow_eq`, already in `AnalyticRoot`) then makes it analytic.

The remaining input is thus the canonical, sharp one — the `π₁`/winding-divisibility hypothesis —
replacing the ad-hoc matching-point hypotheses of the sector route.

New file (hRigid / connected lane). Deps: `AnalyticRoot` + Mathlib covering/lifting.
-/
import GaloisForLFunctions.Bottcher.AnalyticRoot
import GaloisForLFunctions.Bottcher.WindDynamics
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting

open Topology Complex

namespace Bottcher

/-- **Abstract covering-lift `n`-th root.** A continuous nowhere-zero `g : A → ℂ*` on a path-connected,
locally path-connected space `A`, whose induced map on `π₁` lands inside the `n`-th powers (the winding
hypothesis `hlift`), has a continuous `n`-th root `F` (`F a₀ = e₀`, `(F a)^n = g a`). This is the
covering-space heart of the connected Böttcher root: lift `g` through the covering map
`(· ^ n) : ℂ* → ℂ*` (`isCoveringMap_npow`); the lifting criterion
`existsUnique_continuousMap_lifts_of_range_le` makes the lift exist exactly when the winding number of
`g` is divisible by `n`. No analyticity is used here — purely topological. -/
theorem exists_continuous_pow_lift {A : Type*} [TopologicalSpace A]
    [PathConnectedSpace A] [LocPathConnectedSpace A]
    {n : ℕ} (hn : (n : ℂ) ≠ 0)
    (g : C(A, {w : ℂ // w ≠ 0})) (a₀ : A) (e₀ : {w : ℂ // w ≠ 0})
    (he : (⟨(e₀ : ℂ) ^ n, pow_ne_zero n e₀.2⟩ : {w : ℂ // w ≠ 0}) = g a₀)
    (hlift : (FundamentalGroup.map g a₀).range ≤
      (FundamentalGroup.mapOfEq
        ⟨fun x : {w : ℂ // w ≠ 0} => (⟨(x : ℂ) ^ n, pow_ne_zero n x.2⟩ : {w : ℂ // w ≠ 0}),
          by fun_prop⟩ he).range) :
    ∃ F : C(A, {w : ℂ // w ≠ 0}), F a₀ = e₀ ∧ ∀ a, ((F a : ℂ)) ^ n = (g a : ℂ) := by
  have cov := isCoveringMap_npow (𝕜 := ℂ) n hn
  obtain ⟨F, ⟨hF0, hFp⟩, _⟩ := cov.existsUnique_continuousMap_lifts_of_range_le he hlift
  refine ⟨F, hF0, fun a => ?_⟩
  exact congrArg Subtype.val (congrFun hFp a)

/-- **Analytic `n`-th root on a connected open set from the winding criterion.** On an open connected
`U ⊆ ℂ`, an analytic nowhere-zero `g` (presented as a bundled continuous map `gSub` into `ℂ*` with
`gSub = g`) has an **analytic** `n`-th root `s` on `U`, provided the winding/`π₁` lifting criterion
`hlift` holds (the winding number of `g` around every loop is divisible by `n`). The continuous root
comes from `exists_continuous_pow_lift`; analyticity is then automatic
(`analyticOnNhd_of_continuousOn_pow_eq`). This is the non-simply-connected (annulus) generalisation of
`exists_analyticOnNhd_pow_eq`: the forward direction of the holomorphic-root-in-an-annulus lemma. -/
theorem exists_analyticOnNhd_pow_eq_of_lift
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsConnected U)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U)
    {n : ℕ} (hn : (n : ℂ) ≠ 0)
    (gSub : C(U, {w : ℂ // w ≠ 0})) (hgSub : ∀ a : U, (gSub a : ℂ) = g a)
    {a₀ : U} {e₀ : {w : ℂ // w ≠ 0}}
    (he : (⟨(e₀ : ℂ) ^ n, pow_ne_zero n e₀.2⟩ : {w : ℂ // w ≠ 0}) = gSub a₀)
    (hlift : (FundamentalGroup.map gSub a₀).range ≤
      (FundamentalGroup.mapOfEq
        ⟨fun x : {w : ℂ // w ≠ 0} => (⟨(x : ℂ) ^ n, pow_ne_zero n x.2⟩ : {w : ℂ // w ≠ 0}),
          by fun_prop⟩ he).range) :
    ∃ s : ℂ → ℂ, AnalyticOnNhd ℂ s U ∧ (∀ z ∈ U, s z ^ n = g z) ∧ (∀ z ∈ U, s z ≠ 0) := by
  haveI : LocPathConnectedSpace U := hUo.locPathConnectedSpace
  haveI : PathConnectedSpace U := by
    have h := (hUo.isConnected_iff_isPathConnected).mp hUc
    rwa [isPathConnected_iff_pathConnectedSpace] at h
  obtain ⟨F, _hF0, hFpow⟩ := exists_continuous_pow_lift hn gSub a₀ e₀ he hlift
  classical
  set s : ℂ → ℂ := fun z => if h : z ∈ U then ((F ⟨z, h⟩ : {w : ℂ // w ≠ 0}) : ℂ) else 0 with hsdef
  have hsU : ∀ z (h : z ∈ U), s z = (F ⟨z, h⟩ : ℂ) := fun z h => by simp [hsdef, h]
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hn)
  have hg0 : ∀ z ∈ U, g z ≠ 0 := fun z hz => by
    rw [← hgSub ⟨z, hz⟩]; exact (gSub ⟨z, hz⟩).2
  have hscont : ContinuousOn s U := by
    rw [continuousOn_iff_continuous_restrict]
    have hres : U.restrict s = fun a : U => ((F a : {w : ℂ // w ≠ 0}) : ℂ) := by
      funext a; show s a.1 = _; rw [hsU a.1 a.2]
    rw [hres]
    exact continuous_subtype_val.comp F.continuous
  have hspow : ∀ z ∈ U, s z ^ n = g z := by
    intro z hz; rw [hsU z hz, hFpow ⟨z, hz⟩, hgSub ⟨z, hz⟩]
  have hsne : ∀ z ∈ U, s z ≠ 0 := fun z hz => by rw [hsU z hz]; exact (F ⟨z, hz⟩).2
  exact ⟨s, analyticOnNhd_of_continuousOn_pow_eq hUo hn1 hscont hg hg0 hspow, hspow, hsne⟩

/-- **Analytic square root from even transported winding.** This is the answer-04 annular-root
criterion in the form needed by the connected Böttcher tower: the caller supplies the usual analytic
nowhere-zero map `gSub` and proves that every transported loop has even integer degree; the exact
covering-lift hypothesis is produced by `square_range_of_even_winding`, then upgraded to a holomorphic
square root. -/
theorem exists_analyticOnNhd_sq_eq_of_even_winding
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsConnected U)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U)
    (gSub : C(U, {w : ℂ // w ≠ 0})) (hgSub : ∀ a : U, (gSub a : ℂ) = g a)
    {a₀ : U} {e₀ : {w : ℂ // w ≠ 0}}
    (he : (⟨(e₀ : ℂ) ^ 2, pow_ne_zero 2 e₀.2⟩ : {w : ℂ // w ≠ 0}) = gSub a₀)
    (hwind : ∀ p : Path a₀ a₀,
      Even (Pi1CMinusZero.degZ ⟦transLoop (fun a : U => (gSub a : ℂ))
        (continuous_subtype_val.comp gSub.continuous) (fun a => (gSub a).2) p⟧)) :
    ∃ s : ℂ → ℂ, AnalyticOnNhd ℂ s U ∧ (∀ z ∈ U, s z ^ 2 = g z) ∧
      (∀ z ∈ U, s z ≠ 0) := by
  refine exists_analyticOnNhd_pow_eq_of_lift hUo hUc hg (by norm_num : ((2 : ℕ) : ℂ) ≠ 0)
    gSub hgSub he ?_
  exact square_range_of_even_winding gSub he hwind

end Bottcher
