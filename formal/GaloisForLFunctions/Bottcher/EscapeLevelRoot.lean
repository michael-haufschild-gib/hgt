/-
# The escape-level square root from the winding criterion (connected Böttcher, non-simply-connected)

`BasinColimit.exists_sqrt_pullback_on_simplyConnected` builds the per-level square root branch
`(βnext)² = βlev n ∘ f` only on a **simply-connected** chart of `escapeLevel c (n+1)`; gluing the charts
across the connected (`π₁ = ℤ`) level is left as the "winding step" (`hagree` in
`exists_levelBranch_succ_of_chart_agreement`). For a *connected* filled Julia set the escape level is an
annulus, so the simply-connected hypothesis genuinely fails and the winding step is the whole content.

This file discharges that step with the covering-lift root of `CoveringRoot`: the square root exists on
the *entire* connected escape level (no chart cut, no matching points) as soon as the canonical winding
hypothesis holds — the `π₁`-image of `βlev n ∘ f` lands in the squares, i.e. the winding number of
`βlev n ∘ f` around the hole `K_c` is even. (It is: `f` is degree `2`, so this winding is `2 ·
wind(βlev n)`. That dynamical evenness is the remaining geometric input, now isolated as exactly the
`π₁` condition.)

New file (hRigid / connected lane). Deps: `CoveringRoot` + `BasinColimit`.
-/
import GaloisForLFunctions.Bottcher.CoveringRoot
import GaloisForLFunctions.Bottcher.BasinColimit

open Topology Complex

namespace Bottcher

/-- **Square-root descent on the whole connected escape level, from the winding criterion.** The
pullback `βlev n ∘ f` is analytic and nowhere-zero on `escapeLevel c (n+1)`
(`f(escapeLevel c (n+1)) ⊆ escapeLevel c n`). If its `π₁`-image lands in the squares of `π₁(ℂ*)` — the
winding-even hypothesis `hlift`, presented through the bundled nowhere-zero map `gSub = βlev n ∘ f` —
then it has a **single-valued analytic square root on all of `escapeLevel c (n+1)`**, with no
simply-connectedness assumption. This is the non-simply-connected generalisation of
`exists_sqrt_pullback_on_simplyConnected`: it removes the chart cut and the matching-point hypotheses,
replacing them with the one canonical winding condition. -/
theorem exists_sqrt_pullback_of_lift (c : ℂ) (n : ℕ)
    (βlevn : ℂ → ℂ) (hβan : AnalyticOnNhd ℂ βlevn (escapeLevel c n))
    (gSub : C(escapeLevel c (n + 1), {w : ℂ // w ≠ 0}))
    (hgSub : ∀ a : escapeLevel c (n + 1), (gSub a : ℂ) = βlevn (quadratic c a))
    {a₀ : escapeLevel c (n + 1)} {e₀ : {w : ℂ // w ≠ 0}}
    (he : (⟨(e₀ : ℂ) ^ 2, pow_ne_zero 2 e₀.2⟩ : {w : ℂ // w ≠ 0}) = gSub a₀)
    (hlift : (FundamentalGroup.map gSub a₀).range ≤
      (FundamentalGroup.mapOfEq
        ⟨fun x : {w : ℂ // w ≠ 0} => (⟨(x : ℂ) ^ 2, pow_ne_zero 2 x.2⟩ : {w : ℂ // w ≠ 0}),
          by fun_prop⟩ he).range) :
    ∃ s : ℂ → ℂ, AnalyticOnNhd ℂ s (escapeLevel c (n + 1)) ∧
      ∀ z ∈ escapeLevel c (n + 1), (s z) ^ 2 = βlevn (quadratic c z) := by
  have hmaps : Set.MapsTo (quadratic c) (escapeLevel c (n + 1)) (escapeLevel c n) :=
    quadratic_mapsTo_escapeLevel c n
  -- the pullback `g = βlev n ∘ f`, analytic and nowhere-zero on the escape level
  have hgan : AnalyticOnNhd ℂ (fun z => βlevn (quadratic c z)) (escapeLevel c (n + 1)) := fun z hz =>
    (hβan _ (hmaps hz)).comp (analyticAt_quadratic c z)
  obtain ⟨s, hsan, hspow, _hsne⟩ :=
    exists_analyticOnNhd_pow_eq_of_lift (isOpen_escapeLevel c (n + 1))
      (isConnected_escapeLevel c (n + 1)) hgan (by norm_num : ((2 : ℕ) : ℂ) ≠ 0)
      gSub hgSub he hlift
  exact ⟨s, hsan, hspow⟩

end Bottcher
