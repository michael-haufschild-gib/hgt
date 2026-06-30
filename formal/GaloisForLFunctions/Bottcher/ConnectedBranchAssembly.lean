/-
# The connected Böttcher branch, assembled from one isolated per-level root datum

The connected-case global Böttcher branch is reduced (in `BasinColimit`) to producing, at every level
`n`, a single-valued analytic nowhere-zero `2ⁿ`-th root of `bottcherCoord c ∘ f^[n]` on the connected
`escapeLevel c n`. The *existence* of that root is the genuine geometric content — exactly the winding /
`π₁`-divisibility statement (the winding number of `bottcherCoord∘f^[n]` around the hole `K_c` is
divisible by `2ⁿ`) that `CoveringRoot.exists_analyticOnNhd_pow_eq_of_lift` converts into a root.

This file isolates that content as `LevelRootInput c` and discharges *everything downstream of it*: the
roots are renormalised so each restricts to `bottcherCoord c` on the far field (the discrepancy is a
`2ⁿ`-th root of unity, constant on the connected `escapeOpen c` by `const_of_pow_eq_one`, divided out),
and then `exists_global_branch_of_level_roots` glues the levels into the global branch. So the connected
Böttcher uniformisation holds unconditionally once `LevelRootInput c` is supplied — the per-level winding
datum is the only remaining input, cleanly separated from the analytic/colimit plumbing.
-/
import GaloisForLFunctions.Bottcher.BasinColimit
import GaloisForLFunctions.Bottcher.BasinConnected
import GaloisForLFunctions.Bottcher.BasinBranchGlue
import GaloisForLFunctions.Bottcher.BottcherCoord
import GaloisForLFunctions.Bottcher.CoveringRoot

open Topology

namespace Bottcher

/-- **The isolated remaining geometric input for the connected case.** At every level `n`, the pullback
`bottcherCoord c ∘ f^[n]` has a single-valued analytic nowhere-zero `2ⁿ`-th root on the connected escape
level `escapeLevel c n`. This is precisely the winding/`π₁`-divisibility content (winding of
`bottcherCoord∘f^[n]` around the hole divisible by `2ⁿ`) supplied by `CoveringRoot`; with it, the whole
connected-branch assembly proceeds. -/
def LevelRootInput (c : ℂ) : Prop :=
  ∀ n : ℕ, ∃ s : ℂ → ℂ, AnalyticOnNhd ℂ s (escapeLevel c n) ∧
    (∀ z ∈ escapeLevel c n, s z ^ (2 ^ n) = bottcherCoord c ((quadratic c)^[n] z)) ∧
    (∀ z ∈ escapeLevel c n, s z ≠ 0)

/-- **The connected global Böttcher branch from the per-level root input.** Given `LevelRootInput c`,
renormalise each level root to agree with `bottcherCoord c` on the far field and glue: the result is a
single-valued analytic branch on the basin `(filledJulia c)ᶜ` extending `bottcherCoord c` on
`escapeOpen c`. -/
theorem exists_global_branch_of_levelRootInput (c : ℂ) (h : LevelRootInput c) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) := by
  classical
  choose s hsan hspow hsne using h
  set dpt : ℂ := ((max 2 ‖c‖ + 1 : ℝ) : ℂ) with hdpt
  have hsub : ∀ n, escapeOpen c ⊆ escapeLevel c n := by
    intro n; rw [← escapeLevel_zero]; exact escapeLevel_subset_of_le c (Nat.zero_le n)
  have hdptEsc : dpt ∈ escapeOpen c := by
    have := deep_mem_escapeLevel c 0; rwa [escapeLevel_zero] at this
  -- the renormalising constant: `ζ n = s n / bottcherCoord` at the deep anchor, a `2ⁿ`-th root of unity
  set ζ : ℕ → ℂ := fun n => s n dpt / bottcherCoord c dpt with hζdef
  have hζne : ∀ n, ζ n ≠ 0 := fun n =>
    div_ne_zero (hsne n dpt (hsub n hdptEsc)) (bottcherCoord_ne_zero c _)
  have hζpow : ∀ n, (ζ n) ^ (2 ^ n) = 1 := by
    intro n
    obtain ⟨hcz, hz2⟩ := mem_escapeOpen_regime hdptEsc
    rw [hζdef]
    simp only
    rw [div_pow, hspow n dpt (hsub n hdptEsc), bottcherCoord_iterate hcz hz2 n, div_self]
    exact pow_ne_zero _ (bottcherCoord_ne_zero c _)
  -- the discrepancy `s n / bottcherCoord` is constant `= ζ n` on the connected far field
  have hξconst : ∀ n, ∀ z ∈ escapeOpen c, s n z / bottcherCoord c z = ζ n := by
    intro n
    have hξc : ContinuousOn (fun z => s n z / bottcherCoord c z) (escapeOpen c) := by
      apply ContinuousOn.div
      · exact ((hsan n).continuousOn).mono (hsub n)
      · exact (analyticOnNhd_bottcherCoord_full c).continuousOn
      · exact fun z _ => bottcherCoord_ne_zero c _
    have hξpow : ∀ z ∈ escapeOpen c, (fun z => s n z / bottcherCoord c z) z ^ (2 ^ n) = 1 := by
      intro z hz
      obtain ⟨hcz, hz2⟩ := mem_escapeOpen_regime hz
      simp only
      rw [div_pow, hspow n z (hsub n hz), bottcherCoord_iterate hcz hz2 n, div_self]
      exact pow_ne_zero _ (bottcherCoord_ne_zero c _)
    intro z hz
    exact const_of_pow_eq_one (isConnected_escapeOpen c).isPreconnected hξc (by positivity)
      hξpow hz hdptEsc
  -- the renormalised family `βlev n = s n / ζ n`
  set βlev : ℕ → ℂ → ℂ := fun n z => s n z / ζ n with hβdef
  refine exists_global_branch_of_level_roots c βlev ?_ ?_ ?_ ?_
  · -- analytic
    intro n z hz
    exact (hsan n z hz).div_const
  · -- `2ⁿ`-th power law
    intro n z hz
    show (s n z / ζ n) ^ (2 ^ n) = bottcherCoord c ((quadratic c)^[n] z)
    rw [div_pow, hζpow n, div_one, hspow n z hz]
  · -- nowhere zero
    intro n z hz
    exact div_ne_zero (hsne n z hz) (hζne n)
  · -- anchored to `bottcherCoord` on the far field
    intro n z hz
    have hc := hξconst n z hz
    rw [div_eq_iff (bottcherCoord_ne_zero c z)] at hc
    show s n z / ζ n = bottcherCoord c z
    rw [hc]
    exact mul_div_cancel_left₀ (bottcherCoord c z) (hζne n)

/-- **One level of `LevelRootInput` from the winding lift (CoveringRoot, applied to `bottcherCoord∘f^[n]`).**
The pullback `bottcherCoord c ∘ f^[n]` is analytic and nowhere-zero on the connected open `escapeLevel c n`
(`analyticAt_quadratic_iterate` + `analyticOnNhd_bottcherCoord_full`, `bottcherCoord_ne_zero`). If its
`π₁`-image lands in the `2ⁿ`-th powers of `π₁(ℂ*)` — the canonical winding hypothesis `hlift`, presented
through the bundled nowhere-zero map `gSub = bottcherCoord∘f^[n]` — then it has a single-valued analytic
nowhere-zero `2ⁿ`-th root on the whole level. Running this at every level yields `LevelRootInput c`, which
`exists_global_branch_of_levelRootInput` turns into the global branch: the entire connected case is thus
reduced to the per-level winding hypothesis `hlift`, the only genuinely missing analytic input. -/
theorem exists_levelRoot_of_lift (c : ℂ) (n : ℕ)
    (gSub : C(escapeLevel c n, {w : ℂ // w ≠ 0}))
    (hgSub : ∀ a : escapeLevel c n, (gSub a : ℂ) = bottcherCoord c ((quadratic c)^[n] (a : ℂ)))
    {a₀ : escapeLevel c n} {e₀ : {w : ℂ // w ≠ 0}}
    (he : (⟨(e₀ : ℂ) ^ (2 ^ n), pow_ne_zero (2 ^ n) e₀.2⟩ : {w : ℂ // w ≠ 0}) = gSub a₀)
    (hlift : (FundamentalGroup.map gSub a₀).range ≤
      (FundamentalGroup.mapOfEq
        ⟨fun x : {w : ℂ // w ≠ 0} =>
            (⟨(x : ℂ) ^ (2 ^ n), pow_ne_zero (2 ^ n) x.2⟩ : {w : ℂ // w ≠ 0}), by fun_prop⟩
          he).range) :
    ∃ s : ℂ → ℂ, AnalyticOnNhd ℂ s (escapeLevel c n) ∧
      (∀ z ∈ escapeLevel c n, s z ^ (2 ^ n) = bottcherCoord c ((quadratic c)^[n] z)) ∧
      (∀ z ∈ escapeLevel c n, s z ≠ 0) := by
  have hgan : AnalyticOnNhd ℂ (fun z => bottcherCoord c ((quadratic c)^[n] z)) (escapeLevel c n) :=
    fun z hz => (analyticOnNhd_bottcherCoord_full c _ hz).comp (analyticAt_quadratic_iterate c n z)
  have hne0 : ((2 ^ n : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0)
  exact exists_analyticOnNhd_pow_eq_of_lift (isOpen_escapeLevel c n) (isConnected_escapeLevel c n)
    hgan hne0 gSub hgSub he hlift

end Bottcher
