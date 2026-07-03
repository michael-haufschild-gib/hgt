/-
# Mixed-case q62, reduced to the tower norm bound

The q62 case split (`q62_phiMero_independence_conditional`) has three branches: both
disconnected, both connected, and **mixed** (one parameter disconnected, one connected).
The both-disconnected branch is supplied geometrically by the dyadic radical tower
(`bottcher_towerDataF_pair`); the both-connected branch by the exposed-tip/rigidity chain.
This file supplies the mixed branch, reduced to a single named geometric input.

The generic monodromy core `q62_disconnected_of_towerData` is agnostic about the second
coordinate: it consumes only (i) transcendence of `φ_{c₂}` and (ii) a `c₁` radical tower whose
extension domain carries a germ `GBExt` restricting to `φ_{c₂}` on the base.  In the mixed case
`c₂ ∈ M` is *connected*, so `bottcherCoord c₂` is already single-valued on the whole basin
`escapeOpen c₂ = {max 2 ‖c₂‖ < ‖z‖} = {2 < ‖z‖}` (as `‖c₂‖ ≤ 2` for `c₂ ∈ M`).  Hence the only
geometric demand on the `c₁` tower is that its extension domain stay in `{2 < ‖z‖}`, and then
`GBExt := φ_{c₂}`-germ on `Ext` discharges the compatibility clause for free.  Transcendence of
`φ_{c₂}` comes from the connected natural-boundary route
(`phiMero_transcendental_of_mem_mandelbrot`).

* `subset_escapeOpen_of_two_lt_of_mem_mandelbrot` — `{2 < ‖z‖} ⊆ escapeOpen c₂` for `c₂ ∈ M`.
* `restrictAnalytic_phiAnalytic` — restriction commutes with the `φ_c` germ.
* `q62_phiMero_mixed_of_normBoundedTower` — the mixed capstone: disconnected `c₁` radical tower
  with `∀ z ∈ Ext, 2 < ‖z‖` + connected `c₂ ∈ M ∖ {0,−2}` ⟹ `NoRelation`.

So the mixed case is now conditional on exactly the tower norm bound (task B8): a `c₁` dyadic
radical tower whose `Ext` avoids the closed disk of radius `2`.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.ExtendedNonSquare
import GaloisForLFunctions.Bottcher.ConnectedTranscendenceUnconditional
import GaloisForLFunctions.Bottcher.GreenBallPinch
import GaloisForLFunctions.Bottcher.Q62Field

open Polynomial Set Metric Filter
open scoped Topology

namespace Bottcher

/-- For `c ∈ mandelbrot` (so `‖c‖ ≤ 2`), a set on which `2 < ‖z‖` lies in `escapeOpen c`. -/
theorem subset_escapeOpen_of_two_lt_of_mem_mandelbrot {c : ℂ} (hc : c ∈ mandelbrot)
    {S : Set ℂ} (hS : ∀ z ∈ S, 2 < ‖z‖) : S ⊆ escapeOpen c := by
  intro z hz
  simp only [escapeOpen, mem_setOf_eq]
  have h2 : ‖c‖ ≤ 2 := norm_le_two_of_mem_mandelbrot hc
  rw [max_eq_left h2]
  exact hS z hz

/-- **Restriction commutes with `phiAnalytic`.** Both sides are the germ of `bottcherCoord c`. -/
theorem restrictAnalytic_phiAnalytic {U V : Set ℂ} (hVU : V ⊆ U) (c : ℂ)
    (hU : U ⊆ escapeOpen c) (hV : V ⊆ escapeOpen c) :
    restrictAnalytic hVU (phiAnalytic c hU) = phiAnalytic c hV := by
  apply Subtype.ext
  show (((phiAnalytic c hU : analyticSubring U) : Filter.Germ (𝓟 U) ℂ).compTendsto id
      (Filter.tendsto_principal_principal.mpr (fun x hx => hVU hx)))
    = ((phiAnalytic c hV : analyticSubring V) : Filter.Germ (𝓟 V) ℂ)
  have h1 : ((phiAnalytic c hU : analyticSubring U) : Filter.Germ (𝓟 U) ℂ)
      = Filter.Germ.coeRingHom (𝓟 U) (bottcherCoord c) := rfl
  rw [h1]
  show (((bottcherCoord c : ℂ → ℂ) : Filter.Germ (𝓟 U) ℂ).compTendsto id _)
    = ((phiAnalytic c hV : analyticSubring V) : Filter.Germ (𝓟 V) ℂ)
  rw [Filter.Germ.coe_compTendsto]
  rfl

/-- **Mixed-case q62 from a norm-bounded `c₁` scaffold tower.**  For a disconnected coordinate
`φ_{c₁}` supplied by the dyadic radical tower (winding monodromy) whose extension domain `Ext`
stays in `{2 < ‖z‖}`, paired with a *connected* `c₂ ∈ M ∖ {0,−2}`, the two Böttcher coordinates
are algebraically independent over `ℂ(z)`.  The norm bound `∀ z ∈ Ext, 2 < ‖z‖` is exactly what
lets `bottcherCoord c₂` (single-valued on `escapeOpen c₂ ⊇ {2 < ‖z‖}` since `‖c₂‖ ≤ 2`) supply the
`GBExt` compatibility clause the generic core needs; transcendence of `φ_{c₂}` comes from the
connected natural-boundary route.  This is the mixed branch of the q62 case split, reduced to
exactly the tower norm bound. -/
theorem q62_phiMero_mixed_of_normBoundedTower
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hc₂M : c₂ ∈ mandelbrot) (hc₂0 : c₂ ≠ 0) (hc₂2 : c₂ ≠ -2)
    (towerScaffold : ∀ d : ℕ, ∃ (Ext : Set ℂ)
        (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
        (hUExt : U ⊆ Ext) (F : ℂ → ℂ) (aExt : analyticSubring Ext) (k : ℕ),
        1 ≤ k ∧ d < 2 ^ k ∧
        AnalyticOnNhd ℂ F Ext ∧ (∀ z ∈ Ext, F z ≠ 0) ∧
        (Filter.Germ.coeRingHom (𝓟 Ext) F) = (aExt : Filter.Germ (𝓟 Ext) ℂ) ∧
        restrictAnalytic hUExt aExt = (phiAnalytic c₁ hU₁) ^ (2 ^ k) ∧
        (∀ z ∈ Ext, 2 < ‖z‖) ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, γ θ ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi), logDeriv F (γ θ) * γ' θ)
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hGtr₂ : Transcendental (RatFunc ℂ) (phiMero c₂ hU₂) :=
    phiMero_transcendental_of_mem_mandelbrot hUo hUc hUne hUinf hc₂M hc₂0 hc₂2 hU₂
  have hF₁ : phiMero c₁ hU₁ ≠ 0 := phiMero_ne_zero hUo hUc hUne hU₁
  apply q62_disconnected_of_towerData hUo hUc hUne hUinf
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) hF₁ hGtr₂
  intro d
  obtain ⟨Ext, hExto, hExtc, hExtinf, hUExt, F, aExt, k, hk1, hdk, hFan, hFne, hae, hrad,
    hnorm, hloops⟩ := towerScaffold d
  have hExtesc : Ext ⊆ escapeOpen c₂ :=
    subset_escapeOpen_of_two_lt_of_mem_mandelbrot hc₂M hnorm
  exact ⟨Ext, hExto, hExtc, hExtinf, hUExt, F, aExt, phiAnalytic c₂ hExtesc, k, hk1, hdk,
    hFan, hFne, hae, hrad, restrictAnalytic_phiAnalytic hUExt c₂ hExtesc hU₂, hloops⟩

end Bottcher
