/-
# Descent over a cover sheet: geometric section ⟹ deep-ball independence

`Q62Assembly.noRelation_of_precompMap` carries algebraic independence from the cover field `meroField U`
(base `ℂ(p₀)` via the deck-invariant projection) down to the deep ball `meroField V` (base `ℂ(z)`) along
the cover coordinate `ι = bc∘f^[k] = φc₁^{2^k}`.  It consumes the projection as ABSTRACT germ data: an
element `p₀ : analyticSubring U`, a representative `f₀` with `(p₀ : Germ) = ↑f₀`, an infinitude clause,
and the germ identity `hp0ι : (p₀).compTendsto ι = id` (`p₀∘ι = z`).

This file discharges that abstract data from the GEOMETRIC cover section built in `CoverSheet`
(`exists_coverSheet_section_analytic`): the analytic `pfn = ιf∘ψbc` with `pfn(bc(f^[k] z)) = z`.
`coverSheet_hp0ι` turns the section's pointwise left-inverse property into the exact `hp0ι` germ
identity (mirroring `CoverDeckScaling.compTendsto_germ_fixed`, but for a cover map `ι : V → U` rather
than a self-map).  `noRelation_of_coverSection` then feeds `pfn` as the `noRelation_of_precompMap`
projection: the geometric section IS the analytic germ `p₀`, its membership witness is `⟨pfn, hpan, rfl⟩`,
and `(p₀ : Germ) = ↑pfn` is definitional.  So every germ/analytic hypothesis of the descent is met by
the concrete sheet; the lone remaining input is the cover independence itself (the Kummer close
`q62_disconnected_kummer` over `ℂ(p₀)`).  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.CoverSheet
import GaloisForLFunctions.Bottcher.Q62Assembly

open Set Filter Topology

namespace Bottcher

/-- **Section left-inverse ⟹ the `hp0ι` projection germ identity.**  If `p₀ : analyticSubring U` has
underlying function `g` (`(p₀ : Germ) = ↑g`) and `g` left-inverts the cover map `ι` pointwise on `V`
(`g(ι z) = z` for `z ∈ V`, where `ι : V → U`), then at the germ level the pullback of `p₀` along `ι`
is the identity germ on `V`: `(p₀).compTendsto ι = ↑(w ↦ w)`.  This is EXACTLY the `hp0ι` hypothesis of
`noRelation_of_precompMap`.  Same `Germ.coe_compTendsto`/`Germ.coe_eq`/`eventually_principal` reduction
as `CoverDeckScaling.compTendsto_germ_fixed`, generalized from a self-map `g : U → U` to a genuine cover
map `ι : V → U` with distinct source/target filters — the projection version of the deck-fixing clause. -/
theorem coverSheet_hp0ι {U V : Set ℂ} {ι g : ℂ → ℂ}
    (hmaps : Set.MapsTo ι V U)
    (p₀ : analyticSubring U) (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑g)
    (hgι : ∀ z ∈ V, g (ι z) = z) :
    (p₀ : Germ (𝓟 U) ℂ).compTendsto ι (tendsto_principal_principal.mpr hmaps)
      = (↑(fun w : ℂ => w) : Germ (𝓟 V) ℂ) := by
  rw [hp0, Germ.coe_compTendsto, Germ.coe_eq]
  exact eventually_principal.mpr (fun z hz => hgι z hz)

/-- **Descent over a cover sheet.**  Cover independence over the projection base `ℂ(p₀)` (with `p₀` the
geometric analytic section `pfn` of `CoverSheet`) pulls back to deep-ball independence over `ℂ(z)` along
the cover coordinate `ι = bc∘f^[k]`.  This is `noRelation_of_precompMap` with its abstract projection
germ `p₀` instantiated by the concrete section `pfn`: the membership witness `⟨pfn, hpan, rfl⟩` realizes
`pfn` as an element of `analyticSubring U`, `(p₀ : Germ) = ↑pfn` is definitional, and `coverSheet_hp0ι`
discharges the germ projection identity from `pfn`'s pointwise left-inverse property `hsec`.  So all the
germ/analytic plumbing of the descent is supplied by the geometric sheet.  The remaining hypothesis `h`
is the cover independence `NoRelation ℂ(p₀) F G` — the Kummer close `q62_disconnected_kummer` on the
cover; once it and the identification `precompMeroMap F = phiMero c₁` are in hand, the disconnected
`hDisc` of `q62_independence` is discharged on the sheet.  Axiom-clean. -/
theorem noRelation_of_coverSection {c : ℂ} (k : ℕ) {U V : Set ℂ}
    (hι : AnalyticOnNhd ℂ (fun z => bottcherCoord c ((quadratic c)^[k] z)) V)
    (hmaps : Set.MapsTo (fun z => bottcherCoord c ((quadratic c)^[k] z)) V U)
    (hUc : IsPreconnected U)
    (hopen : IsOpen ((fun z => bottcherCoord c ((quadratic c)^[k] z)) '' V))
    (hne : ((fun z => bottcherCoord c ((quadratic c)^[k] z)) '' V).Nonempty)
    (hUo : IsOpen U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    (pfn : ℂ → ℂ) (hpan : AnalyticOnNhd ℂ pfn U)
    (hsec : ∀ z ∈ V, pfn (bottcherCoord c ((quadratic c)^[k] z)) = z)
    (hinf : (pfn '' U).Infinite)
    (F G : meroField U)
    (h : haveI := isDomain_analyticSubring U hUo hUc hUne
         haveI := (ratfuncToMeroVia (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U) rfl hinf
                     hUo hUc hUne).toAlgebra
         NoRelation (RatFunc ℂ) F G) :
    haveI := isDomain_analyticSubring V hVo hVc hVne
    haveI := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
    NoRelation (RatFunc ℂ)
      (precompMeroMap hι hmaps hUc hopen hne hUo hUne hVo hVc hVne F)
      (precompMeroMap hι hmaps hUc hopen hne hUo hUne hVo hVc hVne G) := by
  set p₀ : analyticSubring U := ⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ with hp0def
  have hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑pfn := rfl
  have hp0ι := coverSheet_hp0ι hmaps p₀ hp0 hsec
  exact noRelation_of_precompMap hι hmaps hUc hopen hne hUo hUne hVo hVc hVne hVinf hp0 hinf hp0ι F G h

end Bottcher
