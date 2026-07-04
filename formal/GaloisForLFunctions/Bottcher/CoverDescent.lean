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
import GaloisForLFunctions.Bottcher.Q62Field
import GaloisForLFunctions.U0.U0MStepKummer
import GaloisForLFunctions.Bottcher.Q62Assembly
import GaloisForLFunctions.Bottcher.Rigidity

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

namespace Bottcher

open Set Filter Topology

/-- **Cover-section projection-base lift descent.**  This is the concrete cover-sheet version of
`noRelation_of_precompMap_projection_base_lifts`: the analytic section `pfn` supplies the projection
coordinate `p₀`, `coverSheet_hp0ι` supplies `p₀ ∘ ι = id`, and projection-base lift data on the cover
then descends to algebraic independence of the pulled-back downstairs coordinates. -/
theorem noRelation_of_coverSection_projection_base_lifts {c : ℂ} (k : ℕ) {U V : Set ℂ}
    (hι : AnalyticOnNhd ℂ (fun z => bottcherCoord c ((quadratic c)^[k] z)) V)
    (hmaps : Set.MapsTo (fun z => bottcherCoord c ((quadratic c)^[k] z)) V U)
    (hUc : IsPreconnected U)
    (hopen : IsOpen ((fun z => bottcherCoord c ((quadratic c)^[k] z)) '' V))
    (himgne : ((fun z => bottcherCoord c ((quadratic c)^[k] z)) '' V).Nonempty)
    (hUo : IsOpen U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    (pfn : ℂ → ℂ) (hpan : AnalyticOnNhd ℂ pfn U)
    (hsec : ∀ z ∈ V, pfn (bottcherCoord c ((quadratic c)^[k] z)) = z)
    (hinf : (pfn '' U).Infinite)
    (a₁ a₂ : analyticSubring U) (c₁ c₂ : ℂ) (hcne : c₁ ≠ c₂)
    (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hF0 : haveI := isDomain_analyticSubring U hUo hUc hUne
           algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hG0 : haveI := isDomain_analyticSubring U hUo hUc hUne
           algebraMap (analyticSubring U) (meroField U) a₂ ≠ 0)
    (hliftF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (_hg' : AnalyticOnNhd ℂ g' U)
        (hmapsg : Set.MapsTo g U U) (_hmapsg' : Set.MapsTo g' U U)
        (_hgg' : Set.EqOn (g ∘ g') id U) (_hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        precompAnalytic hg hmapsg (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U)
          = (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U) ∧
        (a₁ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmapsg)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (a₁ : Germ (𝓟 U) ℂ) ∧
        (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmapsg)
          = (a₂ : Germ (𝓟 U) ℂ))
    (hliftG : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (_hg' : AnalyticOnNhd ℂ g' U)
        (hmapsg : Set.MapsTo g U U) (_hmapsg' : Set.MapsTo g' U U)
        (_hgg' : Set.EqOn (g ∘ g') id U) (_hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        precompAnalytic hg hmapsg (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U)
          = (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U) ∧
        (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmapsg)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (a₂ : Germ (𝓟 U) ℂ)) :
    haveI := isDomain_analyticSubring V hVo hVc hVne
    haveI := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
    NoRelation (RatFunc ℂ)
      (precompMeroMap hι hmaps hUc hopen himgne hUo hUne hVo hVc hVne
        (algebraMap (analyticSubring U) (meroField U) a₁))
      (precompMeroMap hι hmaps hUc hopen himgne hUo hUne hVo hVc hVne
        (algebraMap (analyticSubring U) (meroField U) a₂)) := by
  set p₀ : analyticSubring U := ⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ with hp0def
  have hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑pfn := rfl
  have hp0ι := coverSheet_hp0ι hmaps p₀ hp0 hsec
  exact noRelation_of_precompMap_projection_base_lifts hι hmaps hUc hopen himgne
    hUo hUne hVo hVc hVne hVinf hp0 hinf hp0ι
    a₁ a₂ c₁ c₂ hcne hx₁ hx₂ hF0 hG0
    (by simpa [hp0def] using hliftF)
    (by simpa [hp0def] using hliftG)

end Bottcher

namespace Bottcher

open Set Filter Topology

/-- **Cover-section projection-base lift descent, with named downstairs germs.**  After the cover-section
lift theorem gives independence for the pulled-back meromorphic images, `precompMeroMap_algebraMap`
rewrites those images to the algebraMap of any named downstairs analytic germs whose pullback identities
have been supplied.  The final analytic task for actual Böttcher coordinates is therefore exactly the
two identities `precompAnalyticMap aᵢ = phiAnalytic cᵢ`. -/
theorem noRelation_of_coverSection_projection_base_lifts_pullback_eq {c : ℂ} (k : ℕ) {U V : Set ℂ}
    (hι : AnalyticOnNhd ℂ (fun z => bottcherCoord c ((quadratic c)^[k] z)) V)
    (hmaps : Set.MapsTo (fun z => bottcherCoord c ((quadratic c)^[k] z)) V U)
    (hUc : IsPreconnected U)
    (hopen : IsOpen ((fun z => bottcherCoord c ((quadratic c)^[k] z)) '' V))
    (himgne : ((fun z => bottcherCoord c ((quadratic c)^[k] z)) '' V).Nonempty)
    (hUo : IsOpen U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    (pfn : ℂ → ℂ) (hpan : AnalyticOnNhd ℂ pfn U)
    (hsec : ∀ z ∈ V, pfn (bottcherCoord c ((quadratic c)^[k] z)) = z)
    (hinf : (pfn '' U).Infinite)
    (a₁ a₂ : analyticSubring U) (b₁ b₂ : analyticSubring V) (c₁ c₂ : ℂ) (hcne : c₁ ≠ c₂)
    (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hF0 : haveI := isDomain_analyticSubring U hUo hUc hUne
           algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hG0 : haveI := isDomain_analyticSubring U hUo hUc hUne
           algebraMap (analyticSubring U) (meroField U) a₂ ≠ 0)
    (hliftF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (_hg' : AnalyticOnNhd ℂ g' U)
        (hmapsg : Set.MapsTo g U U) (_hmapsg' : Set.MapsTo g' U U)
        (_hgg' : Set.EqOn (g ∘ g') id U) (_hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        precompAnalytic hg hmapsg (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U)
          = (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U) ∧
        (a₁ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmapsg)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (a₁ : Germ (𝓟 U) ℂ) ∧
        (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmapsg)
          = (a₂ : Germ (𝓟 U) ℂ))
    (hliftG : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (_hg' : AnalyticOnNhd ℂ g' U)
        (hmapsg : Set.MapsTo g U U) (_hmapsg' : Set.MapsTo g' U U)
        (_hgg' : Set.EqOn (g ∘ g') id U) (_hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        precompAnalytic hg hmapsg (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U)
          = (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U) ∧
        (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmapsg)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (a₂ : Germ (𝓟 U) ℂ))
    (hpull₁ : precompAnalyticMap hι hmaps a₁ = b₁)
    (hpull₂ : precompAnalyticMap hι hmaps a₂ = b₂) :
    haveI := isDomain_analyticSubring V hVo hVc hVne
    haveI := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
    NoRelation (RatFunc ℂ)
      (algebraMap (analyticSubring V) (meroField V) b₁)
      (algebraMap (analyticSubring V) (meroField V) b₂) := by
  have h := noRelation_of_coverSection_projection_base_lifts k hι hmaps hUc hopen himgne
    hUo hUne hVo hVc hVne hVinf pfn hpan hsec hinf a₁ a₂ c₁ c₂ hcne hx₁ hx₂
    hF0 hG0 hliftF hliftG
  simpa [precompMeroMap_algebraMap, hpull₁, hpull₂] using h

end Bottcher

namespace Bottcher

open Set Filter Topology

/-- **Cover-section projection-base lift descent to actual Böttcher germs.**  Once the two cover germs
pull back to the genuine downstairs Böttcher analytic germs, the projection-base lift data gives the
actual q62 carrier conclusion `NoRelation (RatFunc ℂ) (phiMero c₁) (phiMero c₂)` on `V`. -/
theorem noRelation_phiMero_of_coverSection_projection_base_lifts {c₀ : ℂ} (k : ℕ) {U V : Set ℂ}
    (hι : AnalyticOnNhd ℂ (fun z => bottcherCoord c₀ ((quadratic c₀)^[k] z)) V)
    (hmaps : Set.MapsTo (fun z => bottcherCoord c₀ ((quadratic c₀)^[k] z)) V U)
    (hUc : IsPreconnected U)
    (hopen : IsOpen ((fun z => bottcherCoord c₀ ((quadratic c₀)^[k] z)) '' V))
    (himgne : ((fun z => bottcherCoord c₀ ((quadratic c₀)^[k] z)) '' V).Nonempty)
    (hUo : IsOpen U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    (pfn : ℂ → ℂ) (hpan : AnalyticOnNhd ℂ pfn U)
    (hsec : ∀ z ∈ V, pfn (bottcherCoord c₀ ((quadratic c₀)^[k] z)) = z)
    (hinf : (pfn '' U).Infinite)
    (a₁ a₂ : analyticSubring U) {c₁ c₂ : ℂ} (hcne : c₁ ≠ c₂)
    (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hV₁ : V ⊆ escapeOpen c₁) (hV₂ : V ⊆ escapeOpen c₂)
    (hF0 : haveI := isDomain_analyticSubring U hUo hUc hUne
           algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hG0 : haveI := isDomain_analyticSubring U hUo hUc hUne
           algebraMap (analyticSubring U) (meroField U) a₂ ≠ 0)
    (hliftF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (_hg' : AnalyticOnNhd ℂ g' U)
        (hmapsg : Set.MapsTo g U U) (_hmapsg' : Set.MapsTo g' U U)
        (_hgg' : Set.EqOn (g ∘ g') id U) (_hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        precompAnalytic hg hmapsg (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U)
          = (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U) ∧
        (a₁ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmapsg)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (a₁ : Germ (𝓟 U) ℂ) ∧
        (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmapsg)
          = (a₂ : Germ (𝓟 U) ℂ))
    (hliftG : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (_hg' : AnalyticOnNhd ℂ g' U)
        (hmapsg : Set.MapsTo g U U) (_hmapsg' : Set.MapsTo g' U U)
        (_hgg' : Set.EqOn (g ∘ g') id U) (_hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        precompAnalytic hg hmapsg (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U)
          = (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U) ∧
        (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmapsg)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (a₂ : Germ (𝓟 U) ℂ))
    (hpull₁ : precompAnalyticMap hι hmaps a₁ = phiAnalytic c₁ hV₁)
    (hpull₂ : precompAnalyticMap hι hmaps a₂ = phiAnalytic c₂ hV₂) :
    haveI := isDomain_analyticSubring V hVo hVc hVne
    haveI := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hV₁) (phiMero c₂ hV₂) :=
  noRelation_of_coverSection_projection_base_lifts_pullback_eq k hι hmaps hUc hopen himgne
    hUo hUne hVo hVc hVne hVinf pfn hpan hsec hinf a₁ a₂
    (phiAnalytic c₁ hV₁) (phiAnalytic c₂ hV₂) c₁ c₂ hcne hx₁ hx₂
    hF0 hG0 hliftF hliftG hpull₁ hpull₂

end Bottcher

namespace Bottcher

open Set Filter Topology

/-- **Cover-section projection-base lift descent with the actual cover-coordinate power.**  On the
`k`-th Böttcher cover the pulled-back first coordinate is naturally `φ_{c₁}^{2^k}`, not `φ_{c₁}`.
The projection-base lift descent therefore first gives independence of `(φ_{c₁})^(2^k)` from
`φ_{c₂}` downstairs; the field-generic Kummer descent then removes the finite power and gives the
actual q62 carrier conclusion. -/
theorem noRelation_phiMero_of_coverSection_projection_base_lifts_power_pullback {c₀ : ℂ} (k : ℕ)
    {U V : Set ℂ}
    (hι : AnalyticOnNhd ℂ (fun z => bottcherCoord c₀ ((quadratic c₀)^[k] z)) V)
    (hmaps : Set.MapsTo (fun z => bottcherCoord c₀ ((quadratic c₀)^[k] z)) V U)
    (hUc : IsPreconnected U)
    (hopen : IsOpen ((fun z => bottcherCoord c₀ ((quadratic c₀)^[k] z)) '' V))
    (himgne : ((fun z => bottcherCoord c₀ ((quadratic c₀)^[k] z)) '' V).Nonempty)
    (hUo : IsOpen U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    (pfn : ℂ → ℂ) (hpan : AnalyticOnNhd ℂ pfn U)
    (hsec : ∀ z ∈ V, pfn (bottcherCoord c₀ ((quadratic c₀)^[k] z)) = z)
    (hinf : (pfn '' U).Infinite)
    (a₁ a₂ : analyticSubring U) {c₁ c₂ : ℂ} (hcne : c₁ ≠ c₂)
    (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hV₁ : V ⊆ escapeOpen c₁) (hV₂ : V ⊆ escapeOpen c₂)
    (hF0 : haveI := isDomain_analyticSubring U hUo hUc hUne
           algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hG0 : haveI := isDomain_analyticSubring U hUo hUc hUne
           algebraMap (analyticSubring U) (meroField U) a₂ ≠ 0)
    (hliftF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (_hg' : AnalyticOnNhd ℂ g' U)
        (hmapsg : Set.MapsTo g U U) (_hmapsg' : Set.MapsTo g' U U)
        (_hgg' : Set.EqOn (g ∘ g') id U) (_hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        precompAnalytic hg hmapsg (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U)
          = (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U) ∧
        (a₁ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmapsg)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (a₁ : Germ (𝓟 U) ℂ) ∧
        (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmapsg)
          = (a₂ : Germ (𝓟 U) ℂ))
    (hliftG : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (_hg' : AnalyticOnNhd ℂ g' U)
        (hmapsg : Set.MapsTo g U U) (_hmapsg' : Set.MapsTo g' U U)
        (_hgg' : Set.EqOn (g ∘ g') id U) (_hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        precompAnalytic hg hmapsg (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U)
          = (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U) ∧
        (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmapsg)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (a₂ : Germ (𝓟 U) ℂ))
    (hpull₁ : precompAnalyticMap hι hmaps a₁ = (phiAnalytic c₁ hV₁) ^ (2 ^ k))
    (hpull₂ : precompAnalyticMap hι hmaps a₂ = phiAnalytic c₂ hV₂) :
    haveI := isDomain_analyticSubring V hVo hVc hVne
    haveI := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hV₁) (phiMero c₂ hV₂) := by
  letI := isDomain_analyticSubring V hVo hVc hVne
  letI := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
  have hpow : NoRelation (RatFunc ℂ) ((phiMero c₁ hV₁) ^ (2 ^ k)) (phiMero c₂ hV₂) := by
    have hraw := noRelation_of_coverSection_projection_base_lifts_pullback_eq k hι hmaps hUc hopen
      himgne hUo hUne hVo hVc hVne hVinf pfn hpan hsec hinf a₁ a₂
      ((phiAnalytic c₁ hV₁) ^ (2 ^ k)) (phiAnalytic c₂ hV₂) c₁ c₂ hcne hx₁ hx₂
      hF0 hG0 hliftF hliftG hpull₁ hpull₂
    simpa [phiMero, map_pow] using hraw
  exact U0MStepKummer.noRelation_pow_descent (phiMero c₁ hV₁) (phiMero c₂ hV₂) (2 ^ k) hpow

end Bottcher

namespace Bottcher

open Set Filter Topology

/-- **Pointwise representative equality gives analytic pullback equality.**  If an analytic germ `a` on
`U` is represented by `f`, an analytic germ `b` on `V` is represented by `g`, and `f ∘ ι = g` on `V`,
then the analytic pullback of `a` along `ι` is exactly `b`. -/
theorem precompAnalyticMap_eq_of_comp_eq {U V : Set ℂ} {ι f g : ℂ → ℂ}
    (hι : AnalyticOnNhd ℂ ι V) (hmaps : Set.MapsTo ι V U)
    (a : analyticSubring U) (b : analyticSubring V)
    (ha : (a : Germ (𝓟 U) ℂ) = ↑f)
    (hb : (b : Germ (𝓟 V) ℂ) = ↑g)
    (hfg : ∀ z ∈ V, f (ι z) = g z) :
    precompAnalyticMap hι hmaps a = b := by
  apply Subtype.ext
  show (a : Germ (𝓟 U) ℂ).compTendsto ι (tendsto_principal_principal.mpr hmaps)
      = (b : Germ (𝓟 V) ℂ)
  rw [ha, Germ.coe_compTendsto, hb, Germ.coe_eq]
  exact eventually_principal.mpr hfg

/-- **The cover identity coordinate pulls back to the Böttcher iterate power.**  For
`ι z = φ_c(f_c^[k] z)`, the analytic pullback of the identity coordinate on the cover is
`(φ_c)^(2^k)` on the downstairs escape region. -/
theorem precompAnalyticMap_polyToAnalytic_X_bottcherCoord_iterate {c : ℂ} (k : ℕ) {U V : Set ℂ}
    (hι : AnalyticOnNhd ℂ (fun z => bottcherCoord c ((quadratic c)^[k] z)) V)
    (hmaps : Set.MapsTo (fun z => bottcherCoord c ((quadratic c)^[k] z)) V U)
    (hV : V ⊆ escapeOpen c) :
    precompAnalyticMap hι hmaps (polyToAnalytic U Polynomial.X) = (phiAnalytic c hV) ^ (2 ^ k) := by
  refine precompAnalyticMap_eq_of_comp_eq (f := fun z : ℂ => z)
    (g := fun z : ℂ => bottcherCoord c z ^ (2 ^ k)) hι hmaps (polyToAnalytic U Polynomial.X)
    ((phiAnalytic c hV) ^ (2 ^ k)) ?_ ?_ ?_
  · show ((polyToAnalytic U Polynomial.X : analyticSubring U) : Germ (𝓟 U) ℂ)
        = ↑(fun z : ℂ => z)
    change (↑(fun z : ℂ => Polynomial.eval z (Polynomial.X : Polynomial ℂ)) : Germ (𝓟 U) ℂ)
        = ↑(fun z : ℂ => z)
    congr 1
    funext z
    simp
  · change ((phiAnalytic c hV : analyticSubring V) : Germ (𝓟 V) ℂ) ^ (2 ^ k)
        = ↑(fun z : ℂ => bottcherCoord c z ^ (2 ^ k))
    rw [show ((phiAnalytic c hV : analyticSubring V) : Germ (𝓟 V) ℂ) = ↑(bottcherCoord c) from rfl,
      ← Germ.coe_pow]
    rfl
  · intro z hz
    exact bottcherCoord_iterate (mem_escapeOpen_regime (hV hz)).1 (mem_escapeOpen_regime (hV hz)).2 k

end Bottcher

namespace Bottcher

open Set Filter Topology

/-- **Cover-section descent with the first cover coordinate fixed to the identity.**  This packages the
canonical first pullback equality
`precompAnalyticMap X = (φ_{c₁})^(2^k)` from `bottcherCoord_iterate`; only the second cover-coordinate
pullback to `φ_{c₂}` remains as an input. -/
theorem noRelation_phiMero_of_coverSection_projection_base_lifts_identity_power_pullback
    {c₁ c₂ : ℂ} (k : ℕ) {U V : Set ℂ}
    (hι : AnalyticOnNhd ℂ (fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) V)
    (hmaps : Set.MapsTo (fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) V U)
    (hUc : IsPreconnected U)
    (hopen : IsOpen ((fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) '' V))
    (himgne : ((fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) '' V).Nonempty)
    (hUo : IsOpen U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    (pfn : ℂ → ℂ) (hpan : AnalyticOnNhd ℂ pfn U)
    (hsec : ∀ z ∈ V, pfn (bottcherCoord c₁ ((quadratic c₁)^[k] z)) = z)
    (hinf : (pfn '' U).Infinite)
    (a₂ : analyticSubring U) (hcne : c₁ ≠ c₂)
    (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hV₁ : V ⊆ escapeOpen c₁) (hV₂ : V ⊆ escapeOpen c₂)
    (hF0 : haveI := isDomain_analyticSubring U hUo hUc hUne
           algebraMap (analyticSubring U) (meroField U) (polyToAnalytic U Polynomial.X) ≠ 0)
    (hG0 : haveI := isDomain_analyticSubring U hUo hUc hUne
           algebraMap (analyticSubring U) (meroField U) a₂ ≠ 0)
    (hliftF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (_hg' : AnalyticOnNhd ℂ g' U)
        (hmapsg : Set.MapsTo g U U) (_hmapsg' : Set.MapsTo g' U U)
        (_hgg' : Set.EqOn (g ∘ g') id U) (_hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        precompAnalytic hg hmapsg (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U)
          = (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U) ∧
        ((polyToAnalytic U Polynomial.X : analyticSubring U) : Germ (𝓟 U) ℂ).compTendsto g
            (tendsto_principal_principal.mpr hmapsg)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ)
              * ((polyToAnalytic U Polynomial.X : analyticSubring U) : Germ (𝓟 U) ℂ) ∧
        (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmapsg)
          = (a₂ : Germ (𝓟 U) ℂ))
    (hliftG : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (_hg' : AnalyticOnNhd ℂ g' U)
        (hmapsg : Set.MapsTo g U U) (_hmapsg' : Set.MapsTo g' U U)
        (_hgg' : Set.EqOn (g ∘ g') id U) (_hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        precompAnalytic hg hmapsg (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U)
          = (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U) ∧
        (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmapsg)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (a₂ : Germ (𝓟 U) ℂ))
    (hpull₂ : precompAnalyticMap hι hmaps a₂ = phiAnalytic c₂ hV₂) :
    haveI := isDomain_analyticSubring V hVo hVc hVne
    haveI := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hV₁) (phiMero c₂ hV₂) :=
  noRelation_phiMero_of_coverSection_projection_base_lifts_power_pullback k hι hmaps hUc hopen himgne
    hUo hUne hVo hVc hVne hVinf pfn hpan hsec hinf (polyToAnalytic U Polynomial.X) a₂
    hcne hx₁ hx₂ hV₁ hV₂ hF0 hG0 hliftF hliftG
    (precompAnalyticMap_polyToAnalytic_X_bottcherCoord_iterate k hι hmaps hV₁) hpull₂

end Bottcher

namespace Bottcher

open Set Filter Topology

/-- The identity analytic coordinate is nonzero on an infinite domain. -/
theorem polyToAnalytic_X_ne_zero_of_infinite {U : Set ℂ} (hUinf : U.Infinite) :
    polyToAnalytic U Polynomial.X ≠ 0 := by
  intro h
  have hinj := polyToAnalytic_injective U hUinf
  have hX0 : (Polynomial.X : Polynomial ℂ) = 0 := hinj (by simpa using h)
  exact Polynomial.X_ne_zero hX0

/-- The identity meromorphic coordinate is nonzero on an infinite domain. -/
theorem polyToMero_X_ne_zero_of_infinite {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    algebraMap (analyticSubring U) (meroField U) (polyToAnalytic U Polynomial.X) ≠ 0 := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  intro h
  have han : polyToAnalytic U Polynomial.X = 0 := by
    exact IsFractionRing.injective (analyticSubring U) (meroField U) (by simpa using h)
  exact polyToAnalytic_X_ne_zero_of_infinite hUinf han

/-- **Identity-coordinate cover descent with automatic first nonzero witness.**  The section-image
infinitude hypothesis implies `U` is infinite, hence the cover identity coordinate `X` is nonzero in
`meroField U`; callers only supply nonzero-ness for the second cover coordinate. -/
theorem noRelation_phiMero_of_coverSection_projection_base_lifts_identity_power_pullback_autoFirstNonzero
    {c₁ c₂ : ℂ} (k : ℕ) {U V : Set ℂ}
    (hι : AnalyticOnNhd ℂ (fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) V)
    (hmaps : Set.MapsTo (fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) V U)
    (hUc : IsPreconnected U)
    (hopen : IsOpen ((fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) '' V))
    (himgne : ((fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) '' V).Nonempty)
    (hUo : IsOpen U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    (pfn : ℂ → ℂ) (hpan : AnalyticOnNhd ℂ pfn U)
    (hsec : ∀ z ∈ V, pfn (bottcherCoord c₁ ((quadratic c₁)^[k] z)) = z)
    (hinf : (pfn '' U).Infinite)
    (a₂ : analyticSubring U) (hcne : c₁ ≠ c₂)
    (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hV₁ : V ⊆ escapeOpen c₁) (hV₂ : V ⊆ escapeOpen c₂)
    (hG0 : haveI := isDomain_analyticSubring U hUo hUc hUne
           algebraMap (analyticSubring U) (meroField U) a₂ ≠ 0)
    (hliftF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (_hg' : AnalyticOnNhd ℂ g' U)
        (hmapsg : Set.MapsTo g U U) (_hmapsg' : Set.MapsTo g' U U)
        (_hgg' : Set.EqOn (g ∘ g') id U) (_hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        precompAnalytic hg hmapsg (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U)
          = (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U) ∧
        ((polyToAnalytic U Polynomial.X : analyticSubring U) : Germ (𝓟 U) ℂ).compTendsto g
            (tendsto_principal_principal.mpr hmapsg)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ)
              * ((polyToAnalytic U Polynomial.X : analyticSubring U) : Germ (𝓟 U) ℂ) ∧
        (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmapsg)
          = (a₂ : Germ (𝓟 U) ℂ))
    (hliftG : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (_hg' : AnalyticOnNhd ℂ g' U)
        (hmapsg : Set.MapsTo g U U) (_hmapsg' : Set.MapsTo g' U U)
        (_hgg' : Set.EqOn (g ∘ g') id U) (_hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        precompAnalytic hg hmapsg (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U)
          = (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U) ∧
        (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmapsg)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (a₂ : Germ (𝓟 U) ℂ))
    (hpull₂ : precompAnalyticMap hι hmaps a₂ = phiAnalytic c₂ hV₂) :
    haveI := isDomain_analyticSubring V hVo hVc hVne
    haveI := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hV₁) (phiMero c₂ hV₂) :=
  noRelation_phiMero_of_coverSection_projection_base_lifts_identity_power_pullback k hι hmaps hUc hopen
    himgne hUo hUne hVo hVc hVne hVinf pfn hpan hsec hinf a₂ hcne hx₁ hx₂ hV₁ hV₂
    (polyToMero_X_ne_zero_of_infinite hUo hUc hUne (Set.Infinite.of_image pfn hinf)) hG0
    hliftF hliftG hpull₂

end Bottcher

namespace Bottcher

open Set Filter Topology

/-- If a cover analytic coordinate pulls back to a genuine Böttcher coordinate, then it is nonzero in
`meroField U`: otherwise its meromorphic pullback would force `phiMero` to vanish downstairs. -/
theorem algebraMap_ne_zero_of_precompAnalyticMap_eq_phiAnalytic {U V : Set ℂ} {ι : ℂ → ℂ} {c : ℂ}
    (hι : AnalyticOnNhd ℂ ι V) (hmaps : Set.MapsTo ι V U) (hUc : IsPreconnected U)
    (hopen : IsOpen (ι '' V)) (himgne : (ι '' V).Nonempty)
    (hUo : IsOpen U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty)
    (a : analyticSubring U) (hV : V ⊆ escapeOpen c)
    (hpull : precompAnalyticMap hι hmaps a = phiAnalytic c hV) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    algebraMap (analyticSubring U) (meroField U) a ≠ 0 := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  haveI := isDomain_analyticSubring V hVo hVc hVne
  intro hzero
  have hmap : precompMeroMap hι hmaps hUc hopen himgne hUo hUne hVo hVc hVne
      (algebraMap (analyticSubring U) (meroField U) a) = phiMero c hV := by
    rw [precompMeroMap_algebraMap, hpull]
    rfl
  exact phiMero_ne_zero hVo hVc hVne hV (by rw [← hmap, hzero, map_zero])

/-- **Identity-coordinate cover descent with both nonzero witnesses automatic.**  The first nonzero
witness comes from the section-image infinitude; the second comes from its pullback being the nonzero
Böttcher coordinate `φ_{c₂}`. -/
theorem noRelation_phiMero_of_coverSection_projection_base_lifts_identity_power_pullback_autoNonzero
    {c₁ c₂ : ℂ} (k : ℕ) {U V : Set ℂ}
    (hι : AnalyticOnNhd ℂ (fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) V)
    (hmaps : Set.MapsTo (fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) V U)
    (hUc : IsPreconnected U)
    (hopen : IsOpen ((fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) '' V))
    (himgne : ((fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) '' V).Nonempty)
    (hUo : IsOpen U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    (pfn : ℂ → ℂ) (hpan : AnalyticOnNhd ℂ pfn U)
    (hsec : ∀ z ∈ V, pfn (bottcherCoord c₁ ((quadratic c₁)^[k] z)) = z)
    (hinf : (pfn '' U).Infinite)
    (a₂ : analyticSubring U) (hcne : c₁ ≠ c₂)
    (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hV₁ : V ⊆ escapeOpen c₁) (hV₂ : V ⊆ escapeOpen c₂)
    (hliftF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (_hg' : AnalyticOnNhd ℂ g' U)
        (hmapsg : Set.MapsTo g U U) (_hmapsg' : Set.MapsTo g' U U)
        (_hgg' : Set.EqOn (g ∘ g') id U) (_hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        precompAnalytic hg hmapsg (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U)
          = (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U) ∧
        ((polyToAnalytic U Polynomial.X : analyticSubring U) : Germ (𝓟 U) ℂ).compTendsto g
            (tendsto_principal_principal.mpr hmapsg)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ)
              * ((polyToAnalytic U Polynomial.X : analyticSubring U) : Germ (𝓟 U) ℂ) ∧
        (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmapsg)
          = (a₂ : Germ (𝓟 U) ℂ))
    (hliftG : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (_hg' : AnalyticOnNhd ℂ g' U)
        (hmapsg : Set.MapsTo g U U) (_hmapsg' : Set.MapsTo g' U U)
        (_hgg' : Set.EqOn (g ∘ g') id U) (_hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        precompAnalytic hg hmapsg (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U)
          = (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U) ∧
        (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmapsg)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (a₂ : Germ (𝓟 U) ℂ))
    (hpull₂ : precompAnalyticMap hι hmaps a₂ = phiAnalytic c₂ hV₂) :
    haveI := isDomain_analyticSubring V hVo hVc hVne
    haveI := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hV₁) (phiMero c₂ hV₂) :=
  noRelation_phiMero_of_coverSection_projection_base_lifts_identity_power_pullback_autoFirstNonzero
    k hι hmaps hUc hopen himgne hUo hUne hVo hVc hVne hVinf pfn hpan hsec hinf a₂
    hcne hx₁ hx₂ hV₁ hV₂
    (algebraMap_ne_zero_of_precompAnalyticMap_eq_phiAnalytic hι hmaps hUc hopen himgne hUo hUne
      hVo hVc hVne a₂ hV₂ hpull₂)
    hliftF hliftG hpull₂

end Bottcher

namespace Bottcher

open Set Filter Topology

/-- The second Böttcher coordinate transported to the cover sheet by the analytic section `pfn`: the
analytic germ of `w ↦ φ_c(pfn w)` on the cover domain `U`. -/
noncomputable def coverSectionPhiAnalytic {U : Set ℂ} (c : ℂ) (pfn : ℂ → ℂ)
    (hpan : AnalyticOnNhd ℂ pfn U) (hpmaps : Set.MapsTo pfn U (escapeOpen c)) :
    analyticSubring U :=
  ⟨Germ.coeRingHom (𝓟 U) (fun w => bottcherCoord c (pfn w)),
    ⟨fun w => bottcherCoord c (pfn w),
      (analyticOnNhd_bottcherCoord_full c).comp hpan hpmaps, rfl⟩⟩

/-- Pulling the transported second coordinate `φ_c ∘ pfn` back along the cover coordinate gives the
ordinary downstairs Böttcher coordinate, because `pfn` is a left inverse to the cover map on `V`. -/
theorem precompAnalyticMap_coverSectionPhiAnalytic {c₁ c₂ : ℂ} (k : ℕ) {U V : Set ℂ}
    (hι : AnalyticOnNhd ℂ (fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) V)
    (hmaps : Set.MapsTo (fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) V U)
    (pfn : ℂ → ℂ) (hpan : AnalyticOnNhd ℂ pfn U)
    (hsec : ∀ z ∈ V, pfn (bottcherCoord c₁ ((quadratic c₁)^[k] z)) = z)
    (hpmaps : Set.MapsTo pfn U (escapeOpen c₂)) (hV₂ : V ⊆ escapeOpen c₂) :
    precompAnalyticMap hι hmaps (coverSectionPhiAnalytic c₂ pfn hpan hpmaps)
      = phiAnalytic c₂ hV₂ := by
  refine precompAnalyticMap_eq_of_comp_eq
    (f := fun w : ℂ => bottcherCoord c₂ (pfn w)) (g := bottcherCoord c₂)
    hι hmaps (coverSectionPhiAnalytic c₂ pfn hpan hpmaps) (phiAnalytic c₂ hV₂) ?_ ?_ ?_
  · rfl
  · rfl
  · intro z hz
    change bottcherCoord c₂ (pfn (bottcherCoord c₁ ((quadratic c₁)^[k] z))) = bottcherCoord c₂ z
    rw [hsec z hz]

/-- **Cover-section descent with the second coordinate fixed to `φ_{c₂} ∘ pfn`.**  The first coordinate
is the cover identity `X`, whose pullback is `(φ_{c₁})^(2^k)`; the second coordinate is the transported
Böttcher coordinate on the sheet, whose pullback is `φ_{c₂}`.  Both nonzero witnesses are automatic. -/
theorem noRelation_phiMero_of_coverSection_projection_base_lifts_sectionPhi_autoNonzero
    {c₁ c₂ : ℂ} (k : ℕ) {U V : Set ℂ}
    (hι : AnalyticOnNhd ℂ (fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) V)
    (hmaps : Set.MapsTo (fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) V U)
    (hUc : IsPreconnected U)
    (hopen : IsOpen ((fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) '' V))
    (himgne : ((fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) '' V).Nonempty)
    (hUo : IsOpen U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    (pfn : ℂ → ℂ) (hpan : AnalyticOnNhd ℂ pfn U)
    (hsec : ∀ z ∈ V, pfn (bottcherCoord c₁ ((quadratic c₁)^[k] z)) = z)
    (hinf : (pfn '' U).Infinite)
    (hpmaps₂ : Set.MapsTo pfn U (escapeOpen c₂))
    (hcne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hV₁ : V ⊆ escapeOpen c₁) (hV₂ : V ⊆ escapeOpen c₂)
    (hliftF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (_hg' : AnalyticOnNhd ℂ g' U)
        (hmapsg : Set.MapsTo g U U) (_hmapsg' : Set.MapsTo g' U U)
        (_hgg' : Set.EqOn (g ∘ g') id U) (_hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        precompAnalytic hg hmapsg (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U)
          = (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U) ∧
        ((polyToAnalytic U Polynomial.X : analyticSubring U) : Germ (𝓟 U) ℂ).compTendsto g
            (tendsto_principal_principal.mpr hmapsg)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ)
              * ((polyToAnalytic U Polynomial.X : analyticSubring U) : Germ (𝓟 U) ℂ) ∧
        (coverSectionPhiAnalytic c₂ pfn hpan hpmaps₂ : Germ (𝓟 U) ℂ).compTendsto g
            (tendsto_principal_principal.mpr hmapsg)
          = (coverSectionPhiAnalytic c₂ pfn hpan hpmaps₂ : Germ (𝓟 U) ℂ))
    (hliftG : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (_hg' : AnalyticOnNhd ℂ g' U)
        (hmapsg : Set.MapsTo g U U) (_hmapsg' : Set.MapsTo g' U U)
        (_hgg' : Set.EqOn (g ∘ g') id U) (_hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        precompAnalytic hg hmapsg (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U)
          = (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U) ∧
        (coverSectionPhiAnalytic c₂ pfn hpan hpmaps₂ : Germ (𝓟 U) ℂ).compTendsto g
            (tendsto_principal_principal.mpr hmapsg)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ)
              * (coverSectionPhiAnalytic c₂ pfn hpan hpmaps₂ : Germ (𝓟 U) ℂ)) :
    haveI := isDomain_analyticSubring V hVo hVc hVne
    haveI := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hV₁) (phiMero c₂ hV₂) :=
  noRelation_phiMero_of_coverSection_projection_base_lifts_identity_power_pullback_autoNonzero
    k hι hmaps hUc hopen himgne hUo hUne hVo hVc hVne hVinf pfn hpan hsec hinf
    (coverSectionPhiAnalytic c₂ pfn hpan hpmaps₂) hcne hx₁ hx₂ hV₁ hV₂ hliftF hliftG
    (precompAnalyticMap_coverSectionPhiAnalytic k hι hmaps pfn hpan hsec hpmaps₂ hV₂)

end Bottcher

namespace Bottcher

open Set Filter Topology

/-- Pointwise equality of representatives gives equality after germ precomposition on the same domain. -/
theorem germ_compTendsto_eq_of_comp_eq {U : Set ℂ} {g f h : ℂ → ℂ}
    (hmaps : Set.MapsTo g U U) (a b : analyticSubring U)
    (ha : (a : Germ (𝓟 U) ℂ) = ↑f)
    (hb : (b : Germ (𝓟 U) ℂ) = ↑h)
    (hfg : ∀ z ∈ U, f (g z) = h z) :
    (a : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
      = (b : Germ (𝓟 U) ℂ) := by
  rw [ha, Germ.coe_compTendsto, hb, Germ.coe_eq]
  exact eventually_principal.mpr hfg

/-- Pointwise equality of representatives gives equality after the analytic precomposition operator. -/
theorem precompAnalytic_eq_of_comp_eq {U : Set ℂ} {g f h : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hmaps : Set.MapsTo g U U) (a b : analyticSubring U)
    (ha : (a : Germ (𝓟 U) ℂ) = ↑f)
    (hb : (b : Germ (𝓟 U) ℂ) = ↑h)
    (hfg : ∀ z ∈ U, f (g z) = h z) :
    precompAnalytic hg hmaps a = b := by
  apply Subtype.ext
  exact germ_compTendsto_eq_of_comp_eq hmaps a b ha hb hfg

/-- The polynomial identity coordinate has representative `z ↦ z`. -/
theorem polyToAnalytic_X_germ {U : Set ℂ} :
    ((polyToAnalytic U Polynomial.X : analyticSubring U) : Germ (𝓟 U) ℂ) = ↑(fun z : ℂ => z) := by
  change (↑(fun z : ℂ => Polynomial.eval z (Polynomial.X : Polynomial ℂ)) : Germ (𝓟 U) ℂ)
      = ↑(fun z : ℂ => z)
  congr 1
  funext z
  simp

/-- The germ of `ζ * X` is the pointwise function `z ↦ ζ z`. -/
theorem const_mul_polyToAnalytic_X_germ {U : Set ℂ} (ζ : ℂ) :
    (((constToAnalytic U ζ : analyticSubring U) * (polyToAnalytic U Polynomial.X : analyticSubring U))
        : Germ (𝓟 U) ℂ) = ↑(fun z : ℂ => ζ * z) := by
  rw [polyToAnalytic_X_germ]
  change (↑((fun _ : ℂ => ζ) * (fun z : ℂ => z)) : Germ (𝓟 U) ℂ)
      = ↑(fun z : ℂ => ζ * z)
  rfl

/-- If a deck map acts pointwise as `z ↦ ζ z`, then the identity coordinate scales by `ζ`. -/
theorem polyToAnalytic_X_compTendsto_scale_of_pointwise {U : Set ℂ} {g : ℂ → ℂ} {ζ : ℂ}
    (hmaps : Set.MapsTo g U U) (hscale : ∀ z ∈ U, g z = ζ * z) :
    ((polyToAnalytic U Polynomial.X : analyticSubring U) : Germ (𝓟 U) ℂ).compTendsto g
        (tendsto_principal_principal.mpr hmaps)
      = ((constToAnalytic U ζ : analyticSubring U) : Germ (𝓟 U) ℂ)
          * ((polyToAnalytic U Polynomial.X : analyticSubring U) : Germ (𝓟 U) ℂ) := by
  exact germ_compTendsto_eq_of_comp_eq hmaps (polyToAnalytic U Polynomial.X)
    ((constToAnalytic U ζ : analyticSubring U) * (polyToAnalytic U Polynomial.X : analyticSubring U))
    polyToAnalytic_X_germ (const_mul_polyToAnalytic_X_germ ζ) hscale

/-- The transported section coordinate has representative `w ↦ φ_c(pfn w)`. -/
theorem coverSectionPhiAnalytic_germ {U : Set ℂ} {c : ℂ} {pfn : ℂ → ℂ}
    {hpan : AnalyticOnNhd ℂ pfn U} {hpmaps : Set.MapsTo pfn U (escapeOpen c)} :
    ((coverSectionPhiAnalytic c pfn hpan hpmaps : analyticSubring U) : Germ (𝓟 U) ℂ)
      = ↑(fun w : ℂ => bottcherCoord c (pfn w)) := rfl

/-- The germ of `ζ * (φ_c ∘ pfn)` is the pointwise product. -/
theorem const_mul_coverSectionPhiAnalytic_germ {U : Set ℂ} {c ζ : ℂ} {pfn : ℂ → ℂ}
    {hpan : AnalyticOnNhd ℂ pfn U} {hpmaps : Set.MapsTo pfn U (escapeOpen c)} :
    (((constToAnalytic U ζ : analyticSubring U) * coverSectionPhiAnalytic c pfn hpan hpmaps)
        : Germ (𝓟 U) ℂ) = ↑(fun z : ℂ => ζ * bottcherCoord c (pfn z)) := by
  rw [coverSectionPhiAnalytic_germ]
  change (↑((fun _ : ℂ => ζ) * (fun z : ℂ => bottcherCoord c (pfn z))) : Germ (𝓟 U) ℂ)
      = ↑(fun z : ℂ => ζ * bottcherCoord c (pfn z))
  rfl

/-- If a deck fixes the section projection `pfn`, it fixes the transported coordinate `φ_c ∘ pfn`. -/
theorem coverSectionPhiAnalytic_compTendsto_fix_of_pfn_fixed {U : Set ℂ} {g pfn : ℂ → ℂ} {c : ℂ}
    {hpan : AnalyticOnNhd ℂ pfn U} {hpmaps : Set.MapsTo pfn U (escapeOpen c)}
    (hmaps : Set.MapsTo g U U) (hfix : ∀ z ∈ U, pfn (g z) = pfn z) :
    (coverSectionPhiAnalytic c pfn hpan hpmaps : Germ (𝓟 U) ℂ).compTendsto g
        (tendsto_principal_principal.mpr hmaps)
      = (coverSectionPhiAnalytic c pfn hpan hpmaps : Germ (𝓟 U) ℂ) := by
  refine germ_compTendsto_eq_of_comp_eq hmaps (coverSectionPhiAnalytic c pfn hpan hpmaps)
    (coverSectionPhiAnalytic c pfn hpan hpmaps) coverSectionPhiAnalytic_germ
    coverSectionPhiAnalytic_germ ?_
  intro z hz
  change bottcherCoord c (pfn (g z)) = bottcherCoord c (pfn z)
  rw [hfix z hz]

/-- A pointwise multiplier action on `φ_c ∘ pfn` is exactly the corresponding germ scaling action. -/
theorem coverSectionPhiAnalytic_compTendsto_scale_of_pointwise {U : Set ℂ} {g pfn : ℂ → ℂ} {c ζ : ℂ}
    {hpan : AnalyticOnNhd ℂ pfn U} {hpmaps : Set.MapsTo pfn U (escapeOpen c)}
    (hmaps : Set.MapsTo g U U)
    (hscale : ∀ z ∈ U, bottcherCoord c (pfn (g z)) = ζ * bottcherCoord c (pfn z)) :
    (coverSectionPhiAnalytic c pfn hpan hpmaps : Germ (𝓟 U) ℂ).compTendsto g
        (tendsto_principal_principal.mpr hmaps)
      = ((constToAnalytic U ζ : analyticSubring U) : Germ (𝓟 U) ℂ)
          * (coverSectionPhiAnalytic c pfn hpan hpmaps : Germ (𝓟 U) ℂ) := by
  exact germ_compTendsto_eq_of_comp_eq hmaps (coverSectionPhiAnalytic c pfn hpan hpmaps)
    ((constToAnalytic U ζ : analyticSubring U) * coverSectionPhiAnalytic c pfn hpan hpmaps)
    coverSectionPhiAnalytic_germ const_mul_coverSectionPhiAnalytic_germ hscale

end Bottcher

namespace Bottcher

open Set Filter Topology

/-- **Pointwise deck data version of cover-section descent.**  Instead of asking for the exact germ
`hliftF`/`hliftG` tuples, this wrapper accepts the concrete pointwise deck actions on the cover sheet:
`pfn` is fixed, the cover identity coordinate is scaled by `ζ`, and the transported second coordinate
is fixed/scaled as needed.  The helper lemmas above convert those pointwise identities to the germ
hypotheses consumed by the projection-base descent. -/
theorem noRelation_phiMero_of_coverSection_pointwise_decks_sectionPhi_autoNonzero
    {c₁ c₂ : ℂ} (k : ℕ) {U V : Set ℂ}
    (hι : AnalyticOnNhd ℂ (fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) V)
    (hmaps : Set.MapsTo (fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) V U)
    (hUc : IsPreconnected U)
    (hopen : IsOpen ((fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) '' V))
    (himgne : ((fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) '' V).Nonempty)
    (hUo : IsOpen U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    (pfn : ℂ → ℂ) (hpan : AnalyticOnNhd ℂ pfn U)
    (hsec : ∀ z ∈ V, pfn (bottcherCoord c₁ ((quadratic c₁)^[k] z)) = z)
    (hinf : (pfn '' U).Infinite)
    (hpmaps₂ : Set.MapsTo pfn U (escapeOpen c₂))
    (hcne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hV₁ : V ⊆ escapeOpen c₁) (hV₂ : V ⊆ escapeOpen c₂)
    (hdeckF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (_hg : AnalyticOnNhd ℂ g U) (_hg' : AnalyticOnNhd ℂ g' U)
        (_hmapsg : Set.MapsTo g U U) (_hmapsg' : Set.MapsTo g' U U)
        (_hgg' : Set.EqOn (g ∘ g') id U) (_hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        (∀ z ∈ U, pfn (g z) = pfn z) ∧
        (∀ z ∈ U, g z = ζ₀ * z))
    (hdeckG : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (_hg : AnalyticOnNhd ℂ g U) (_hg' : AnalyticOnNhd ℂ g' U)
        (_hmapsg : Set.MapsTo g U U) (_hmapsg' : Set.MapsTo g' U U)
        (_hgg' : Set.EqOn (g ∘ g') id U) (_hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        (∀ z ∈ U, pfn (g z) = pfn z) ∧
        (∀ z ∈ U, bottcherCoord c₂ (pfn (g z)) = ζ₀ * bottcherCoord c₂ (pfn z))) :
    haveI := isDomain_analyticSubring V hVo hVc hVne
    haveI := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hV₁) (phiMero c₂ hV₂) := by
  refine noRelation_phiMero_of_coverSection_projection_base_lifts_sectionPhi_autoNonzero
    k hι hmaps hUc hopen himgne hUo hUne hVo hVc hVne hVinf pfn hpan hsec hinf hpmaps₂
    hcne hx₁ hx₂ hV₁ hV₂ ?_ ?_
  · intro d
    obtain ⟨ζ₀, g, g', hg, hg', hmapsg, hmapsg', hgg', hg'g, hord, hpfix, hxscale⟩ := hdeckF d
    refine ⟨ζ₀, g, g', hg, hg', hmapsg, hmapsg', hgg', hg'g, hord, ?_, ?_, ?_⟩
    · exact precompAnalytic_eq_of_comp_eq (f := pfn) (h := pfn) hg hmapsg
        (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U)
        (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U) rfl rfl hpfix
    · exact polyToAnalytic_X_compTendsto_scale_of_pointwise hmapsg hxscale
    · exact coverSectionPhiAnalytic_compTendsto_fix_of_pfn_fixed
        (c := c₂) (hpan := hpan) (hpmaps := hpmaps₂) hmapsg hpfix
  · intro d
    obtain ⟨ζ₀, g, g', hg, hg', hmapsg, hmapsg', hgg', hg'g, hord, hpfix, hscale⟩ := hdeckG d
    refine ⟨ζ₀, g, g', hg, hg', hmapsg, hmapsg', hgg', hg'g, hord, ?_, ?_⟩
    · exact precompAnalytic_eq_of_comp_eq (f := pfn) (h := pfn) hg hmapsg
        (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U)
        (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U) rfl rfl hpfix
    · exact coverSectionPhiAnalytic_compTendsto_scale_of_pointwise
        (c := c₂) (ζ := ζ₀) (hpan := hpan) (hpmaps := hpmaps₂) hmapsg hscale

end Bottcher

namespace Bottcher

open Set Filter Topology

/-- If the image of `x` under a `K`-algebra hom is transcendental, then `x` is transcendental.
A polynomial relation upstairs would map to the same polynomial relation downstairs. -/
theorem transcendental_of_algHom_image {K M N : Type*} [CommRing K] [Ring M] [Ring N]
    [Algebra K M] [Algebra K N] (φ : M →ₐ[K] N) {x : M}
    (hx : Transcendental K (φ x)) : Transcendental K x := by
  intro halg
  obtain ⟨p, hp0, hp⟩ := halg
  exact hx ⟨p, hp0, by rw [Polynomial.aeval_algHom_apply, hp, map_zero]⟩

/-- **Mixed cover-section descent.**  A single projection-base deck tower scaling the cover identity
coordinate, together with downstream transcendence of the transported second Böttcher coordinate,
already gives `NoRelation (φ_{c₁}, φ_{c₂})`.  The cover-side transcendence input required by
`noRelation_of_mixed_projection_base_lifts` is pulled back from the downstairs `phiMero c₂` statement
through the `ℂ(z)`-algebra cover-descent map. -/
theorem noRelation_phiMero_of_coverSection_mixed_lifts_sectionPhi_of_transcendental
    {c₁ c₂ : ℂ} (k : ℕ) {U V : Set ℂ}
    (hι : AnalyticOnNhd ℂ (fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) V)
    (hmaps : Set.MapsTo (fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) V U)
    (hUc : IsPreconnected U)
    (hopen : IsOpen ((fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) '' V))
    (himgne : ((fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) '' V).Nonempty)
    (hUo : IsOpen U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    (pfn : ℂ → ℂ) (hpan : AnalyticOnNhd ℂ pfn U)
    (hsec : ∀ z ∈ V, pfn (bottcherCoord c₁ ((quadratic c₁)^[k] z)) = z)
    (hinf : (pfn '' U).Infinite)
    (hpmaps₂ : Set.MapsTo pfn U (escapeOpen c₂))
    (hV₁ : V ⊆ escapeOpen c₁) (hV₂ : V ⊆ escapeOpen c₂)
    (hGdown : haveI := isDomain_analyticSubring V hVo hVc hVne
      haveI := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
      Transcendental (RatFunc ℂ) (phiMero c₂ hV₂))
    (hliftF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (_hg' : AnalyticOnNhd ℂ g' U)
        (hmapsg : Set.MapsTo g U U) (_hmapsg' : Set.MapsTo g' U U)
        (_hgg' : Set.EqOn (g ∘ g') id U) (_hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        precompAnalytic hg hmapsg (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U)
          = (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U) ∧
        ((polyToAnalytic U Polynomial.X : analyticSubring U) : Germ (𝓟 U) ℂ).compTendsto g
            (tendsto_principal_principal.mpr hmapsg)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ)
              * ((polyToAnalytic U Polynomial.X : analyticSubring U) : Germ (𝓟 U) ℂ) ∧
        (coverSectionPhiAnalytic c₂ pfn hpan hpmaps₂ : Germ (𝓟 U) ℂ).compTendsto g
            (tendsto_principal_principal.mpr hmapsg)
          = (coverSectionPhiAnalytic c₂ pfn hpan hpmaps₂ : Germ (𝓟 U) ℂ)) :
    haveI := isDomain_analyticSubring V hVo hVc hVne
    haveI := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hV₁) (phiMero c₂ hV₂) := by
  letI := isDomain_analyticSubring U hUo hUc hUne
  letI := isDomain_analyticSubring V hVo hVc hVne
  set p₀ : analyticSubring U := ⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ with hp0def
  have hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑pfn := rfl
  have hp0ι := coverSheet_hp0ι hmaps p₀ hp0 hsec
  letI algU : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMeroVia p₀ hp0 hinf hUo hUc hUne).toAlgebra
  letI algV : Algebra (RatFunc ℂ) (meroField V) := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
  let a₁ : analyticSubring U := polyToAnalytic U Polynomial.X
  let a₂ : analyticSubring U := coverSectionPhiAnalytic c₂ pfn hpan hpmaps₂
  let ψ : meroField U →ₐ[RatFunc ℂ] meroField V :=
    { precompMeroMap hι hmaps hUc hopen himgne hUo hUne hVo hVc hVne with
      commutes' := fun q => precompMeroMap_ratfuncToMeroVia hι hmaps hUc hopen himgne
        hUo hUne hVo hVc hVne hVinf hp0 hinf hp0ι q }
  have hψa₂ : ψ (algebraMap (analyticSubring U) (meroField U) a₂) = phiMero c₂ hV₂ := by
    change precompMeroMap hι hmaps hUc hopen himgne hUo hUne hVo hVc hVne
        (algebraMap (analyticSubring U) (meroField U) a₂) = phiMero c₂ hV₂
    rw [precompMeroMap_algebraMap, precompAnalyticMap_coverSectionPhiAnalytic k hι hmaps pfn hpan hsec hpmaps₂ hV₂]
    rfl
  have hGup : Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂) := by
    exact transcendental_of_algHom_image ψ (by simpa [hψa₂] using hGdown)
  have hcover : NoRelation (RatFunc ℂ)
      (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
    exact noRelation_of_mixed_projection_base_lifts hUo hUc hUne hp0 hinf a₁ a₂
      (polyToMero_X_ne_zero_of_infinite hUo hUc hUne (Set.Infinite.of_image pfn hinf))
      hGup
      (by simpa [a₁, a₂, hp0def] using hliftF)
  have hdesc : NoRelation (RatFunc ℂ)
      (precompMeroMap hι hmaps hUc hopen himgne hUo hUne hVo hVc hVne
        (algebraMap (analyticSubring U) (meroField U) a₁))
      (precompMeroMap hι hmaps hUc hopen himgne hUo hUne hVo hVc hVne
        (algebraMap (analyticSubring U) (meroField U) a₂)) :=
    noRelation_of_precompMap hι hmaps hUc hopen himgne hUo hUne hVo hVc hVne hVinf
      hp0 hinf hp0ι
      (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) hcover
  have hpow : NoRelation (RatFunc ℂ) ((phiMero c₁ hV₁) ^ (2 ^ k)) (phiMero c₂ hV₂) := by
    simpa [a₁, a₂, precompMeroMap_algebraMap,
      precompAnalyticMap_polyToAnalytic_X_bottcherCoord_iterate k hι hmaps hV₁,
      precompAnalyticMap_coverSectionPhiAnalytic k hι hmaps pfn hpan hsec hpmaps₂ hV₂,
      phiMero, map_pow] using hdesc
  exact U0MStepKummer.noRelation_pow_descent (phiMero c₁ hV₁) (phiMero c₂ hV₂) (2 ^ k) hpow

/-- **Pointwise mixed cover-section descent.**  This is the geometric-input version of the mixed
cover-section close: the deck tower is supplied by pointwise identities (`pfn` fixed, identity
coordinate scaled, transported second coordinate fixed), while transcendence of `φ_{c₂}` is supplied on
the downstairs domain. -/
theorem noRelation_phiMero_of_coverSection_pointwise_deck_sectionPhi_of_transcendental
    {c₁ c₂ : ℂ} (k : ℕ) {U V : Set ℂ}
    (hι : AnalyticOnNhd ℂ (fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) V)
    (hmaps : Set.MapsTo (fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) V U)
    (hUc : IsPreconnected U)
    (hopen : IsOpen ((fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) '' V))
    (himgne : ((fun z => bottcherCoord c₁ ((quadratic c₁)^[k] z)) '' V).Nonempty)
    (hUo : IsOpen U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    (pfn : ℂ → ℂ) (hpan : AnalyticOnNhd ℂ pfn U)
    (hsec : ∀ z ∈ V, pfn (bottcherCoord c₁ ((quadratic c₁)^[k] z)) = z)
    (hinf : (pfn '' U).Infinite)
    (hpmaps₂ : Set.MapsTo pfn U (escapeOpen c₂))
    (hV₁ : V ⊆ escapeOpen c₁) (hV₂ : V ⊆ escapeOpen c₂)
    (hGdown : haveI := isDomain_analyticSubring V hVo hVc hVne
      haveI := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
      Transcendental (RatFunc ℂ) (phiMero c₂ hV₂))
    (hdeckF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (_hg : AnalyticOnNhd ℂ g U) (_hg' : AnalyticOnNhd ℂ g' U)
        (_hmapsg : Set.MapsTo g U U) (_hmapsg' : Set.MapsTo g' U U)
        (_hgg' : Set.EqOn (g ∘ g') id U) (_hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        (∀ z ∈ U, pfn (g z) = pfn z) ∧
        (∀ z ∈ U, g z = ζ₀ * z)) :
    haveI := isDomain_analyticSubring V hVo hVc hVne
    haveI := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hV₁) (phiMero c₂ hV₂) := by
  refine noRelation_phiMero_of_coverSection_mixed_lifts_sectionPhi_of_transcendental
    k hι hmaps hUc hopen himgne hUo hUne hVo hVc hVne hVinf pfn hpan hsec hinf hpmaps₂
    hV₁ hV₂ hGdown ?_
  intro d
  obtain ⟨ζ₀, g, g', hg, hg', hmapsg, hmapsg', hgg', hg'g, hord, hpfix, hxscale⟩ := hdeckF d
  refine ⟨ζ₀, g, g', hg, hg', hmapsg, hmapsg', hgg', hg'g, hord, ?_, ?_, ?_⟩
  · exact precompAnalytic_eq_of_comp_eq (f := pfn) (h := pfn) hg hmapsg
      (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U)
      (⟨↑pfn, ⟨pfn, hpan, rfl⟩⟩ : analyticSubring U) rfl rfl hpfix
  · exact polyToAnalytic_X_compTendsto_scale_of_pointwise hmapsg hxscale
  · exact coverSectionPhiAnalytic_compTendsto_fix_of_pfn_fixed
      (c := c₂) (hpan := hpan) (hpmaps := hpmaps₂) hmapsg hpfix

end Bottcher

namespace Bottcher

open Set Filter Topology

/-- **Swapped pointwise mixed cover-section descent.**  Same mixed cover-section close as
`noRelation_phiMero_of_coverSection_pointwise_deck_sectionPhi_of_transcendental`, but the cover sheet is
built from the second parameter.  The result is flipped back with `noRelation_symm`, so the conclusion
has the standard `(c₁,c₂)` order. -/
theorem noRelation_phiMero_of_coverSection_pointwise_deck_sectionPhi_of_transcendental_swapped
    {c₁ c₂ : ℂ} (k : ℕ) {U V : Set ℂ}
    (hι : AnalyticOnNhd ℂ (fun z => bottcherCoord c₂ ((quadratic c₂)^[k] z)) V)
    (hmaps : Set.MapsTo (fun z => bottcherCoord c₂ ((quadratic c₂)^[k] z)) V U)
    (hUc : IsPreconnected U)
    (hopen : IsOpen ((fun z => bottcherCoord c₂ ((quadratic c₂)^[k] z)) '' V))
    (himgne : ((fun z => bottcherCoord c₂ ((quadratic c₂)^[k] z)) '' V).Nonempty)
    (hUo : IsOpen U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    (pfn : ℂ → ℂ) (hpan : AnalyticOnNhd ℂ pfn U)
    (hsec : ∀ z ∈ V, pfn (bottcherCoord c₂ ((quadratic c₂)^[k] z)) = z)
    (hinf : (pfn '' U).Infinite)
    (hpmaps₁ : Set.MapsTo pfn U (escapeOpen c₁))
    (hV₁ : V ⊆ escapeOpen c₁) (hV₂ : V ⊆ escapeOpen c₂)
    (hGdown : haveI := isDomain_analyticSubring V hVo hVc hVne
      haveI := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
      Transcendental (RatFunc ℂ) (phiMero c₁ hV₁))
    (hdeckG : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (_hg : AnalyticOnNhd ℂ g U) (_hg' : AnalyticOnNhd ℂ g' U)
        (_hmapsg : Set.MapsTo g U U) (_hmapsg' : Set.MapsTo g' U U)
        (_hgg' : Set.EqOn (g ∘ g') id U) (_hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        (∀ z ∈ U, pfn (g z) = pfn z) ∧
        (∀ z ∈ U, g z = ζ₀ * z)) :
    haveI := isDomain_analyticSubring V hVo hVc hVne
    haveI := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hV₁) (phiMero c₂ hV₂) := by
  letI := isDomain_analyticSubring V hVo hVc hVne
  letI := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
  exact noRelation_symm
    (noRelation_phiMero_of_coverSection_pointwise_deck_sectionPhi_of_transcendental
      (c₁ := c₂) (c₂ := c₁) k hι hmaps hUc hopen himgne hUo hUne hVo hVc hVne hVinf
      pfn hpan hsec hinf hpmaps₁ hV₂ hV₁ hGdown hdeckG)

end Bottcher
