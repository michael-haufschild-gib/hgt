/-
# u₀ ⟂ φ_b — the mixed-case reduction at the genuine (cover / projection) carrier

**Carrier correction (important).** The dyadic monodromy lift `g` must *fix* `ℂ(z)` while *scaling*
`φ_b`. That is possible only when `ℂ(z) ↪ meroField U` is the **projection embedding of the cover** —
`U` the (uniformized) cover, `g` a deck map fixing the base projection and permuting the branch
coordinate `φ_b`. It is impossible for the identity-coordinate embedding `ratfuncToMero` of the base
`z`-plane: there `algebraMap z` is the identity germ, so "`g` fixes `ℂ(z)`" forces `g = id`, hence
`φ_b ∘ g = φ_b` and the scaling root `ζ₀ = 1` — making `hliftF` **unsatisfiable** (`orderOf ζ₀ > d`
fails). So the carrier here is the *abstract* `[Algebra (RatFunc ℂ) (meroField U)]` supplied by the
cover, exactly as in `Bottcher.q62_independence_disconnected_of_lifts` ("the projection embedding").

This file states the u₀ mixed case at that carrier: it reduces `NoRelation ℂ(z) φ_b u₀` to
`Bottcher.noRelation_of_mixed_lifts`'s inputs — `hF` (φ_b ≠ 0), `hG` (u₀ transcendental over `ℂ(z)` via
the projection), and `hliftF` (the deck lift scaling `φ_b`, fixing `u₀` and `ℂ(z)`). The `hliftF` is the
shared open crux with the Böttcher disconnected case — constructing that one deck lift closes both.

The remaining u₀-specific work is to discharge `hG` at this carrier by transporting
`U0Transcendence.u0Field_transcendental` (u₀ transcendental over `ℂ(z)`, axiom-clean) along the base
projection — buildable once the cover + projection embedding is constructed (parallel Böttcher work).
The previous version of this file instantiated the *base-plane* `ratfuncToMero` carrier and so reduced
to a vacuously unsatisfiable `hliftF`; this corrects it to the genuine monodromy carrier.
-/
import GaloisForLFunctions.U0.U0MeroCarrier
import GaloisForLFunctions.U0.U0CoverTransport
import GaloisForLFunctions.Bottcher.Q62Assembly

open Polynomial Filter Topology Bottcher

namespace U0PhiLifts

variable {U : Set ℂ}

/-- **u₀ ⟂ φ_b at the genuine cover/projection carrier, reduced to the shared deck lift (PROVEN).**
With `[Algebra (RatFunc ℂ) (meroField U)]` the cover's projection embedding, `aφ`/`au0` the `φ_b`/`u₀`
germs, this reduces `NoRelation ℂ(z) φ_b u₀` to exactly `Bottcher.noRelation_of_mixed_lifts`'s inputs:
`hF` (`φ_b ≠ 0`), `hG` (`u₀` transcendental over `ℂ(z)`), and `hliftF` (the deck self-map scaling `φ_b`
by a root of unbounded order, fixing `u₀` and `ℂ(z)`). The `hliftF` is the shared crux with the Böttcher
disconnected case. (Carrier note in the file header: the base-plane `ratfuncToMero` carrier makes
`hliftF` unsatisfiable; the projection carrier is the genuine one.) -/
@[aesop safe]
theorem u0_phib_independence_of_lifts (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    [Algebra (RatFunc ℂ) (meroField U)] (aφ au0 : analyticSubring U)
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) aφ ≠ 0)
    (hG : haveI := isDomain_analyticSubring U hUo hUc hUne
          Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) au0))
    (hliftF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
        (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
        (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        (aφ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (aφ : Germ (𝓟 U) ℂ) ∧
        (au0 : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
          = (au0 : Germ (𝓟 U) ℂ) ∧
        ∀ k : RatFunc ℂ, precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
          (algebraMap (RatFunc ℂ) (meroField U) k) = algebraMap (RatFunc ℂ) (meroField U) k) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) aφ)
      (algebraMap (analyticSubring U) (meroField U) au0) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  exact noRelation_of_mixed_lifts hUo hUc hUne aφ au0 hF hG hliftF

/-- **u₀ ⟂ φ_b — the FULL descent capstone (genuine carrier → deep ball, reduced to the cover + lift).**
The genuine independence `NoRelation ℂ(z) φ_b u₀` *descended to the deep ball `V`*, obtained by composing
two committed steps: (i) the cover-side mixed independence over `ℂ(p₀)` (`noRelation_of_mixed_lifts`,
inputs `hF`: φ_b≠0, `hG`: u₀ transcendental over `ℂ(p₀)`, `hliftF`: the dyadic deck lift on the cover
`U`); (ii) the descent along the pullback `ι` with `p₀∘ι = z` (`Bottcher.noRelation_of_precompMap`),
carrying `φ_b ↦ precompMeroMap φ_b = φ_b|_V`, `u₀ ↦ u₀|_V`. This is the u₀ analogue of
`Bottcher.noRelation_of_precompMap` (the disconnected-case capstone): every algebraic step is built and
axiom-clean; the lone remaining input is the analytic lift — the genuine cover `U`, its `φ_b` germ, deck
`g`, and pullback `ι` (parallel Böttcher work). The `hG` transcendence is itself supplied by
`U0CoverTransport.transcendental_precompMeroCross`. -/
theorem u0_phib_noRelation_descended {V : Set ℂ} {ι : ℂ → ℂ}
    (hι : AnalyticOnNhd ℂ ι V) (hmaps : Set.MapsTo ι V U) (hUc : IsPreconnected U)
    (hopen : IsOpen (ι '' V)) (hne : (ι '' V).Nonempty)
    (hUo : IsOpen U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    {p₀ : analyticSubring U} {f₀ : ℂ → ℂ} (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑f₀)
    (hinf : (f₀ '' U).Infinite)
    (hp0ι : (p₀ : Germ (𝓟 U) ℂ).compTendsto ι (tendsto_principal_principal.mpr hmaps)
        = (↑(fun w : ℂ => w) : Germ (𝓟 V) ℂ))
    (aφ au0 : analyticSubring U)
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) aφ ≠ 0)
    (hG : haveI := isDomain_analyticSubring U hUo hUc hUne
          letI := (ratfuncToMeroVia p₀ hp0 hinf hUo hUc hUne).toAlgebra
          Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) au0))
    (hliftF : haveI := isDomain_analyticSubring U hUo hUc hUne
        letI := (ratfuncToMeroVia p₀ hp0 hinf hUo hUc hUne).toAlgebra
        ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
          (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
          (hmg : Set.MapsTo g U U) (hmg' : Set.MapsTo g' U U)
          (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U),
          d < orderOf ζ₀ ∧
          (aφ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmg)
            = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (aφ : Germ (𝓟 U) ℂ) ∧
          (au0 : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmg)
            = (au0 : Germ (𝓟 U) ℂ) ∧
          ∀ k : RatFunc ℂ, precompMeroEquiv hg hg' hmg hmg' hgg' hg'g hUo hUc hUne
            (algebraMap (RatFunc ℂ) (meroField U) k) = algebraMap (RatFunc ℂ) (meroField U) k) :
    haveI := isDomain_analyticSubring V hVo hVc hVne
    letI := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
    NoRelation (RatFunc ℂ)
      (precompMeroMap hι hmaps hUc hopen hne hUo hUne hVo hVc hVne
        (algebraMap (analyticSubring U) (meroField U) aφ))
      (precompMeroMap hι hmaps hUc hopen hne hUo hUne hVo hVc hVne
        (algebraMap (analyticSubring U) (meroField U) au0)) := by
  apply noRelation_of_precompMap hι hmaps hUc hopen hne hUo hUne hVo hVc hVne hVinf hp0 hinf hp0ι
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMeroVia p₀ hp0 hinf hUo hUc hUne).toAlgebra
  exact noRelation_of_mixed_lifts hUo hUc hUne aφ au0 hF hG hliftF

end U0PhiLifts

namespace U0PhiLifts

/-- U0-phi cover lift close with the `u₀` transcendence input supplied by projection transport from the
base carrier. Compared with `u0_phib_independence_of_lifts`, this no longer asks for a separate `hG`:
it is built from `U0MeroCarrier.u0Mero_transcendental` and `U0CoverTransport.precompMeroCross`. -/
theorem u0_phib_independence_of_precomp_lifts {U V : Set ℂ} {g : ℂ → ℂ}
    (hgbase : AnalyticOnNhd ℂ g U) (hbaseMaps : Set.MapsTo g U V)
    (hbase : Tendsto g (𝓟 U) (𝓟 V)) (hbaseSurj : Set.SurjOn g U V)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    (hV_ext : V ⊆ U0NaturalBoundary.Ext)
    [haveI := isDomain_analyticSubring U hUo hUc hUne; Algebra (RatFunc ℂ) (meroField U)]
    (hcompat : haveI := isDomain_analyticSubring U hUo hUc hUne
      haveI := isDomain_analyticSubring V hVo hVc hVne
      letI : Algebra (RatFunc ℂ) (meroField V) := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
      ∀ k : RatFunc ℂ, U0CoverTransport.precompMeroCross hgbase hbaseMaps hbase hbaseSurj
          hUo hUc hUne hVo hVc hVne
          (algebraMap (RatFunc ℂ) (meroField V) k) = algebraMap (RatFunc ℂ) (meroField U) k)
    (aφ : analyticSubring U)
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) aφ ≠ 0)
    (hliftF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (gdeck gdeck' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ gdeck U) (hg' : AnalyticOnNhd ℂ gdeck' U)
        (hmaps : Set.MapsTo gdeck U U) (hmaps' : Set.MapsTo gdeck' U U)
        (hgg' : Set.EqOn (gdeck ∘ gdeck') id U) (hg'g : Set.EqOn (gdeck' ∘ gdeck) id U),
        d < orderOf ζ₀ ∧
        (aφ : Germ (𝓟 U) ℂ).compTendsto gdeck (tendsto_principal_principal.mpr hmaps)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (aφ : Germ (𝓟 U) ℂ) ∧
        ((U0CoverTransport.precompAnalyticCross hgbase hbaseMaps hbase
            (U0MeroCarrier.u0AnSub hV_ext) : analyticSubring U) : Germ (𝓟 U) ℂ).compTendsto
          gdeck (tendsto_principal_principal.mpr hmaps)
          = (U0CoverTransport.precompAnalyticCross hgbase hbaseMaps hbase
              (U0MeroCarrier.u0AnSub hV_ext) : analyticSubring U) ∧
        ∀ k : RatFunc ℂ, precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
          (algebraMap (RatFunc ℂ) (meroField U) k) = algebraMap (RatFunc ℂ) (meroField U) k) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) aφ)
      (algebraMap (analyticSubring U) (meroField U)
        (U0CoverTransport.precompAnalyticCross hgbase hbaseMaps hbase
          (U0MeroCarrier.u0AnSub hV_ext))) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  haveI := isDomain_analyticSubring V hVo hVc hVne
  let au0 : analyticSubring U :=
    U0CoverTransport.precompAnalyticCross hgbase hbaseMaps hbase (U0MeroCarrier.u0AnSub hV_ext)
  have hGpre := U0CoverTransport.u0_transcendental_precompMeroCross hgbase hbaseMaps hbase
    hbaseSurj hUo hUc hUne hVo hVc hVne hVinf hV_ext hcompat
  have hG : Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) au0) := by
    rw [← U0CoverTransport.precompMeroCross_algebraMap hgbase hbaseMaps hbase hbaseSurj
      hUo hUc hUne hVo hVc hVne (U0MeroCarrier.u0AnSub hV_ext)]
    exact hGpre
  exact u0_phib_independence_of_lifts hUo hUc hUne aφ au0 hF hG hliftF

end U0PhiLifts

namespace U0PhiLifts

/-- U0-phi full descent capstone with cover-side `u₀` transcendence supplied by projection transport.
Compared with `u0_phib_noRelation_descended`, this removes the separate `hG` hypothesis by building it
from the base `u₀` carrier theorem and the cover projection. -/
theorem u0_phib_noRelation_descended_precomp {U B V : Set ℂ} {π ι : ℂ → ℂ}
    (hπ : AnalyticOnNhd ℂ π U) (hπmaps : Set.MapsTo π U B)
    (hπtend : Tendsto π (𝓟 U) (𝓟 B)) (hπsurj : Set.SurjOn π U B)
    (hι : AnalyticOnNhd ℂ ι V) (hmaps : Set.MapsTo ι V U) (hUc : IsPreconnected U)
    (hopen : IsOpen (ι '' V)) (hne : (ι '' V).Nonempty)
    (hUo : IsOpen U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    (hBo : IsOpen B) (hBc : IsPreconnected B) (hBne : B.Nonempty) (hBinf : B.Infinite)
    (hB_ext : B ⊆ U0NaturalBoundary.Ext)
    {p₀ : analyticSubring U} {f₀ : ℂ → ℂ} (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑f₀)
    (hinf : (f₀ '' U).Infinite)
    (hp0ι : (p₀ : Germ (𝓟 U) ℂ).compTendsto ι (tendsto_principal_principal.mpr hmaps)
        = (↑(fun w : ℂ => w) : Germ (𝓟 V) ℂ))
    (aφ : analyticSubring U)
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) aφ ≠ 0)
    (hcompat : haveI := isDomain_analyticSubring U hUo hUc hUne
      haveI := isDomain_analyticSubring B hBo hBc hBne
      letI := (ratfuncToMeroVia p₀ hp0 hinf hUo hUc hUne).toAlgebra
      letI : Algebra (RatFunc ℂ) (meroField B) := (ratfuncToMero B hBo hBc hBne hBinf).toAlgebra
      ∀ k : RatFunc ℂ, U0CoverTransport.precompMeroCross hπ hπmaps hπtend hπsurj hUo hUc hUne hBo hBc hBne
          (algebraMap (RatFunc ℂ) (meroField B) k) = algebraMap (RatFunc ℂ) (meroField U) k)
    (hliftF : haveI := isDomain_analyticSubring U hUo hUc hUne
        letI := (ratfuncToMeroVia p₀ hp0 hinf hUo hUc hUne).toAlgebra
        ∀ d : ℕ, ∃ (ζ₀ : ℂ) (gdeck gdeck' : ℂ → ℂ)
          (hg : AnalyticOnNhd ℂ gdeck U) (hg' : AnalyticOnNhd ℂ gdeck' U)
          (hmg : Set.MapsTo gdeck U U) (hmg' : Set.MapsTo gdeck' U U)
          (hgg' : Set.EqOn (gdeck ∘ gdeck') id U) (hg'g : Set.EqOn (gdeck' ∘ gdeck) id U),
          d < orderOf ζ₀ ∧
          (aφ : Germ (𝓟 U) ℂ).compTendsto gdeck (tendsto_principal_principal.mpr hmg)
            = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (aφ : Germ (𝓟 U) ℂ) ∧
          ((U0CoverTransport.precompAnalyticCross hπ hπmaps hπtend
              (U0MeroCarrier.u0AnSub hB_ext) : analyticSubring U) : Germ (𝓟 U) ℂ).compTendsto
            gdeck (tendsto_principal_principal.mpr hmg)
            = (U0CoverTransport.precompAnalyticCross hπ hπmaps hπtend
                (U0MeroCarrier.u0AnSub hB_ext) : analyticSubring U) ∧
          ∀ k : RatFunc ℂ, precompMeroEquiv hg hg' hmg hmg' hgg' hg'g hUo hUc hUne
            (algebraMap (RatFunc ℂ) (meroField U) k) = algebraMap (RatFunc ℂ) (meroField U) k) :
    haveI := isDomain_analyticSubring V hVo hVc hVne
    letI := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
    NoRelation (RatFunc ℂ)
      (precompMeroMap hι hmaps hUc hopen hne hUo hUne hVo hVc hVne
        (algebraMap (analyticSubring U) (meroField U) aφ))
      (precompMeroMap hι hmaps hUc hopen hne hUo hUne hVo hVc hVne
        (algebraMap (analyticSubring U) (meroField U)
          (U0CoverTransport.precompAnalyticCross hπ hπmaps hπtend
            (U0MeroCarrier.u0AnSub hB_ext)))) := by
  apply noRelation_of_precompMap hι hmaps hUc hopen hne hUo hUne hVo hVc hVne hVinf hp0 hinf hp0ι
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMeroVia p₀ hp0 hinf hUo hUc hUne).toAlgebra
  exact u0_phib_independence_of_precomp_lifts hπ hπmaps hπtend hπsurj hUo hUc hUne hBo hBc hBne hBinf
    hB_ext hcompat aφ hF hliftF

end U0PhiLifts

namespace U0PhiLifts

/-- U0-phi full descent capstone with the deck's `RatFunc ℂ`-linearity derived from the projection
base. Compared with `u0_phib_noRelation_descended_precomp`, the lift input no longer has to state that
all base rational functions are fixed by the deck; it only states that the deck fixes the projection
analytic germ `p₀`. -/
theorem u0_phib_noRelation_descended_precomp_projection_lifts {U B V : Set ℂ} {π ι : ℂ → ℂ}
    (hπ : AnalyticOnNhd ℂ π U) (hπmaps : Set.MapsTo π U B)
    (hπtend : Tendsto π (𝓟 U) (𝓟 B)) (hπsurj : Set.SurjOn π U B)
    (hι : AnalyticOnNhd ℂ ι V) (hmaps : Set.MapsTo ι V U) (hUc : IsPreconnected U)
    (hopen : IsOpen (ι '' V)) (hne : (ι '' V).Nonempty)
    (hUo : IsOpen U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    (hBo : IsOpen B) (hBc : IsPreconnected B) (hBne : B.Nonempty) (hBinf : B.Infinite)
    (hB_ext : B ⊆ U0NaturalBoundary.Ext)
    {p₀ : analyticSubring U} {f₀ : ℂ → ℂ} (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑f₀)
    (hinf : (f₀ '' U).Infinite)
    (hp0ι : (p₀ : Germ (𝓟 U) ℂ).compTendsto ι (tendsto_principal_principal.mpr hmaps)
        = (↑(fun w : ℂ => w) : Germ (𝓟 V) ℂ))
    (aφ : analyticSubring U)
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) aφ ≠ 0)
    (hcompat : haveI := isDomain_analyticSubring U hUo hUc hUne
      haveI := isDomain_analyticSubring B hBo hBc hBne
      letI := (ratfuncToMeroVia p₀ hp0 hinf hUo hUc hUne).toAlgebra
      letI : Algebra (RatFunc ℂ) (meroField B) := (ratfuncToMero B hBo hBc hBne hBinf).toAlgebra
      ∀ k : RatFunc ℂ, U0CoverTransport.precompMeroCross hπ hπmaps hπtend hπsurj hUo hUc hUne hBo hBc hBne
          (algebraMap (RatFunc ℂ) (meroField B) k) = algebraMap (RatFunc ℂ) (meroField U) k)
    (hliftF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (gdeck gdeck' : ℂ → ℂ)
          (hg : AnalyticOnNhd ℂ gdeck U) (_hg' : AnalyticOnNhd ℂ gdeck' U)
          (hmg : Set.MapsTo gdeck U U) (_hmg' : Set.MapsTo gdeck' U U)
          (_hgg' : Set.EqOn (gdeck ∘ gdeck') id U) (_hg'g : Set.EqOn (gdeck' ∘ gdeck) id U),
          d < orderOf ζ₀ ∧
          (aφ : Germ (𝓟 U) ℂ).compTendsto gdeck (tendsto_principal_principal.mpr hmg)
            = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (aφ : Germ (𝓟 U) ℂ) ∧
          ((U0CoverTransport.precompAnalyticCross hπ hπmaps hπtend
              (U0MeroCarrier.u0AnSub hB_ext) : analyticSubring U) : Germ (𝓟 U) ℂ).compTendsto
            gdeck (tendsto_principal_principal.mpr hmg)
            = (U0CoverTransport.precompAnalyticCross hπ hπmaps hπtend
                (U0MeroCarrier.u0AnSub hB_ext) : analyticSubring U) ∧
          precompAnalytic hg hmg p₀ = p₀) :
    haveI := isDomain_analyticSubring V hVo hVc hVne
    letI := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
    NoRelation (RatFunc ℂ)
      (precompMeroMap hι hmaps hUc hopen hne hUo hUne hVo hVc hVne
        (algebraMap (analyticSubring U) (meroField U) aφ))
      (precompMeroMap hι hmaps hUc hopen hne hUo hUne hVo hVc hVne
        (algebraMap (analyticSubring U) (meroField U)
          (U0CoverTransport.precompAnalyticCross hπ hπmaps hπtend
            (U0MeroCarrier.u0AnSub hB_ext)))) := by
  apply u0_phib_noRelation_descended_precomp hπ hπmaps hπtend hπsurj hι hmaps hUc hopen hne
    hUo hUne hVo hVc hVne hVinf hBo hBc hBne hBinf hB_ext hp0 hinf hp0ι aφ hF hcompat
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMeroVia p₀ hp0 hinf hUo hUc hUne).toAlgebra
  intro d
  obtain ⟨ζ₀, gdeck, gdeck', hg, hg', hmg, hmg', hgg', hg'g, hord, hscale, hinv, hpfix⟩ := hliftF d
  refine ⟨ζ₀, gdeck, gdeck', hg, hg', hmg, hmg', hgg', hg'g, hord, hscale, hinv, ?_⟩
  intro k
  simpa using! precompMeroEquiv_ratfuncToMeroVia_fix hg hg' hmg hmg' hgg' hg'g
    hUo hUc hUne hp0 hinf hpfix k

end U0PhiLifts

namespace U0PhiLifts

/-- U0-phi full descent capstone with both base-compatibility facts derived from projection data. Compared
with `u0_phib_noRelation_descended_precomp_projection_lifts`, the cross-precomposition `RatFunc ℂ`
compatibility is no longer an input: it follows from the projection germ identity `p₀ = π`. -/
theorem u0_phib_noRelation_descended_precomp_projection_base_lifts {U B V : Set ℂ} {π ι : ℂ → ℂ}
    (hπ : AnalyticOnNhd ℂ π U) (hπmaps : Set.MapsTo π U B)
    (hπtend : Tendsto π (𝓟 U) (𝓟 B)) (hπsurj : Set.SurjOn π U B)
    (hι : AnalyticOnNhd ℂ ι V) (hmaps : Set.MapsTo ι V U) (hUc : IsPreconnected U)
    (hopen : IsOpen (ι '' V)) (hne : (ι '' V).Nonempty)
    (hUo : IsOpen U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    (hBo : IsOpen B) (hBc : IsPreconnected B) (hBne : B.Nonempty) (hBinf : B.Infinite)
    (hB_ext : B ⊆ U0NaturalBoundary.Ext)
    {p₀ : analyticSubring U} {f₀ : ℂ → ℂ} (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑f₀)
    (hinf : (f₀ '' U).Infinite) (hp0π : (p₀ : Germ (𝓟 U) ℂ) = ↑π)
    (hp0ι : (p₀ : Germ (𝓟 U) ℂ).compTendsto ι (tendsto_principal_principal.mpr hmaps)
        = (↑(fun w : ℂ => w) : Germ (𝓟 V) ℂ))
    (aφ : analyticSubring U)
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) aφ ≠ 0)
    (hliftF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (gdeck gdeck' : ℂ → ℂ)
          (hg : AnalyticOnNhd ℂ gdeck U) (_hg' : AnalyticOnNhd ℂ gdeck' U)
          (hmg : Set.MapsTo gdeck U U) (_hmg' : Set.MapsTo gdeck' U U)
          (_hgg' : Set.EqOn (gdeck ∘ gdeck') id U) (_hg'g : Set.EqOn (gdeck' ∘ gdeck) id U),
          d < orderOf ζ₀ ∧
          (aφ : Germ (𝓟 U) ℂ).compTendsto gdeck (tendsto_principal_principal.mpr hmg)
            = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (aφ : Germ (𝓟 U) ℂ) ∧
          ((U0CoverTransport.precompAnalyticCross hπ hπmaps hπtend
              (U0MeroCarrier.u0AnSub hB_ext) : analyticSubring U) : Germ (𝓟 U) ℂ).compTendsto
            gdeck (tendsto_principal_principal.mpr hmg)
            = (U0CoverTransport.precompAnalyticCross hπ hπmaps hπtend
                (U0MeroCarrier.u0AnSub hB_ext) : analyticSubring U) ∧
          precompAnalytic hg hmg p₀ = p₀) :
    haveI := isDomain_analyticSubring V hVo hVc hVne
    letI := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
    NoRelation (RatFunc ℂ)
      (precompMeroMap hι hmaps hUc hopen hne hUo hUne hVo hVc hVne
        (algebraMap (analyticSubring U) (meroField U) aφ))
      (precompMeroMap hι hmaps hUc hopen hne hUo hUne hVo hVc hVne
        (algebraMap (analyticSubring U) (meroField U)
          (U0CoverTransport.precompAnalyticCross hπ hπmaps hπtend
            (U0MeroCarrier.u0AnSub hB_ext)))) := by
  apply u0_phib_noRelation_descended_precomp_projection_lifts hπ hπmaps hπtend hπsurj hι hmaps hUc
    hopen hne hUo hUne hVo hVc hVne hVinf hBo hBc hBne hBinf hB_ext hp0 hinf hp0ι aφ hF
  · intro k
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := isDomain_analyticSubring B hBo hBc hBne
    letI := (ratfuncToMeroVia p₀ hp0 hinf hUo hUc hUne).toAlgebra
    letI : Algebra (RatFunc ℂ) (meroField B) := (ratfuncToMero B hBo hBc hBne hBinf).toAlgebra
    simpa using! U0CoverTransport.precompMeroCross_ratfuncToMeroVia hπ hπmaps hπtend hπsurj
      hUo hUc hUne hBo hBc hBne hBinf hp0 hinf hp0π k
  · exact hliftF

end U0PhiLifts
