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
