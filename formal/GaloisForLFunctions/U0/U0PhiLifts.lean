/-
# u₀ ⟂ φ_b reduced to the *shared* analytic lift data

The named goal (`u0_phi_independence`) and the Böttcher disconnected case
(`Bottcher.q62_independence_disconnected_of_lifts`) bottom out at the **same** object: the genuine
analytic dyadic-monodromy lift of `φ_b` on the basin — an analytic self-map `g` of `U` (with analytic
inverse `g'`) scaling the germ of `φ_b` by a root of unity of unbounded order while fixing `ℂ(z)`. The
u₀-specific inputs are already discharged, axiom-clean:

* `hF` (φ_b ≠ 0) — `Bottcher.phiMero_ne_zero`;
* `hG` (u₀ transcendental over ℂ(z) at the genuine carrier) — `U0MeroCarrier.u0Mero_transcendental`;
* the engine — `Bottcher.q62_mixed`, applied through `Bottcher.noRelation_of_mixed_lifts`.

For the mixed case the lift need only **fix** `u₀` (single-valued), which the *same* `g` does
automatically (`u₀` is a function of the base coordinate `z`, fixed by every deck transformation): the
lift datum `hliftF` that scales `φ_b` already contains the `fixes a₂` clause this file feeds as `u₀`.

So this theorem reduces the genuine independence `NoRelation ℂ(z) φ_b u₀` to **exactly** the lift datum
`hliftF` of the Böttcher disconnected case — making the shared crux machine-checked: construct that one
analytic monodromy and *both* the Böttcher independence and the u₀ independence close at once. This is
the u₀ analogue of `Bottcher.q62_independence_disconnected_of_lifts`, on the faithful carrier
`Bottcher.meroField U` where `NoRelation` is the real independence.
-/
import GaloisForLFunctions.U0.U0MeroCarrier
import GaloisForLFunctions.Bottcher.Q62Assembly

open Polynomial Filter Topology U0 U0NaturalBoundary U0Transcendence U0MeroCarrier Bottcher

namespace U0PhiLifts

variable {U : Set ℂ}

/-- **u₀ ⟂ φ_b, reduced to the Böttcher disconnected-case lift datum (PROVEN).** For a connected open
infinite `U ⊆ Ext ∩ escapeOpen b`, the genuine Böttcher coordinate `φ_b` and the c-velocity `u₀` — both
as the *actual analytic functions* inside the faithful carrier `meroField U` — satisfy no nonzero
polynomial relation over `ℂ(z)`, **given** the single analytic input `hliftF`: a dyadic-monodromy lift
of `φ_b` (an analytic self-map `g` of `U` with analytic inverse `g'`, scaling `φ_b`'s germ by a root of
unity `ζ₀` of unbounded order, fixing `u₀`'s germ and fixing `ℂ(z)`). This is precisely the `hliftF`
that `Bottcher.q62_independence_disconnected_of_lifts` consumes — the one shared open crux. The
u₀-side inputs (`φ_b ≠ 0`, `u₀` transcendence) are discharged here; only the monodromy remains. -/
theorem u0_phib_independence_of_lifts (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ Ext)
    {b : ℂ} (hU_esc : U ⊆ escapeOpen b)
    (hliftF : letI := isDomain_analyticSubring U hUo hUc hUne
      letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
        (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
        (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        ((phiAnalytic b hU_esc : analyticSubring U) : Germ (𝓟 U) ℂ).compTendsto g
            (tendsto_principal_principal.mpr hmaps)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ)
            * ((phiAnalytic b hU_esc : analyticSubring U) : Germ (𝓟 U) ℂ) ∧
        ((u0AnSub hU_ext : analyticSubring U) : Germ (𝓟 U) ℂ).compTendsto g
            (tendsto_principal_principal.mpr hmaps)
          = ((u0AnSub hU_ext : analyticSubring U) : Germ (𝓟 U) ℂ) ∧
        ∀ k : RatFunc ℂ, precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
          (algebraMap (RatFunc ℂ) (meroField U) k) = algebraMap (RatFunc ℂ) (meroField U) k) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext)) := by
  letI := isDomain_analyticSubring U hUo hUc hUne
  letI algR : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact noRelation_of_mixed_lifts hUo hUc hUne (phiAnalytic b hU_esc) (u0AnSub hU_ext)
    (phiMero_ne_zero hUo hUc hUne hU_esc)
    (u0Mero_transcendental hUo hUc hUne hUinf hU_ext)
    hliftF

end U0PhiLifts
