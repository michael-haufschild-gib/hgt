import GaloisForLFunctions.Bottcher.Q62Assembly

/-!
# Disconnected lift data, reduced to pointwise conditions on the deck map

`Q62Assembly.noRelation_of_disconnected_lifts` proves the disconnected/disconnected `q62`
independence once the deck **lift data** `hliftF`/`hliftG` is supplied — but there the two
Böttcher clauses (`a₁` scales by `ζ₀`, `a₂` is fixed) are phrased as equalities of *germs*
(`Germ.compTendsto`).  A geometric construction of the deck self-map `g` does not naturally
produce germ equalities; it produces **pointwise** identities on the common domain `U`:
`φ₁(g w) = ζ₀·φ₁ w` and `φ₂(g w) = φ₂ w`.

This file bridges the two.  `noRelation_of_disconnected_pointwise_lifts` takes exactly the
pointwise clauses (against the underlying functions `φ₁ = ↑a₁`, `φ₂ = ↑a₂`) and discharges the
germ clauses of `noRelation_of_disconnected_lifts`.  So a downstream supplier of the small
separating-annulus deck near `x ∈ K₁ ∖ K₂` only has to verify pointwise scaling/fixing on `U`,
not manipulate germs.  Axiom-clean; the base-field clause `hK` is passed through unchanged.
-/

open Bottcher Set Filter Topology

namespace Bottcher

/-- **Pointwise → germ bridge, fixing clause.** If `g` maps `U` into `U` and fixes `φ` pointwise on
`U`, then the germ `↑φ` is fixed by `Germ.compTendsto _ g`. -/
theorem compTendsto_fix_of_eqOn {U : Set ℂ} {g : ℂ → ℂ} (φ : ℂ → ℂ)
    (hmaps : Set.MapsTo g U U) (hfix : ∀ w ∈ U, φ (g w) = φ w) :
    (↑φ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps) = ↑φ := by
  rw [Germ.coe_compTendsto]
  exact Germ.coe_eq.mpr (Filter.eventually_principal.mpr hfix)

/-- **Pointwise → germ bridge, scaling clause.** If `g` maps `U` into `U` and scales `φ` by `ζ`
pointwise on `U`, then `Germ.compTendsto _ g` scales the germ `↑φ` by the constant germ `↑(fun _ => ζ)`. -/
theorem compTendsto_scale_of_eqOn {U : Set ℂ} {g : ℂ → ℂ} (φ : ℂ → ℂ) (ζ : ℂ)
    (hmaps : Set.MapsTo g U U) (hsc : ∀ w ∈ U, φ (g w) = ζ * φ w) :
    (↑φ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
      = (↑(fun _ : ℂ => ζ) : Germ (𝓟 U) ℂ) * ↑φ := by
  rw [Germ.coe_compTendsto, ← Germ.coe_mul]
  exact Germ.coe_eq.mpr (Filter.eventually_principal.mpr (fun w hw => hsc w hw))

/-- **Disconnected independence from pointwise deck lift data.**  Same conclusion as
`noRelation_of_disconnected_lifts`, but the Böttcher clauses are the pointwise identities a genuine
separating-annulus deck produces: at every depth `d` a self-biholomorphism `g` of `U` (inverse `g'`,
both analytic) and a root `ζ₀` of order `> d` with `φ₁ ∘ g = ζ₀ · φ₁` and `φ₂ ∘ g = φ₂` on `U`
(symmetrically for `hliftG`), fixing the base field `K`.  Here `φ₁, φ₂` are the underlying functions
of the germs `a₁, a₂` (`ha₁ : (a₁ : Germ) = ↑φ₁`, etc.) — in the intended instance
`φ₁ = bottcherCoord c₁`, `φ₂ = bottcherCoord c₂`.  The remaining input is thus purely the *pointwise*
dynamics of the deck; all germ/field algebra is discharged here. -/
theorem noRelation_of_disconnected_pointwise_lifts {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {K : Type*} [Field K] [Algebra K (meroField U)]
    (a₁ a₂ : analyticSubring U) (φ₁ φ₂ : ℂ → ℂ)
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = ↑φ₁) (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = ↑φ₂)
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hG : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₂ ≠ 0)
    (hliftF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
        (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
        (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        (∀ w ∈ U, φ₁ (g w) = ζ₀ * φ₁ w) ∧
        (∀ w ∈ U, φ₂ (g w) = φ₂ w) ∧
        ∀ k : K, precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
          (algebraMap K (meroField U) k) = algebraMap K (meroField U) k)
    (hliftG : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
        (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
        (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        (∀ w ∈ U, φ₂ (g w) = ζ₀ * φ₂ w) ∧
        ∀ k : K, precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
          (algebraMap K (meroField U) k) = algebraMap K (meroField U) k) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    NoRelation K (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  refine noRelation_of_disconnected_lifts hUo hUc hUne a₁ a₂ hF hG ?_ ?_
  · intro d
    obtain ⟨ζ₀, g, g', hg, hg', hmaps, hmaps', hgg', hg'g, hord, hsc, hfx, hK⟩ := hliftF d
    refine ⟨ζ₀, g, g', hg, hg', hmaps, hmaps', hgg', hg'g, hord, ?_, ?_, hK⟩
    · have hconst : ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ)
          = (↑(fun _ : ℂ => ζ₀) : Germ (𝓟 U) ℂ) := rfl
      rw [ha₁, hconst]
      exact compTendsto_scale_of_eqOn φ₁ ζ₀ hmaps hsc
    · rw [ha₂]
      exact compTendsto_fix_of_eqOn φ₂ hmaps hfx
  · intro d
    obtain ⟨ζ₀, g, g', hg, hg', hmaps, hmaps', hgg', hg'g, hord, hsc, hK⟩ := hliftG d
    refine ⟨ζ₀, g, g', hg, hg', hmaps, hmaps', hgg', hg'g, hord, ?_, hK⟩
    · have hconst : ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ)
          = (↑(fun _ : ℂ => ζ₀) : Germ (𝓟 U) ℂ) := rfl
      rw [ha₂, hconst]
      exact compTendsto_scale_of_eqOn φ₂ ζ₀ hmaps hsc

end Bottcher
