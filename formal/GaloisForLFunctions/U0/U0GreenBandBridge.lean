/-
# The Green-band tower consumer: the `GBExt` clause discharged by exterior geometry

`U0TowerBridge.u0_phi_independence_of_towerData` consumes a tower certificate whose hardest
conjunct is `GBExt` — an element of `analyticSubring Ext'` restricting to the `u₀`-germ on `U`.
By `U0SectionExterior.green_sublevel_exterior`, at large `‖b‖` any extension domain contained in
a Green sublevel band lies inside `u₀`'s domain `{|z| > 1}`, where the `GBExt` element is simply
the restriction of `u₀` itself.  This file banks the two consumer theorems:

* `u0_phi_independence_of_towerData_exterior` — the `GBExt` clause replaced by the geometric
  clause `∀ z ∈ Ext', 1 < ‖z‖`;
* `u0_phi_independence_of_towerData_greenBand` — the clause replaced by a Green-band bound
  `∀ z ∈ Ext', G_b(z) < t` with `exp(4t) + 4 ≤ (‖b‖−1)² − ‖b‖`, for `‖b‖ ≥ 4`.

The moment the q62 lane's `bottcher_towerDataG_far`-style certificate exposes either conjunct
(library-backlog ticket, Update 5), the all-parameters U0 card closes mechanically at large
`‖b‖` — no `u₀`-specific construction inside the tower at all.
-/
import GaloisForLFunctions.U0.U0TowerBridge
import GaloisForLFunctions.U0.U0SectionExterior

open Complex Set Filter Bottcher U0 U0NaturalBoundary U0MeroCarrier U0SectionExterior

namespace U0GreenBandBridge

/-- Restricting the `u₀`-germ from a larger exterior domain to a smaller one is the `u₀`-germ. -/
theorem restrictAnalytic_u0AnSub {V U' : Set ℂ} (hV_ext : V ⊆ Ext) (hU'_ext : U' ⊆ Ext)
    (hVU' : V ⊆ U') :
    restrictAnalytic hVU' (u0AnSub hU'_ext) = u0AnSub hV_ext := by
  apply Subtype.ext
  show ((u0 : ℂ → ℂ) : Germ (𝓟 U') ℂ).compTendsto id
    (tendsto_principal_principal.mpr (fun x hx => hVU' hx)) = ((u0 : ℂ → ℂ) : Germ (𝓟 V) ℂ)
  rw [Germ.coe_compTendsto]
  rfl

/-- **The exterior-clause tower consumer.**  The all-parameters U0 conclusion from a tower
certificate whose `u₀`-clause is replaced by the purely geometric `∀ z ∈ Ext', 1 < ‖z‖`:
on an exterior extension domain, `GBExt` is the restriction of `u₀` itself. -/
theorem u0_phi_independence_of_towerData_exterior {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ Ext) {b : ℂ} (hU_esc : U ⊆ escapeOpen b)
    (towerdata : ∀ d : ℕ, ∃ (Ext' : Set ℂ)
        (_hExto : IsOpen Ext') (_hExtc : IsConnected Ext') (_hExtinf : Ext'.Infinite)
        (hUExt : U ⊆ Ext') (F : ℂ → ℂ) (aExt : analyticSubring Ext') (k : ℕ),
        1 ≤ k ∧ d < 2 ^ k ∧
        AnalyticOnNhd ℂ F Ext' ∧ (∀ z ∈ Ext', F z ≠ 0) ∧
        (Filter.Germ.coeRingHom (Filter.principal Ext') F)
          = (aExt : Filter.Germ (Filter.principal Ext') ℂ) ∧
        restrictAnalytic hUExt aExt = (phiAnalytic b hU_esc) ^ (2 ^ k) ∧
        (∀ z ∈ Ext', 1 < ‖z‖) ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext') ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, γ θ ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi), logDeriv F (γ θ) * γ' θ)
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext)) := by
  refine U0TowerBridge.u0_phi_independence_of_towerData hUo hUc hUne hUinf hU_ext hU_esc ?_
  intro d
  obtain ⟨Ext', hExto, hExtc, hExtinf, hUExt, F, aExt, k, hk1, hdk, hFan, hFne, hae, hrad,
    hout, hloops⟩ := towerdata d
  have hExtSub : Ext' ⊆ Ext := fun z hz => hout z hz
  exact ⟨Ext', hExto, hExtc, hExtinf, hUExt, F, aExt, u0AnSub hExtSub, k, hk1, hdk, hFan, hFne,
    hae, hrad, restrictAnalytic_u0AnSub hU_ext hExtSub hUExt, hloops⟩

/-- **The Green-band tower consumer.**  For `‖b‖ ≥ 4`, the all-parameters U0 conclusion from a
tower certificate whose `u₀`-clause is replaced by a Green sublevel bound on the extension
domain: `green_sublevel_exterior` pushes the band outside the unit disk, where `u₀` restricts. -/
theorem u0_phi_independence_of_towerData_greenBand {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ Ext) {b : ℂ} (hb : 4 ≤ ‖b‖) (hU_esc : U ⊆ escapeOpen b)
    (towerdata : ∀ d : ℕ, ∃ (Ext' : Set ℂ)
        (_hExto : IsOpen Ext') (_hExtc : IsConnected Ext') (_hExtinf : Ext'.Infinite)
        (hUExt : U ⊆ Ext') (F : ℂ → ℂ) (aExt : analyticSubring Ext') (k : ℕ),
        1 ≤ k ∧ d < 2 ^ k ∧
        AnalyticOnNhd ℂ F Ext' ∧ (∀ z ∈ Ext', F z ≠ 0) ∧
        (Filter.Germ.coeRingHom (Filter.principal Ext') F)
          = (aExt : Filter.Germ (Filter.principal Ext') ℂ) ∧
        restrictAnalytic hUExt aExt = (phiAnalytic b hU_esc) ^ (2 ^ k) ∧
        (∃ t : ℝ, Real.exp (4 * t) + 4 ≤ (‖b‖ - 1) ^ 2 - ‖b‖ ∧
          ∀ z ∈ Ext', greenFunctionDyn b z < t) ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext') ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, γ θ ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi), logDeriv F (γ θ) * γ' θ)
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext)) := by
  refine u0_phi_independence_of_towerData_exterior hUo hUc hUne hUinf hU_ext hU_esc ?_
  intro d
  obtain ⟨Ext', hExto, hExtc, hExtinf, hUExt, F, aExt, k, hk1, hdk, hFan, hFne, hae, hrad,
    ⟨t, hband, hGlt⟩, hloops⟩ := towerdata d
  refine ⟨Ext', hExto, hExtc, hExtinf, hUExt, F, aExt, k, hk1, hdk, hFan, hFne, hae, hrad,
    ?_, hloops⟩
  intro z hz
  exact green_sublevel_exterior hb hband (hGlt z hz)

end U0GreenBandBridge
