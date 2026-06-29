/-
# Q62 from lifted odd image-winding curves

This file separates the remaining geometric input from the analytic/non-square
pipeline.  The base curve need not be a round circle: it is any closed image
curve whose logarithmic winding integral is odd, together with a closed lift in
the deep domain.
-/
import GaloisForLFunctions.Bottcher.Q62DeepDataAssembly

open Complex Set Filter Polynomial
open scoped BigOperators

namespace Bottcher

/-- Q62 disconnected/disconnected from lifted odd image-winding curves.  The geometric input is now:
for each depth and countable exceptional set, produce a closed lift `γ` in `Ext` of a base image curve
`β`, with chain-rule velocity `β'`, and prove the odd winding integral for `β`. -/
theorem q62_disconnected_of_liftedImageWindingDeepData_escape
    {c₁ c₂ : ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hUesc : ∀ z ∈ U, ‖c₁‖ ≤ ‖z‖ ∧ 2 < ‖z‖)
    (a₁ a₂ : analyticSubring U)
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₁) : Germ (𝓟 U) ℂ))
    (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₂) : Germ (𝓟 U) ℂ))
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hGtr : haveI := isDomain_analyticSubring U hUo hUc hUne
            haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
            Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂))
    (deepdata : ∀ d : ℕ, ∃ (Ext : Set ℂ),
      IsOpen Ext ∧ IsConnected Ext ∧ Ext.Infinite ∧ U ⊆ Ext ∧
      (∀ z ∈ Ext, (quadratic c₁)^[d+1] z ∈ escapeOpen c₁) ∧
      Ext ⊆ escapeOpen c₂ ∧
      (∀ T : Set ℂ, T.Countable →
        ∃ (γ γ' β β' : ℝ → ℂ) (m : ℤ),
          (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
          (∀ θ : ℝ, HasDerivAt γ (γ' θ) θ) ∧
          γ (2 * Real.pi) = γ 0 ∧
          (∀ θ : ℝ, (quadratic c₁)^[d+1] (γ θ) ∉ T) ∧
          (∀ θ : ℝ, (quadratic c₁)^[d+1] (γ θ) = β θ) ∧
          (∀ θ : ℝ,
            (∏ j ∈ Finset.range (d+1), 2 * (quadratic c₁)^[j] (γ θ)) * γ' θ = β' θ) ∧
          (∫ θ in (0:ℝ)..(2 * Real.pi), (β θ)⁻¹ * β' θ)
            = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  apply q62_disconnected_of_imageWindingDeepData_escape hUo hUc hUne hUinf
    hUesc a₁ a₂ ha₁ ha₂ hF hGtr
  intro d
  obtain ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂, hloops⟩ := deepdata d
  have hradan : AnalyticOnNhd ℂ
      (fun z => bottcherCoord c₁ ((quadratic c₁)^[d+1] z)) Ext := by
    intro z hz
    have hφ : AnalyticAt ℂ (bottcherCoord c₁) ((quadratic c₁)^[d+1] z) :=
      ((differentiableOn_bottcherCoord c₁).analyticOnNhd (isOpen_escapeOpen c₁)) _
        (hExtesc z hz)
    have hit : AnalyticAt ℂ (fun w => (quadratic c₁)^[d+1] w) z :=
      (analyticOnNhd_quadratic_iterate c₁ (d+1)) z (Set.mem_univ _)
    exact hφ.comp hit
  let aExt : analyticSubring Ext :=
    ⟨(↑(fun z => bottcherCoord c₁ ((quadratic c₁)^[d+1] z)) : Germ (𝓟 Ext) ℂ),
      fun z => bottcherCoord c₁ ((quadratic c₁)^[d+1] z), hradan, rfl⟩
  refine ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂, aExt, rfl, ?_⟩
  intro T hT
  obtain ⟨γ, γ', β, β', m, hγExt, hγcont, hγ'cont, hdγ, hγclosed, havoid,
    hlift, hvel, hwindβ⟩ := hloops T hT
  refine ⟨γ, γ', m, hγExt, hγcont, hγ'cont, hdγ, hγclosed, havoid, ?_⟩
  calc
    (∫ θ in (0:ℝ)..(2 * Real.pi),
        ((quadratic c₁)^[d+1] (γ θ))⁻¹ *
          ((∏ j ∈ Finset.range (d+1), 2 * (quadratic c₁)^[j] (γ θ)) * γ' θ))
        = ∫ θ in (0:ℝ)..(2 * Real.pi), (β θ)⁻¹ * β' θ := by
          refine intervalIntegral.integral_congr ?_
          intro θ _hθ
          change ((quadratic c₁)^[d+1] (γ θ))⁻¹ *
              ((∏ j ∈ Finset.range (d+1), 2 * (quadratic c₁)^[j] (γ θ)) * γ' θ)
            = (β θ)⁻¹ * β' θ
          rw [hlift θ, hvel θ]
    _ = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1) := hwindβ

end Bottcher
