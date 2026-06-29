/-
# Separated local-collar input for the Q62 disconnected capstone

The odd-winding loop cannot live in the same single-sheet slit collar whose
forward image stays in `Complex.slitPlane`: a closed loop in one logarithm sheet
has zero `∫ w⁻¹ dw`.  The useful interface therefore separates the witnesses:
`Ext` carries the odd image-winding loop, while `ForwardCollarData` records the
local one-sheet branch geometry.
-/
import GaloisForLFunctions.Bottcher.LocalCollar
import GaloisForLFunctions.Bottcher.Q62DeepDataAssembly

open Complex Set Filter Polynomial
open scoped BigOperators

namespace Bottcher

/-- Q62 disconnected/disconnected from separated data: a larger escape domain `Ext` carrying the odd
image-winding loop, plus an independent forward collar for the local one-sheet branch geometry. -/
theorem q62_disconnected_of_separated_forwardCollar_imageWinding_escape
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
    (data : ∀ d : ℕ, ∃ (Ext A E : Set ℂ) (y₀ : ℝ),
      IsOpen Ext ∧ IsConnected Ext ∧ Ext.Infinite ∧ U ⊆ Ext ∧
      (∀ z ∈ Ext, (quadratic c₁)^[d+1] z ∈ escapeOpen c₁) ∧
      Ext ⊆ escapeOpen c₂ ∧
      ForwardCollarData c₁ c₂ (d + 1) A E y₀ ∧ A ⊆ Ext ∧
      (∀ T : Set ℂ, T.Countable →
        ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
          (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
          (∀ θ : ℝ, HasDerivAt γ (γ' θ) θ) ∧
          γ (2 * Real.pi) = γ 0 ∧
          (∀ θ : ℝ, (quadratic c₁)^[d+1] (γ θ) ∉ T) ∧
          (∫ θ in (0:ℝ)..(2 * Real.pi),
              ((quadratic c₁)^[d+1] (γ θ))⁻¹ *
                ((∏ j ∈ Finset.range (d+1), 2 * (quadratic c₁)^[j] (γ θ)) * γ' θ))
            = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  apply q62_disconnected_of_imageWindingDeepData_escape hUo hUc hUne hUinf
    hUesc a₁ a₂ ha₁ ha₂ hF hGtr
  intro d
  obtain ⟨Ext, A, E, y₀, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂,
    _hcollar, _hAExt, hloops⟩ := data d
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
  exact ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂, aExt, rfl, hloops⟩

end Bottcher
