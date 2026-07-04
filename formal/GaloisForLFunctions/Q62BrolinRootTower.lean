import GaloisForLFunctions.Q62RootTower
import GaloisForLFunctions.Bottcher.Q62BackwardOrbitBrolin

/-!
# q62 Brolin capstones for root towers

This file lifts the strongest Brolin/visibility conditional q62 capstones from the base
Boettcher functions to arbitrary Kummer roots.  It is intentionally separate from
`Q62RootTower` so the basic root-tower interface does not import the Brolin-heavy geometry.
-/

namespace Bottcher

noncomputable section

/-- Root-tower descent for the all-placement visible-access q62 bridge. -/
theorem q62_phiMero_independence_conditional_visibleOffOtherFrontierOneSided_smoothArcSelection_roots
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hmono₁ : c₁ ∉ mandelbrot →
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ d : ℕ, ∃ (σ : meroField U ≃ₐ[RatFunc ℂ] meroField U) (ζ : meroField U) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧ σ (phiMero c₂ hU₂) = phiMero c₂ hU₂ ∧ σ ζ = ζ ∧
        σ (phiMero c₁ hU₁) = ζ * phiMero c₁ hU₁)
    (hmono₂ : c₂ ∉ mandelbrot →
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ d : ℕ, ∃ (σ : meroField U ≃ₐ[RatFunc ℂ] meroField U) (ζ : meroField U) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧ σ (phiMero c₁ hU₁) = phiMero c₁ hU₁ ∧ σ ζ = ζ ∧
        σ (phiMero c₂ hU₂) = ζ * phiMero c₂ hU₂)
    (hsel₁ : c₁ ∈ mandelbrot → SmoothArcSelection c₁)
    (hsel₂ : c₂ ∈ mandelbrot → SmoothArcSelection c₂)
    (hone₁₂ : c₁ ∈ mandelbrot → c₂ ∈ mandelbrot →
      VisibleOffOtherFrontierOneSidedCofinalNbhd c₁ c₂)
    (hone₂₁ : c₂ ∈ mandelbrot → c₁ ∈ mandelbrot →
      VisibleOffOtherFrontierOneSidedCofinalNbhd c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hNR :=
    q62_phiMero_independence_conditional_visibleOffOtherFrontierOneSided_smoothArcSelection
      hUo hUc hUne hUinf hne hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂
      hmono₁ hmono₂ hsel₁ hsel₂ hone₁₂ hone₂₁
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

/-- Root-tower descent for either one-sided visible-off-other connected orientation. -/
theorem q62_phiMero_independence_conditional_oneSide_visibleOffOtherFrontierOneSided_smoothArcSelection_or_swap_roots
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ}
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hmono₁ : c₁ ∉ mandelbrot →
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ d : ℕ, ∃ (σ : meroField U ≃ₐ[RatFunc ℂ] meroField U) (ζ : meroField U) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧ σ (phiMero c₂ hU₂) = phiMero c₂ hU₂ ∧ σ ζ = ζ ∧
        σ (phiMero c₁ hU₁) = ζ * phiMero c₁ hU₁)
    (hmono₂ : c₂ ∉ mandelbrot →
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ d : ℕ, ∃ (σ : meroField U ≃ₐ[RatFunc ℂ] meroField U) (ζ : meroField U) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧ σ (phiMero c₁ hU₁) = phiMero c₁ hU₁ ∧ σ ζ = ζ ∧
        σ (phiMero c₂ hU₂) = ζ * phiMero c₂ hU₂)
    (horient :
      ((c₁ ∈ mandelbrot → SmoothArcSelection c₁) ∧
        (c₁ ∈ mandelbrot → c₂ ∈ mandelbrot →
          ∃ x, x ∈ filledJulia c₁ ∧ x ∉ filledJulia c₂) ∧
        (c₁ ∈ mandelbrot → c₂ ∈ mandelbrot →
          VisibleOffOtherFrontierOneSidedCofinalNbhd c₁ c₂)) ∨
      ((c₂ ∈ mandelbrot → SmoothArcSelection c₂) ∧
        (c₂ ∈ mandelbrot → c₁ ∈ mandelbrot →
          ∃ x, x ∈ filledJulia c₂ ∧ x ∉ filledJulia c₁) ∧
        (c₂ ∈ mandelbrot → c₁ ∈ mandelbrot →
          VisibleOffOtherFrontierOneSidedCofinalNbhd c₂ c₁))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hNR :=
    q62_phiMero_independence_conditional_oneSide_visibleOffOtherFrontierOneSided_smoothArcSelection_or_swap
      hUo hUc hUne hUinf hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂ hmono₁ hmono₂
      horient
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

/-- Root-tower descent for either exposed one-sided cofinal connected orientation. -/
theorem q62_phiMero_independence_conditional_exposedOneSidedCofinalNbhd_smoothArcSelection_or_swap_roots
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ}
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hmono₁ : c₁ ∉ mandelbrot →
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ d : ℕ, ∃ (σ : meroField U ≃ₐ[RatFunc ℂ] meroField U) (ζ : meroField U) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧ σ (phiMero c₂ hU₂) = phiMero c₂ hU₂ ∧ σ ζ = ζ ∧
        σ (phiMero c₁ hU₁) = ζ * phiMero c₁ hU₁)
    (hmono₂ : c₂ ∉ mandelbrot →
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ d : ℕ, ∃ (σ : meroField U ≃ₐ[RatFunc ℂ] meroField U) (ζ : meroField U) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧ σ (phiMero c₁ hU₁) = phiMero c₁ hU₁ ∧ σ ζ = ζ ∧
        σ (phiMero c₂ hU₂) = ζ * phiMero c₂ hU₂)
    (horient :
      ((c₁ ∈ mandelbrot → c₂ ∈ mandelbrot → ExposedOneSidedCofinalNbhd c₁ c₂) ∧
        (c₁ ∈ mandelbrot → SmoothArcSelection c₁)) ∨
      ((c₂ ∈ mandelbrot → c₁ ∈ mandelbrot → ExposedOneSidedCofinalNbhd c₂ c₁) ∧
        (c₂ ∈ mandelbrot → SmoothArcSelection c₂))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hNR :=
    q62_phiMero_independence_conditional_exposedOneSidedCofinalNbhd_smoothArcSelection_or_swap
      hUo hUc hUne hUinf hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂ hmono₁ hmono₂
      horient
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

end

end Bottcher
