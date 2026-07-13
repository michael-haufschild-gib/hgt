import GaloisForLFunctions.Bottcher.Q62RootTower
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

/-- Root-tower descent for the direct one-sided visible-off-other orientation. -/
theorem q62_phiMero_independence_conditional_oneSide_visibleOffOtherFrontierOneSided_smoothArcSelection_roots
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
    (hsel₁ : c₁ ∈ mandelbrot → SmoothArcSelection c₁)
    (hoff₁₂ : c₁ ∈ mandelbrot → c₂ ∈ mandelbrot →
      ∃ x, x ∈ filledJulia c₁ ∧ x ∉ filledJulia c₂)
    (hone₁₂ : c₁ ∈ mandelbrot → c₂ ∈ mandelbrot →
      VisibleOffOtherFrontierOneSidedCofinalNbhd c₁ c₂) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  exact q62_phiMero_independence_conditional_oneSide_visibleOffOtherFrontierOneSided_smoothArcSelection_or_swap_roots
    hUo hUc hUne hUinf hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂ hmono₁ hmono₂
    (Or.inl ⟨hsel₁, hoff₁₂, hone₁₂⟩)

/-- Root-tower descent for the swapped one-sided visible-off-other orientation. -/
theorem q62_phiMero_independence_conditional_oneSide_visibleOffOtherFrontierOneSided_smoothArcSelection_swapped_roots
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
    (hsel₂ : c₂ ∈ mandelbrot → SmoothArcSelection c₂)
    (hoff₂₁ : c₂ ∈ mandelbrot → c₁ ∈ mandelbrot →
      ∃ x, x ∈ filledJulia c₂ ∧ x ∉ filledJulia c₁)
    (hone₂₁ : c₂ ∈ mandelbrot → c₁ ∈ mandelbrot →
      VisibleOffOtherFrontierOneSidedCofinalNbhd c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  exact q62_phiMero_independence_conditional_oneSide_visibleOffOtherFrontierOneSided_smoothArcSelection_or_swap_roots
    hUo hUc hUne hUinf hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂ hmono₁ hmono₂
    (Or.inr ⟨hsel₂, hoff₂₁, hone₂₁⟩)

/-- Root-tower descent for the direct exposed one-sided cofinal orientation. -/
theorem q62_phiMero_independence_conditional_exposedOneSidedCofinalNbhd_smoothArcSelection_roots
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
    (hexp : c₁ ∈ mandelbrot → c₂ ∈ mandelbrot → ExposedOneSidedCofinalNbhd c₁ c₂)
    (hsel₁ : c₁ ∈ mandelbrot → SmoothArcSelection c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  exact q62_phiMero_independence_conditional_exposedOneSidedCofinalNbhd_smoothArcSelection_or_swap_roots
    hUo hUc hUne hUinf hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂ hmono₁ hmono₂
    (Or.inl ⟨hexp, hsel₁⟩)

/-- Root-tower descent for the swapped exposed one-sided cofinal orientation. -/
theorem q62_phiMero_independence_conditional_exposedOneSidedCofinalNbhd_smoothArcSelection_swapped_roots
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
    (hexp₂₁ : c₂ ∈ mandelbrot → c₁ ∈ mandelbrot → ExposedOneSidedCofinalNbhd c₂ c₁)
    (hsel₂ : c₂ ∈ mandelbrot → SmoothArcSelection c₂) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  exact q62_phiMero_independence_conditional_exposedOneSidedCofinalNbhd_smoothArcSelection_or_swap_roots
    hUo hUc hUne hUinf hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂ hmono₁ hmono₂
    (Or.inr ⟨hexp₂₁, hsel₂⟩)

/-- All-placement root-tower q62 from dense local one-sidedness plus off-other visibility.

This packages the bridge
`exposedOneSidedCofinalNbhd_or_swap_of_locOneSidedDense` with the conditional q62 dispatcher:
the disconnected branches are the explicit monodromy inputs, connected one-coordinate
transcendence is discharged from `c ∈ M`, and the both-connected branch is reduced to dense
local one-sidedness, off-other visibility, and smooth-piece rigidity. -/
theorem q62_phiMero_independence_conditional_locOneSidedDense_visible_roots
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
    (hd₁ : LocOneSidedDense c₁) (hd₂ : LocOneSidedDense c₂)
    (hvis₁₂ : OffOtherCofinalNbhdVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdVisible c₂ c₁)
    (hrig₁₂ : SmoothPieceRigidity c₁ c₂)
    (hrig₂₁ : SmoothPieceRigidity c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hNR :
      NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
    refine q62_phiMero_independence_conditional hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂
      (fun c => c ∉ mandelbrot) hmono₁ hmono₂ ?_ ?_ ?_
    · intro hc₁notNotM
      have hc₁M : c₁ ∈ mandelbrot := by
        by_contra hc₁notM
        exact hc₁notNotM hc₁notM
      exact phiMero_transcendental_of_mem_mandelbrot hUo hUc hUne hUinf
        hc₁M hc₁0 hc₁m2 hU₁
    · intro hc₂notNotM
      have hc₂M : c₂ ∈ mandelbrot := by
        by_contra hc₂notM
        exact hc₂notNotM hc₂notM
      exact phiMero_transcendental_of_mem_mandelbrot hUo hUc hUne hUinf
        hc₂M hc₂0 hc₂m2 hU₂
    · intro hc₁notNotM hc₂notNotM
      have hc₁M : c₁ ∈ mandelbrot := by
        by_contra hc₁notM
        exact hc₁notNotM hc₁notM
      have hc₂M : c₂ ∈ mandelbrot := by
        by_contra hc₂notM
        exact hc₂notNotM hc₂notM
      have hexp :=
        exposedOneSidedCofinalNbhd_or_swap_of_locOneSidedDense hne hd₁ hd₂
          hvis₁₂ hvis₂₁
      exact q62_phiMero_bothconnected_of_op6_cofinalNbhd hUo hUc hUne hUinf
        hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂ hexp hrig₁₂ hrig₂₁
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

/-- Joint-frontier visibility variant of
`q62_phiMero_independence_conditional_locOneSidedDense_visible_roots`. -/
theorem q62_phiMero_independence_conditional_locOneSidedDense_jointFrontierVisible_roots
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
    (hd₁ : LocOneSidedDense c₁) (hd₂ : LocOneSidedDense c₂)
    (hvis₁₂ : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdJointFrontierVisible c₂ c₁)
    (hrig₁₂ : SmoothPieceRigidity c₁ c₂)
    (hrig₂₁ : SmoothPieceRigidity c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  exact q62_phiMero_independence_conditional_locOneSidedDense_visible_roots
    hUo hUc hUne hUinf hne hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂
    hmono₁ hmono₂ hd₁ hd₂
    (offOtherCofinalNbhdVisible_of_jointFrontierVisible hvis₁₂)
    (offOtherCofinalNbhdVisible_of_jointFrontierVisible hvis₂₁)
    hrig₁₂ hrig₂₁

/-- Both-connected root-tower q62 from the fixed-point Brolin bridge, with the
non-postcritical fixed targets selected internally and no parabolic fixed-point exclusion. -/
theorem q62_phiMero_bothconnected_of_fixedPoint_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia_all_notPostcritical_jointFrontierVisibility_roots
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a →
      a ∉ positiveCriticalOrbit c₁ → OneSidedAtCofinalNbhd c₁ a)
    (hsupp₁ : ∀ a : ℂ, quadratic c₁ a = a → LimitingBrolinMeasureAtSupportsJulia c₁ a)
    (hbase₂ : ∀ a : ℂ, quadratic c₂ a = a →
      a ∉ positiveCriticalOrbit c₂ → OneSidedAtCofinalNbhd c₂ a)
    (hsupp₂ : ∀ a : ℂ, quadratic c₂ a = a → LimitingBrolinMeasureAtSupportsJulia c₂ a)
    (hvis₁₂ : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdJointFrontierVisible c₂ c₁)
    (hrig₁₂ : SmoothPieceRigidity c₁ c₂)
    (hrig₂₁ : SmoothPieceRigidity c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hNR :=
    q62_phiMero_bothconnected_of_fixedPoint_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia_all_notPostcritical_jointFrontierVisibility
      hUo hUc hUne hUinf hne hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂
      hbase₁ hsupp₁ hbase₂ hsupp₂ hvis₁₂ hvis₂₁ hrig₁₂ hrig₂₁
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

/-- All-placement root-tower q62 from the fixed-point Brolin bridge, with no
parabolic fixed-point exclusion.  The only remaining non-disconnected inputs are fixed-point
neighbourhood-cofinal one-sidedness, Brolin support at fixed points, joint-frontier visibility, and
smooth-piece rigidity. -/
theorem q62_phiMero_independence_of_monodromy_fixedPoint_cofinalNbhd_brolin_notPostcritical_jointFrontierVisibility_all_roots
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
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a →
      a ∉ positiveCriticalOrbit c₁ → OneSidedAtCofinalNbhd c₁ a)
    (hsupp₁ : ∀ a : ℂ, quadratic c₁ a = a → LimitingBrolinMeasureAtSupportsJulia c₁ a)
    (hbase₂ : ∀ a : ℂ, quadratic c₂ a = a →
      a ∉ positiveCriticalOrbit c₂ → OneSidedAtCofinalNbhd c₂ a)
    (hsupp₂ : ∀ a : ℂ, quadratic c₂ a = a → LimitingBrolinMeasureAtSupportsJulia c₂ a)
    (hvis₁₂ : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdJointFrontierVisible c₂ c₁)
    (hrig₁₂ : SmoothPieceRigidity c₁ c₂)
    (hrig₂₁ : SmoothPieceRigidity c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hNR :=
    q62_phiMero_independence_of_monodromy_fixedPoint_cofinalNbhd_brolin_notPostcritical_jointFrontierVisibility_all
      hUo hUc hUne hUinf hne hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂
      hmono₁ hmono₂ hbase₁ hsupp₁ hbase₂ hsupp₂ hvis₁₂ hvis₂₁ hrig₁₂ hrig₂₁
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

/-- Asymmetric fixed-target Brolin support q62, lifted directly to finite roots. -/
theorem q62_phiMero_oneSide_brolin_frontierOff_smoothArcSelection_jointFrontierVisibility_roots
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ}
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hconn₁ : IsPreconnected (filledJulia c₁))
    (hsel₁ : SmoothArcSelection c₁)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a →
      a ∉ positiveCriticalOrbit c₁ → OneSidedAtCofinalNbhd c₁ a)
    (hsupp₁ : ∀ a : ℂ, quadratic c₁ a = a → LimitingBrolinMeasureAtSupportsJulia c₁ a)
    (hoff : ∃ p, p ∈ frontier (filledJulia c₁) ∧ p ∉ filledJulia c₂)
    (hvis : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  have hNR :=
    q62_phiMero_oneSide_brolin_frontierOff_smoothArcSelection_jointFrontierVisibility
      hUo hUc hUne hUinf hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hconn₁ hsel₁
      hU₁ hU₂ hbase₁ hsupp₁ hoff hvis
  intro χ η p q hχ hη
  exact q62_phiMero_roots_of_noRelation hUo hUc hUne hUinf hNR hχ hη

/-- Asymmetric fixed-target Brolin support q62 with connectedness supplied by
membership in `mandelbrot`, lifted directly to finite roots. -/
theorem q62_phiMero_oneSide_brolin_frontierOff_smoothArcSelection_of_mem_jointFrontierVisibility_roots
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ}
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hsel₁ : SmoothArcSelection c₁)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a →
      a ∉ positiveCriticalOrbit c₁ → OneSidedAtCofinalNbhd c₁ a)
    (hsupp₁ : ∀ a : ℂ, quadratic c₁ a = a → LimitingBrolinMeasureAtSupportsJulia c₁ a)
    (hoff : ∃ p, p ∈ frontier (filledJulia c₁) ∧ p ∉ filledJulia c₂)
    (hvis : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  have hNR :=
    q62_phiMero_oneSide_brolin_frontierOff_smoothArcSelection_of_mem_jointFrontierVisibility
      hUo hUc hUne hUinf hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hsel₁
      hU₁ hU₂ hbase₁ hsupp₁ hoff hvis
  intro χ η p q hχ hη
  exact q62_phiMero_roots_of_noRelation hUo hUc hUne hUinf hNR hχ hη

/-- Asymmetric explicit-target Brolin ball q62 with one-sided cofinal-neighborhood
data, lifted directly to finite roots. -/
theorem q62_phiMero_oneSide_target_brolinBall_oneSidedNbhd_frontierOff_smoothArcSelection_of_mem_jointFrontierVisibility_roots
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ z₁ : ℂ}
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hsel₁ : SmoothArcSelection c₁)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : OneSidedAtCofinalNbhd c₁ z₁)
    (hpos₁ : BrolinJuliaBallPositiveAt c₁ z₁)
    (hcrit₁ : z₁ ∉ positiveCriticalOrbit c₁)
    (hoff : ∃ p, p ∈ frontier (filledJulia c₁) ∧ p ∉ filledJulia c₂)
    (hvis : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  have hNR :=
    q62_phiMero_oneSide_target_brolinBall_oneSidedNbhd_frontierOff_smoothArcSelection_of_mem_jointFrontierVisibility
      hUo hUc hUne hUinf hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hsel₁ hU₁ hU₂
      hbase₁ hpos₁ hcrit₁ hoff hvis
  intro χ η p q hχ hη
  exact q62_phiMero_roots_of_noRelation hUo hUc hUne hUinf hNR hχ hη

/-- Asymmetric explicit-target Brolin ball q62 with one-sided cofinal data,
lifted directly to finite roots. -/
theorem q62_phiMero_oneSide_target_brolinBall_oneSidedCofinal_frontierOff_smoothArcSelection_of_mem_jointFrontierVisibility_roots
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ z₁ : ℂ}
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hsel₁ : SmoothArcSelection c₁)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : OneSidedAtCofinal c₁ z₁)
    (hpos₁ : BrolinJuliaBallPositiveAt c₁ z₁)
    (hcrit₁ : z₁ ∉ positiveCriticalOrbit c₁)
    (hoff : ∃ p, p ∈ frontier (filledJulia c₁) ∧ p ∉ filledJulia c₂)
    (hvis : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  have hNR :=
    q62_phiMero_oneSide_target_brolinBall_oneSidedCofinal_frontierOff_smoothArcSelection_of_mem_jointFrontierVisibility
      hUo hUc hUne hUinf hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hsel₁ hU₁ hU₂
      hbase₁ hpos₁ hcrit₁ hoff hvis
  intro χ η p q hχ hη
  exact q62_phiMero_roots_of_noRelation hUo hUc hUne hUinf hNR hχ hη

/-- Asymmetric explicit-target Brolin ball q62 with strong one-sided data,
lifted directly to finite roots. -/
theorem q62_phiMero_oneSide_target_brolinBall_oneSided_frontierOff_smoothArcSelection_of_mem_jointFrontierVisibility_roots
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ z₁ : ℂ}
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hsel₁ : SmoothArcSelection c₁)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : OneSidedAt c₁ z₁)
    (hpos₁ : BrolinJuliaBallPositiveAt c₁ z₁)
    (hcrit₁ : z₁ ∉ positiveCriticalOrbit c₁)
    (hoff : ∃ p, p ∈ frontier (filledJulia c₁) ∧ p ∉ filledJulia c₂)
    (hvis : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  have hNR :=
    q62_phiMero_oneSide_target_brolinBall_oneSided_frontierOff_smoothArcSelection_of_mem_jointFrontierVisibility
      hUo hUc hUne hUinf hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hsel₁ hU₁ hU₂
      hbase₁ hpos₁ hcrit₁ hoff hvis
  intro χ η p q hχ hη
  exact q62_phiMero_roots_of_noRelation hUo hUc hUne hUinf hNR hχ hη

/-- Both-connected Brolin support q62, lifted directly to finite roots without
the all-placement monodromy dispatcher. -/
theorem q62_phiMero_bothconnected_brolin_frontierOffDichotomy_smoothArcSelection_of_mem_jointFrontierVisibility_roots
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hsel₁ : SmoothArcSelection c₁)
    (hsel₂ : SmoothArcSelection c₂)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a →
      a ∉ positiveCriticalOrbit c₁ → OneSidedAtCofinalNbhd c₁ a)
    (hsupp₁ : ∀ a : ℂ, quadratic c₁ a = a → LimitingBrolinMeasureAtSupportsJulia c₁ a)
    (hbase₂ : ∀ a : ℂ, quadratic c₂ a = a →
      a ∉ positiveCriticalOrbit c₂ → OneSidedAtCofinalNbhd c₂ a)
    (hsupp₂ : ∀ a : ℂ, quadratic c₂ a = a → LimitingBrolinMeasureAtSupportsJulia c₂ a)
    (hvis₁₂ : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdJointFrontierVisible c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  have hNR :=
    q62_phiMero_bothconnected_brolin_frontierOffDichotomy_smoothArcSelection_of_mem_jointFrontierVisibility
      hUo hUc hUne hUinf hne hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hsel₁ hsel₂
      hU₁ hU₂ hbase₁ hsupp₁ hbase₂ hsupp₂ hvis₁₂ hvis₂₁
  intro χ η p q hχ hη
  exact q62_phiMero_roots_of_noRelation hUo hUc hUne hUinf hNR hχ hη

/-- Both-connected Brolin ball-positivity q62, lifted directly to finite roots. -/
theorem q62_phiMero_bothconnected_brolinBall_frontierOffDichotomy_smoothArcSelection_of_mem_jointFrontierVisibility_roots
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hsel₁ : SmoothArcSelection c₁)
    (hsel₂ : SmoothArcSelection c₂)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a →
      a ∉ positiveCriticalOrbit c₁ → OneSidedAtCofinalNbhd c₁ a)
    (hpos₁ : ∀ a : ℂ, quadratic c₁ a = a → BrolinJuliaBallPositiveAt c₁ a)
    (hbase₂ : ∀ a : ℂ, quadratic c₂ a = a →
      a ∉ positiveCriticalOrbit c₂ → OneSidedAtCofinalNbhd c₂ a)
    (hpos₂ : ∀ a : ℂ, quadratic c₂ a = a → BrolinJuliaBallPositiveAt c₂ a)
    (hvis₁₂ : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdJointFrontierVisible c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  have hNR :=
    q62_phiMero_bothconnected_brolinBall_frontierOffDichotomy_smoothArcSelection_of_mem_jointFrontierVisibility
      hUo hUc hUne hUinf hne hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hsel₁ hsel₂
      hU₁ hU₂ hbase₁ hpos₁ hbase₂ hpos₂ hvis₁₂ hvis₂₁
  intro χ η p q hχ hη
  exact q62_phiMero_roots_of_noRelation hUo hUc hUne hUinf hNR hχ hη

/-- Both-connected Brolin ball q62 with strong one-sided fixed-point data away
from the positive critical orbit, lifted directly to finite roots. -/
theorem q62_phiMero_bothconnected_brolinBall_oneSided_frontierOffDichotomy_smoothArcSelection_of_mem_jointFrontierVisibility_roots
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hsel₁ : SmoothArcSelection c₁)
    (hsel₂ : SmoothArcSelection c₂)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a →
      a ∉ positiveCriticalOrbit c₁ → OneSidedAt c₁ a)
    (hpos₁ : ∀ a : ℂ, quadratic c₁ a = a → BrolinJuliaBallPositiveAt c₁ a)
    (hbase₂ : ∀ a : ℂ, quadratic c₂ a = a →
      a ∉ positiveCriticalOrbit c₂ → OneSidedAt c₂ a)
    (hpos₂ : ∀ a : ℂ, quadratic c₂ a = a → BrolinJuliaBallPositiveAt c₂ a)
    (hvis₁₂ : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdJointFrontierVisible c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  have hNR :=
    q62_phiMero_bothconnected_brolinBall_oneSided_frontierOffDichotomy_smoothArcSelection_of_mem_jointFrontierVisibility
      hUo hUc hUne hUinf hne hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hsel₁ hsel₂
      hU₁ hU₂ hbase₁ hpos₁ hbase₂ hpos₂ hvis₁₂ hvis₂₁
  intro χ η p q hχ hη
  exact q62_phiMero_roots_of_noRelation hUo hUc hUne hUinf hNR hχ hη

/-- Both-connected Brolin ball q62 when every fixed point is strongly one-sided,
lifted directly to finite roots. -/
theorem q62_phiMero_bothconnected_brolinBall_allFixedOneSided_smoothArcSelection_of_mem_jointFrontierVisibility_roots
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hsel₁ : SmoothArcSelection c₁)
    (hsel₂ : SmoothArcSelection c₂)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a → OneSidedAt c₁ a)
    (hpos₁ : ∀ a : ℂ, quadratic c₁ a = a → BrolinJuliaBallPositiveAt c₁ a)
    (hbase₂ : ∀ a : ℂ, quadratic c₂ a = a → OneSidedAt c₂ a)
    (hpos₂ : ∀ a : ℂ, quadratic c₂ a = a → BrolinJuliaBallPositiveAt c₂ a)
    (hvis₁₂ : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdJointFrontierVisible c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  have hNR :=
    q62_phiMero_bothconnected_brolinBall_allFixedOneSided_smoothArcSelection_of_mem_jointFrontierVisibility
      hUo hUc hUne hUinf hne hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hsel₁ hsel₂
      hU₁ hU₂ hbase₁ hpos₁ hbase₂ hpos₂ hvis₁₂ hvis₂₁
  intro χ η p q hχ hη
  exact q62_phiMero_roots_of_noRelation hUo hUc hUne hUinf hNR hχ hη

/-- Explicit-target both-connected Brolin ball q62 with one-sided
cofinal-neighborhood data, lifted directly to finite roots. -/
theorem q62_phiMero_bothconnected_target_brolinBall_oneSidedNbhd_frontierOffDichotomy_smoothArcSelection_of_mem_jointFrontierVisibility_roots
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ z₁ z₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hsel₁ : SmoothArcSelection c₁)
    (hsel₂ : SmoothArcSelection c₂)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : OneSidedAtCofinalNbhd c₁ z₁)
    (hpos₁ : BrolinJuliaBallPositiveAt c₁ z₁)
    (hcrit₁ : z₁ ∉ positiveCriticalOrbit c₁)
    (hbase₂ : OneSidedAtCofinalNbhd c₂ z₂)
    (hpos₂ : BrolinJuliaBallPositiveAt c₂ z₂)
    (hcrit₂ : z₂ ∉ positiveCriticalOrbit c₂)
    (hvis₁₂ : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdJointFrontierVisible c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  have hNR :=
    q62_phiMero_bothconnected_target_brolinBall_oneSidedNbhd_frontierOffDichotomy_smoothArcSelection_of_mem_jointFrontierVisibility
      hUo hUc hUne hUinf hne hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hsel₁ hsel₂ hU₁ hU₂
      hbase₁ hpos₁ hcrit₁ hbase₂ hpos₂ hcrit₂ hvis₁₂ hvis₂₁
  intro χ η p q hχ hη
  exact q62_phiMero_roots_of_noRelation hUo hUc hUne hUinf hNR hχ hη

/-- Explicit-target both-connected Brolin ball q62 with one-sided cofinal data,
lifted directly to finite roots. -/
theorem q62_phiMero_bothconnected_target_brolinBall_oneSidedCofinal_frontierOffDichotomy_smoothArcSelection_of_mem_jointFrontierVisibility_roots
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ z₁ z₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hsel₁ : SmoothArcSelection c₁)
    (hsel₂ : SmoothArcSelection c₂)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : OneSidedAtCofinal c₁ z₁)
    (hpos₁ : BrolinJuliaBallPositiveAt c₁ z₁)
    (hcrit₁ : z₁ ∉ positiveCriticalOrbit c₁)
    (hbase₂ : OneSidedAtCofinal c₂ z₂)
    (hpos₂ : BrolinJuliaBallPositiveAt c₂ z₂)
    (hcrit₂ : z₂ ∉ positiveCriticalOrbit c₂)
    (hvis₁₂ : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdJointFrontierVisible c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  have hNR :=
    q62_phiMero_bothconnected_target_brolinBall_oneSidedCofinal_frontierOffDichotomy_smoothArcSelection_of_mem_jointFrontierVisibility
      hUo hUc hUne hUinf hne hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hsel₁ hsel₂ hU₁ hU₂
      hbase₁ hpos₁ hcrit₁ hbase₂ hpos₂ hcrit₂ hvis₁₂ hvis₂₁
  intro χ η p q hχ hη
  exact q62_phiMero_roots_of_noRelation hUo hUc hUne hUinf hNR hχ hη

/-- Explicit-target both-connected Brolin ball q62 with strong one-sided data,
lifted directly to finite roots. -/
theorem q62_phiMero_bothconnected_target_brolinBall_oneSided_frontierOffDichotomy_smoothArcSelection_of_mem_jointFrontierVisibility_roots
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ z₁ z₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hsel₁ : SmoothArcSelection c₁)
    (hsel₂ : SmoothArcSelection c₂)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : OneSidedAt c₁ z₁)
    (hpos₁ : BrolinJuliaBallPositiveAt c₁ z₁)
    (hcrit₁ : z₁ ∉ positiveCriticalOrbit c₁)
    (hbase₂ : OneSidedAt c₂ z₂)
    (hpos₂ : BrolinJuliaBallPositiveAt c₂ z₂)
    (hcrit₂ : z₂ ∉ positiveCriticalOrbit c₂)
    (hvis₁₂ : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdJointFrontierVisible c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  have hNR :=
    q62_phiMero_bothconnected_target_brolinBall_oneSided_frontierOffDichotomy_smoothArcSelection_of_mem_jointFrontierVisibility
      hUo hUc hUne hUinf hne hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hsel₁ hsel₂ hU₁ hU₂
      hbase₁ hpos₁ hcrit₁ hbase₂ hpos₂ hcrit₂ hvis₁₂ hvis₂₁
  intro χ η p q hχ hη
  exact q62_phiMero_roots_of_noRelation hUo hUc hUne hUinf hNR hχ hη

/-- Root-tower q62 from the Brolin support bridge with smooth-arc selection and
explicit connectedness supplied on connected parameters. -/
theorem q62_phiMero_independence_of_monodromy_brolin_smoothArcSelection_jointFrontierVisibility_all_roots
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
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a →
      a ∉ positiveCriticalOrbit c₁ → OneSidedAtCofinalNbhd c₁ a)
    (hsupp₁ : ∀ a : ℂ, quadratic c₁ a = a → LimitingBrolinMeasureAtSupportsJulia c₁ a)
    (hbase₂ : ∀ a : ℂ, quadratic c₂ a = a →
      a ∉ positiveCriticalOrbit c₂ → OneSidedAtCofinalNbhd c₂ a)
    (hsupp₂ : ∀ a : ℂ, quadratic c₂ a = a → LimitingBrolinMeasureAtSupportsJulia c₂ a)
    (hconn₁ : c₁ ∈ mandelbrot → IsPreconnected (filledJulia c₁))
    (hsel₁ : c₁ ∈ mandelbrot → SmoothArcSelection c₁)
    (hconn₂ : c₂ ∈ mandelbrot → IsPreconnected (filledJulia c₂))
    (hsel₂ : c₂ ∈ mandelbrot → SmoothArcSelection c₂)
    (hvis₁₂ : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdJointFrontierVisible c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hNR :=
    q62_phiMero_independence_of_monodromy_brolin_smoothArcSelection_jointFrontierVisibility_all
      hUo hUc hUne hUinf hne hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂ hmono₁ hmono₂
      hbase₁ hsupp₁ hbase₂ hsupp₂ hconn₁ hsel₁ hconn₂ hsel₂ hvis₁₂ hvis₂₁
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

/-- Root-tower q62 from the Brolin support bridge with connectedness supplied
internally by membership in `mandelbrot`. -/
theorem q62_phiMero_independence_of_monodromy_brolin_smoothArcSelection_of_mem_jointFrontierVisibility_all_roots
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
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a →
      a ∉ positiveCriticalOrbit c₁ → OneSidedAtCofinalNbhd c₁ a)
    (hsupp₁ : ∀ a : ℂ, quadratic c₁ a = a → LimitingBrolinMeasureAtSupportsJulia c₁ a)
    (hbase₂ : ∀ a : ℂ, quadratic c₂ a = a →
      a ∉ positiveCriticalOrbit c₂ → OneSidedAtCofinalNbhd c₂ a)
    (hsupp₂ : ∀ a : ℂ, quadratic c₂ a = a → LimitingBrolinMeasureAtSupportsJulia c₂ a)
    (hsel₁ : c₁ ∈ mandelbrot → SmoothArcSelection c₁)
    (hsel₂ : c₂ ∈ mandelbrot → SmoothArcSelection c₂)
    (hvis₁₂ : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdJointFrontierVisible c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hNR :=
    q62_phiMero_independence_of_monodromy_brolin_smoothArcSelection_of_mem_jointFrontierVisibility_all
      hUo hUc hUne hUinf hne hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂ hmono₁ hmono₂
      hbase₁ hsupp₁ hbase₂ hsupp₂ hsel₁ hsel₂ hvis₁₂ hvis₂₁
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

/-- Root-tower q62 from the Brolin ball-positivity bridge with cofinal-neighborhood
one-sided fixed-point inputs. -/
theorem q62_phiMero_independence_of_monodromy_brolinBall_smoothArcSelection_of_mem_jointFrontierVisibility_all_roots
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
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a →
      a ∉ positiveCriticalOrbit c₁ → OneSidedAtCofinalNbhd c₁ a)
    (hpos₁ : ∀ a : ℂ, quadratic c₁ a = a → BrolinJuliaBallPositiveAt c₁ a)
    (hbase₂ : ∀ a : ℂ, quadratic c₂ a = a →
      a ∉ positiveCriticalOrbit c₂ → OneSidedAtCofinalNbhd c₂ a)
    (hpos₂ : ∀ a : ℂ, quadratic c₂ a = a → BrolinJuliaBallPositiveAt c₂ a)
    (hsel₁ : c₁ ∈ mandelbrot → SmoothArcSelection c₁)
    (hsel₂ : c₂ ∈ mandelbrot → SmoothArcSelection c₂)
    (hvis₁₂ : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdJointFrontierVisible c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hNR :=
    q62_phiMero_independence_of_monodromy_brolinBall_smoothArcSelection_of_mem_jointFrontierVisibility_all
      hUo hUc hUne hUinf hne hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂ hmono₁ hmono₂
      hbase₁ hpos₁ hbase₂ hpos₂ hsel₁ hsel₂ hvis₁₂ hvis₂₁
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

/-- Root-tower q62 from the Brolin ball-positivity bridge with strong
one-sided fixed-point inputs away from the positive critical orbit. -/
theorem q62_phiMero_independence_of_monodromy_brolinBall_oneSided_smoothArcSelection_of_mem_jointFrontierVisibility_all_roots
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
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a →
      a ∉ positiveCriticalOrbit c₁ → OneSidedAt c₁ a)
    (hpos₁ : ∀ a : ℂ, quadratic c₁ a = a → BrolinJuliaBallPositiveAt c₁ a)
    (hbase₂ : ∀ a : ℂ, quadratic c₂ a = a →
      a ∉ positiveCriticalOrbit c₂ → OneSidedAt c₂ a)
    (hpos₂ : ∀ a : ℂ, quadratic c₂ a = a → BrolinJuliaBallPositiveAt c₂ a)
    (hsel₁ : c₁ ∈ mandelbrot → SmoothArcSelection c₁)
    (hsel₂ : c₂ ∈ mandelbrot → SmoothArcSelection c₂)
    (hvis₁₂ : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdJointFrontierVisible c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hNR :=
    q62_phiMero_independence_of_monodromy_brolinBall_oneSided_smoothArcSelection_of_mem_jointFrontierVisibility_all
      hUo hUc hUne hUinf hne hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂ hmono₁ hmono₂
      hbase₁ hpos₁ hbase₂ hpos₂ hsel₁ hsel₂ hvis₁₂ hvis₂₁
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

/-- All-placement root-tower q62 from the Brolin ball-positivity bridge when every fixed
point is strongly one-sided, with the smooth-piece gate supplied by `SmoothArcSelection`. -/
theorem q62_phiMero_independence_of_monodromy_brolinBall_allFixedOneSided_smoothArcSelection_of_mem_jointFrontierVisibility_all_roots
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
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a → OneSidedAt c₁ a)
    (hpos₁ : ∀ a : ℂ, quadratic c₁ a = a → BrolinJuliaBallPositiveAt c₁ a)
    (hbase₂ : ∀ a : ℂ, quadratic c₂ a = a → OneSidedAt c₂ a)
    (hpos₂ : ∀ a : ℂ, quadratic c₂ a = a → BrolinJuliaBallPositiveAt c₂ a)
    (hsel₁ : c₁ ∈ mandelbrot → SmoothArcSelection c₁)
    (hsel₂ : c₂ ∈ mandelbrot → SmoothArcSelection c₂)
    (hvis₁₂ : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdJointFrontierVisible c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hNR :=
    q62_phiMero_independence_of_monodromy_brolinBall_allFixedOneSided_smoothArcSelection_of_mem_jointFrontierVisibility_all
      hUo hUc hUne hUinf hne hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂ hmono₁ hmono₂
      hbase₁ hpos₁ hbase₂ hpos₂ hsel₁ hsel₂ hvis₁₂ hvis₂₁
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

/-- Target-point root-tower q62 from the Brolin ball-positivity bridge with
one-sided cofinal-neighborhood data at the two selected Julia points. -/
theorem q62_phiMero_independence_of_monodromy_target_brolinBall_oneSidedNbhd_smoothArcSelection_of_mem_jointFrontierVisibility_all_roots
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ z₁ z₂ : ℂ} (hne : c₁ ≠ c₂)
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
    (hbase₁ : OneSidedAtCofinalNbhd c₁ z₁)
    (hpos₁ : BrolinJuliaBallPositiveAt c₁ z₁)
    (hcrit₁ : z₁ ∉ positiveCriticalOrbit c₁)
    (hbase₂ : OneSidedAtCofinalNbhd c₂ z₂)
    (hpos₂ : BrolinJuliaBallPositiveAt c₂ z₂)
    (hcrit₂ : z₂ ∉ positiveCriticalOrbit c₂)
    (hsel₁ : c₁ ∈ mandelbrot → SmoothArcSelection c₁)
    (hsel₂ : c₂ ∈ mandelbrot → SmoothArcSelection c₂)
    (hvis₁₂ : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdJointFrontierVisible c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hNR :=
    q62_phiMero_independence_of_monodromy_target_brolinBall_oneSidedNbhd_smoothArcSelection_of_mem_jointFrontierVisibility_all
      hUo hUc hUne hUinf hne hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂ hmono₁ hmono₂
      hbase₁ hpos₁ hcrit₁ hbase₂ hpos₂ hcrit₂ hsel₁ hsel₂ hvis₁₂ hvis₂₁
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

/-- Target-point root-tower q62 from the Brolin ball-positivity bridge with
one-sided cofinal data at the two selected Julia points. -/
theorem q62_phiMero_independence_of_monodromy_target_brolinBall_oneSidedCofinal_smoothArcSelection_of_mem_jointFrontierVisibility_all_roots
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ z₁ z₂ : ℂ} (hne : c₁ ≠ c₂)
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
    (hbase₁ : OneSidedAtCofinal c₁ z₁)
    (hpos₁ : BrolinJuliaBallPositiveAt c₁ z₁)
    (hcrit₁ : z₁ ∉ positiveCriticalOrbit c₁)
    (hbase₂ : OneSidedAtCofinal c₂ z₂)
    (hpos₂ : BrolinJuliaBallPositiveAt c₂ z₂)
    (hcrit₂ : z₂ ∉ positiveCriticalOrbit c₂)
    (hsel₁ : c₁ ∈ mandelbrot → SmoothArcSelection c₁)
    (hsel₂ : c₂ ∈ mandelbrot → SmoothArcSelection c₂)
    (hvis₁₂ : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdJointFrontierVisible c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hNR :=
    q62_phiMero_independence_of_monodromy_target_brolinBall_oneSidedCofinal_smoothArcSelection_of_mem_jointFrontierVisibility_all
      hUo hUc hUne hUinf hne hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂ hmono₁ hmono₂
      hbase₁ hpos₁ hcrit₁ hbase₂ hpos₂ hcrit₂ hsel₁ hsel₂ hvis₁₂ hvis₂₁
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

/-- Target-point root-tower q62 from the Brolin ball-positivity bridge with
one-sided data at the two selected Julia points. -/
theorem q62_phiMero_independence_of_monodromy_target_brolinBall_oneSided_smoothArcSelection_of_mem_jointFrontierVisibility_all_roots
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ z₁ z₂ : ℂ} (hne : c₁ ≠ c₂)
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
    (hbase₁ : OneSidedAt c₁ z₁)
    (hpos₁ : BrolinJuliaBallPositiveAt c₁ z₁)
    (hcrit₁ : z₁ ∉ positiveCriticalOrbit c₁)
    (hbase₂ : OneSidedAt c₂ z₂)
    (hpos₂ : BrolinJuliaBallPositiveAt c₂ z₂)
    (hcrit₂ : z₂ ∉ positiveCriticalOrbit c₂)
    (hsel₁ : c₁ ∈ mandelbrot → SmoothArcSelection c₁)
    (hsel₂ : c₂ ∈ mandelbrot → SmoothArcSelection c₂)
    (hvis₁₂ : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdJointFrontierVisible c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hNR :=
    q62_phiMero_independence_of_monodromy_target_brolinBall_oneSided_smoothArcSelection_of_mem_jointFrontierVisibility_all
      hUo hUc hUne hUinf hne hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂ hmono₁ hmono₂
      hbase₁ hpos₁ hcrit₁ hbase₂ hpos₂ hcrit₂ hsel₁ hsel₂ hvis₁₂ hvis₂₁
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

end

end Bottcher
