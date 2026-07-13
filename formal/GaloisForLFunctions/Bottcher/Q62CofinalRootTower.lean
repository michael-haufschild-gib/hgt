import GaloisForLFunctions.Bottcher.Q62RootTower
import GaloisForLFunctions.Bottcher.OneSidedCofinal

/-!
# q62 cofinal one-sided capstones for root towers

This file lifts the cofinal and neighbourhood-cofinal one-sided q62 capstones to arbitrary
finite Kummer roots of the two Böttcher coordinates.
-/

namespace Bottcher

noncomputable section

/-- Root-tower descent for the exposed cofinal one-sided q62 capstone. -/
theorem q62_phiMero_independence_of_exposed_oneSidedCofinal_roots
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hc₁0 : c₁ ≠ 0) (hc₁2 : c₁ ≠ -2) (hc₂0 : c₂ ≠ 0) (hc₂2 : c₂ ≠ -2)
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
    (hexp : c₁ ∈ mandelbrot → c₂ ∈ mandelbrot → ExposedOneSidedCofinal c₁ c₂)
    (hrig : c₁ ∈ mandelbrot → c₂ ∈ mandelbrot → SmoothPieceRigidity c₁ c₂) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hNR := q62_phiMero_independence_of_exposed_oneSidedCofinal
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hc₁0 hc₁2 hc₂0 hc₂2
    hmono₁ hmono₂ hexp hrig
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

/-- Root-tower descent for the both-connected cofinal OP6 q62 capstone. -/
theorem q62_phiMero_bothconnected_of_op6_cofinal_roots
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ} (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁2 : c₁ ≠ -2) (hc₂0 : c₂ ≠ 0) (hc₂2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hexp : ExposedOneSidedCofinal c₁ c₂ ∨ ExposedOneSidedCofinal c₂ c₁)
    (hrig12 : SmoothPieceRigidity c₁ c₂) (hrig21 : SmoothPieceRigidity c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hNR := q62_phiMero_bothconnected_of_op6_cofinal hUo hUc hUne hUinf
    hc₁M hc₂M hc₁0 hc₁2 hc₂0 hc₂2 hU₁ hU₂ hexp hrig12 hrig21
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

/-- Root-tower descent for the exposed neighbourhood-cofinal one-sided q62 capstone. -/
theorem q62_phiMero_independence_of_exposed_oneSidedCofinalNbhd_roots
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hc₁0 : c₁ ≠ 0) (hc₁2 : c₁ ≠ -2) (hc₂0 : c₂ ≠ 0) (hc₂2 : c₂ ≠ -2)
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
    (hrig : c₁ ∈ mandelbrot → c₂ ∈ mandelbrot → SmoothPieceRigidity c₁ c₂) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hNR := q62_phiMero_independence_of_exposed_oneSidedCofinalNbhd
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hc₁0 hc₁2 hc₂0 hc₂2
    hmono₁ hmono₂ hexp hrig
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

/-- Root-tower descent for the both-connected neighbourhood-cofinal OP6 q62 capstone. -/
theorem q62_phiMero_bothconnected_of_op6_cofinalNbhd_roots
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ} (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁2 : c₁ ≠ -2) (hc₂0 : c₂ ≠ 0) (hc₂2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hexp : ExposedOneSidedCofinalNbhd c₁ c₂ ∨ ExposedOneSidedCofinalNbhd c₂ c₁)
    (hrig12 : SmoothPieceRigidity c₁ c₂) (hrig21 : SmoothPieceRigidity c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hNR := q62_phiMero_bothconnected_of_op6_cofinalNbhd hUo hUc hUne hUinf
    hc₁M hc₂M hc₁0 hc₁2 hc₂0 hc₂2 hU₁ hU₂ hexp hrig12 hrig21
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

/-- Root-tower descent for the real-pair cofinal connected-beta q62 capstone. -/
theorem q62_phiMero_realPair_of_connected_beta_roots
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℝ} (hlt : c₁ < c₂) (hc₁2 : -2 ≤ c₁) (hc₂4 : c₂ ≤ 1 / 4)
    (hc₁0 : (c₁ : ℂ) ≠ 0) (hc₁m2 : (c₁ : ℂ) ≠ -2) (hc₂0 : (c₂ : ℂ) ≠ 0)
    (hc₂m2 : (c₂ : ℂ) ≠ -2)
    (hU₁ : U ⊆ escapeOpen (c₁ : ℂ)) (hU₂ : U ⊆ escapeOpen (c₂ : ℂ))
    (hconn : ∀ ε > 0, ∃ ρ, 0 < ρ ∧ ρ < ε ∧
      IsConnected (Metric.ball (betaFixed c₁ : ℂ) ρ \ filledJulia (c₁ : ℂ)))
    (hrig12 : SmoothPieceRigidity (c₁ : ℂ) (c₂ : ℂ))
    (hrig21 : SmoothPieceRigidity (c₂ : ℂ) (c₁ : ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero (c₁ : ℂ) hU₁ → η ^ q = phiMero (c₂ : ℂ) hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hNR := q62_phiMero_realPair_of_connected_beta hUo hUc hUne hUinf hlt hc₁2 hc₂4
    hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂ hconn hrig12 hrig21
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

/-- Root-tower descent for the real-pair neighbourhood-cofinal connected-beta q62 capstone. -/
theorem q62_phiMero_realPair_of_connected_beta_nbhd_roots
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℝ} (hlt : c₁ < c₂) (hc₁2 : -2 ≤ c₁) (hc₂4 : c₂ ≤ 1 / 4)
    (hc₁0 : (c₁ : ℂ) ≠ 0) (hc₁m2 : (c₁ : ℂ) ≠ -2) (hc₂0 : (c₂ : ℂ) ≠ 0)
    (hc₂m2 : (c₂ : ℂ) ≠ -2)
    (hU₁ : U ⊆ escapeOpen (c₁ : ℂ)) (hU₂ : U ⊆ escapeOpen (c₂ : ℂ))
    (hconn : ∀ ε > 0, ∃ V : Set ℂ, IsOpen V ∧ (betaFixed c₁ : ℂ) ∈ V ∧
      V ⊆ Metric.ball (betaFixed c₁ : ℂ) ε ∧
      IsConnected (V \ filledJulia (c₁ : ℂ)))
    (hrig12 : SmoothPieceRigidity (c₁ : ℂ) (c₂ : ℂ))
    (hrig21 : SmoothPieceRigidity (c₂ : ℂ) (c₁ : ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero (c₁ : ℂ) hU₁ → η ^ q = phiMero (c₂ : ℂ) hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hNR := q62_phiMero_realPair_of_connected_beta_nbhd hUo hUc hUne hUinf hlt hc₁2 hc₂4
    hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂ hconn hrig12 hrig21
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

end

end Bottcher
