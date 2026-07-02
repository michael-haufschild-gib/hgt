/-
# General both-connected q62, conditional on the exposed one-sided point (L4)

This wires the open-problem-6 shape into the pigeonhole tip chain.

* `exists_oneSided_offOther_of_dense` — with one-sided density on both Julia sets (the classical
  ray-landing input `OneSidedDense`), the exposure dichotomy (L2) already produces a one-sided
  point of one set off the other filled set (after a swap).  The *only* remaining gap to
  `ExposedOneSided` is the visibility-from-infinity (`∂W`) upgrade — open problem 6.
* `q62_phiMero_independence_of_exposed_oneSided` — the general capstone: replacing the abstract
  hole-free-tip input of `q62_phiMero_independence_of_monodromy_tip_rigidity` by an exposed
  one-sided point (via the L3 certificate `holeFreeTip_of_oneSided`).
* `q62_phiMero_bothconnected_of_op6` — the both-connected specialization: for distinct
  nonexceptional connected parameters, the honest open-problem-6 disjunction
  `ExposedOneSided c₁ c₂ ∨ ExposedOneSided c₂ c₁` together with smooth-piece rigidity (both
  orientations) yields `NoRelation` for the pair, orienting the swapped branch with
  `noRelation_symm`.

So the general both-connected case is conditional on exactly: `OneSidedDense` (classical epic
#133), `ExposedOneSided` (open problem 6), and `SmoothPieceRigidity` (classical epic #118).
Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.Q62TipRigidityCapstone
import GaloisForLFunctions.Bottcher.OneSidedCertificate
import GaloisForLFunctions.Bottcher.FullContainment

open Polynomial Set Metric

namespace Bottcher

/-- **One-sided density forces a one-sided point off the other filled set (after a swap).**  The
exposure dichotomy L2 applied to the one-sided witnesses of `OneSidedDense`.  The residual gap to
`ExposedOneSided` is precisely the `∂W` visibility upgrade (open problem 6). -/
theorem exists_oneSided_offOther_of_dense {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂)
    (hd₁ : OneSidedDense c₁) (hd₂ : OneSidedDense c₂) :
    (∃ x, OneSidedAt c₁ x ∧ x ∉ filledJulia c₂) ∨
      (∃ x, OneSidedAt c₂ x ∧ x ∉ filledJulia c₁) := by
  have hD₁ : frontier (filledJulia c₁) ⊆ closure {q | OneSidedAt c₁ q} := by
    intro p hp
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨q, hq, hdist⟩ := hd₁ p hp ε hε
    exact ⟨q, hq, hdist⟩
  have hD₂ : frontier (filledJulia c₂) ⊆ closure {q | OneSidedAt c₂ q} := by
    intro p hp
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨q, hq, hdist⟩ := hd₂ p hp ε hε
    exact ⟨q, hq, hdist⟩
  rcases exists_exposed_of_dense_frontier hne hD₁ hD₂ with ⟨x, hx, hx2⟩ | ⟨x, hx, hx1⟩
  · exact Or.inl ⟨x, hx, hx2⟩
  · exact Or.inr ⟨x, hx, hx1⟩

/-- **General q62 from an exposed one-sided point.**  As `q62_phiMero_independence_of_monodromy_tip_rigidity`,
but the both-connected tip input is supplied by an exposed one-sided point through the certificate
`holeFreeTip_of_oneSided`. -/
theorem q62_phiMero_independence_of_exposed_oneSided
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
    (hexp : c₁ ∈ mandelbrot → c₂ ∈ mandelbrot → ExposedOneSided c₁ c₂)
    (hrig : c₁ ∈ mandelbrot → c₂ ∈ mandelbrot → SmoothPieceRigidity c₁ c₂) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  refine q62_phiMero_independence_of_monodromy_tip_rigidity hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂
    hc₁0 hc₁2 hc₂0 hc₂2 hmono₁ hmono₂ ?_ hrig
  intro h1 h2
  obtain ⟨x, hos, hx2, hvis⟩ := hexp h1 h2
  obtain ⟨r, _, htip⟩ := holeFreeTip_of_oneSided hos hx2 hvis
  exact ⟨x, r, htip⟩

/-- **Both-connected q62 from open problem 6.**  For distinct nonexceptional *connected*
parameters, the open-problem-6 disjunction (an exposed one-sided point after a swap) plus
smooth-piece rigidity in both orientations gives algebraic independence of the two Böttcher
coordinates.  The disconnected-side monodromy Props are vacuous (both parameters lie in `M`). -/
theorem q62_phiMero_bothconnected_of_op6
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ} (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁2 : c₁ ≠ -2) (hc₂0 : c₂ ≠ 0) (hc₂2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hexp : ExposedOneSided c₁ c₂ ∨ ExposedOneSided c₂ c₁)
    (hrig12 : SmoothPieceRigidity c₁ c₂) (hrig21 : SmoothPieceRigidity c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  rcases hexp with hL | hR
  · exact q62_phiMero_independence_of_exposed_oneSided hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂
      hc₁0 hc₁2 hc₂0 hc₂2 (fun h => absurd hc₁M h) (fun h => absurd hc₂M h)
      (fun _ _ => hL) (fun _ _ => hrig12)
  · exact noRelation_symm
      (q62_phiMero_independence_of_exposed_oneSided hUo hUc hUne hUinf c₂ c₁ hU₂ hU₁
        hc₂0 hc₂2 hc₁0 hc₁2 (fun h => absurd hc₂M h) (fun h => absurd hc₁M h)
        (fun _ _ => hR) (fun _ _ => hrig21))

end Bottcher
