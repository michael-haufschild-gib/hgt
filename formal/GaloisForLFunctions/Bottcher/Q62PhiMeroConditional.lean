/-
# Concrete conditional capstone for Nguyen Q6.2 (quadratic) on the genuine Böttcher carrier

The abstract top theorem `q62_independence` quantifies over an arbitrary field pair `K, M`, an
abstract coordinate `φ`, and an abstract Mandelbrot-placement predicate `Disc`.  This file collapses
the whole development into **one statement on the actual carrier** `K = ℂ(z)`, `M = meroField U`,
coordinates `phiMero c₁, phiMero c₂`, whose hypotheses are exactly the named analytic inputs that
remain open, organised by Mandelbrot placement:

* a **disconnected** parameter `cᵢ` contributes an unbounded dyadic monodromy of `phiMero cᵢ` that
  fixes the other coordinate (the Cantor-basin monodromy);
* a **connected** parameter `cᵢ` contributes transcendence of `phiMero cᵢ` over `ℂ(z)`, and — when
  both are connected — algebraic independence directly.  These are precisely the outputs of the
  connected Böttcher-branch + natural-boundary + crossing-producer reductions.

`Disc : ℂ → Prop` is an arbitrary placement predicate; the proof only case-splits on it.  The four
cases dispatch to `q62_disconnected_both` (both disconnected), `q62_mixed` (exactly one disconnected,
with `noRelation_symm` orienting the second mixed case), and the supplied both-connected
independence.  No new mathematics: pure assembly of already-proved theorems.
-/
import GaloisForLFunctions.Bottcher.Q62
import GaloisForLFunctions.Bottcher.RelativeRigidityCountableAvoidance

open Polynomial

namespace Bottcher

/-- **Conditional Q6.2 on the genuine carrier.**  For distinct nonexceptional `c₁, c₂`, the Böttcher
coordinates `phiMero c₁, phiMero c₂` are algebraically independent over `ℂ(z)`, conditional on the
named inputs for whichever Mandelbrot placement holds (see file header). -/
theorem q62_phiMero_independence_conditional
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (Disc : ℂ → Prop)
    (hmono₁ : Disc c₁ →
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ d : ℕ, ∃ (σ : meroField U ≃ₐ[RatFunc ℂ] meroField U) (ζ : meroField U) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧ σ (phiMero c₂ hU₂) = phiMero c₂ hU₂ ∧ σ ζ = ζ ∧
        σ (phiMero c₁ hU₁) = ζ * phiMero c₁ hU₁)
    (hmono₂ : Disc c₂ →
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ d : ℕ, ∃ (σ : meroField U ≃ₐ[RatFunc ℂ] meroField U) (ζ : meroField U) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧ σ (phiMero c₁ hU₁) = phiMero c₁ hU₁ ∧ σ ζ = ζ ∧
        σ (phiMero c₂ hU₂) = ζ * phiMero c₂ hU₂)
    (htrans₁ : ¬ Disc c₁ →
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (htrans₂ : ¬ Disc c₂ →
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (hbothconn : ¬ Disc c₁ → ¬ Disc c₂ →
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hF₁ : phiMero c₁ hU₁ ≠ 0 := phiMero_ne_zero hUo hUc hUne hU₁
  have hF₂ : phiMero c₂ hU₂ ≠ 0 := phiMero_ne_zero hUo hUc hUne hU₂
  by_cases h1 : Disc c₁
  · by_cases h2 : Disc c₂
    · -- both disconnected: q62_disconnected_both (F = φ₁, G = φ₂)
      refine q62_disconnected_both (phiMero c₁ hU₁) (phiMero c₂ hU₂) hF₁ hF₂ (hmono₁ h1) ?_
      intro d
      obtain ⟨σ, ζ, m, hdm, hord, _hfix, hζ, hscale⟩ := hmono₂ h2 d
      exact ⟨σ, ζ, by rw [hord]; exact hdm, hζ, hscale⟩
    · -- mixed: c₁ disconnected, c₂ connected
      exact q62_mixed (phiMero c₁ hU₁) (phiMero c₂ hU₂) hF₁ (htrans₂ h2) (hmono₁ h1)
  · by_cases h2 : Disc c₂
    · -- mixed: c₂ disconnected, c₁ connected (orient with noRelation_symm)
      exact noRelation_symm
        (q62_mixed (phiMero c₂ hU₂) (phiMero c₁ hU₁) hF₂ (htrans₁ h1) (hmono₂ h2))
    · -- both connected
      exact hbothconn h1 h2

end Bottcher
