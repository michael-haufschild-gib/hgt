/-
# Both-connected q62 pair, `hnb` discharged: reduced to exposure + `hinput`

The natural-boundary rigidity engine
`noRelation_phiMero_of_naturalBoundary_global_gamma_frontier_separable` produces the both-connected
pair `NoRelation (RatFunc ℂ) (phiMero c₁) (phiMero c₂)` from four inputs:

* `hG` — transcendence of `φ_{c₂}` (proven, `phiMero_transcendental_of_mem_mandelbrot`);
* the **exposure** data — `γ = bottcherCoord c₂` analytic on the basin `K_{c₁}ᶜ` *and across the
  frontier* `∂K_{c₁}`, matching on `U` (the `∂K_{c₁} ⊆ K_{c₂}ᶜ` clause, #124);
* `hnb` — the Böttcher branch has the Julia frontier as a genuine natural boundary;
* `hinput` — the pigeonhole frontier-fibre producer (#112–117, scaffolded).

With `hnb_of_mem_mandelbrot_connected` / `hnb_of_branch_matching` now proving `hnb` unconditionally for
every connected `c₁ ∈ mandelbrot ∖ {0,-2}` (the interior-nonempty sub-gap of #118, closed), `hnb` is no
longer a caller obligation. This file discharges it inside the engine, leaving the both-connected pair
`NoRelation` conditional on **exactly** exposure + `hinput`.

Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.InteriorNonemptyHnb
import GaloisForLFunctions.Bottcher.RelativeRigidityNaturalBoundary

open Polynomial Filter Topology Set Metric U0NaturalBoundary

namespace Bottcher

variable {U : Set ℂ}

/-- **Both-connected q62 pair with `hnb` discharged.** For a connected `c₁ ∈ mandelbrot ∖ {0,-2}` and a
Böttcher branch `β` on `K_{c₁}ᶜ` matching `bottcherCoord c₁` on `escapeOpen c₁`, the natural-boundary
rigidity engine's `hnb` hypothesis is supplied internally by `hnb_of_branch_matching`. Hence the
both-connected pair `NoRelation (phiMero c₁) (phiMero c₂)` follows from just the transcendence `hG`
(proven elsewhere), the exposure data (`γ = bottcherCoord c₂` analytic on `K_{c₁}ᶜ` and across
`∂K_{c₁}`, matching on `U` — the #124 collar clause), and the pigeonhole frontier-fibre producer
`hinput` (#112–117). `hnb` (#118) is off the critical path. -/
theorem noRelation_phiMero_bothConnected_hnbFree
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hc₁M : c₁ ∈ mandelbrot) (hc₁0 : c₁ ≠ 0) (hc₁2 : c₁ ≠ -2)
    (hconn₁ : IsPreconnected (filledJulia c₁))
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγfront : AnalyticOnNhd ℂ γ (frontier (filledJulia c₁)))
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ),
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  have hnb := hnb_of_branch_matching hc₁M hc₁0 hc₁2 hconn₁ hβan hβesc
  exact noRelation_phiMero_of_naturalBoundary_global_gamma_frontier_separable hUo hUc hUne hUinf
    c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan hγfront hγmatch hnb hinput

end Bottcher
