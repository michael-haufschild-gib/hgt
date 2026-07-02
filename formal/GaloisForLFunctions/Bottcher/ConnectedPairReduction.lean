/-
# The both-connected pair, reduced to the single dendrite datum

The unconditional connected-case transcendence (Gap 4) discharges the `hG`-input of the
both-connected reduction: `NoRelation ℂ(z) φ_{c₁} φ_{c₂}` for connected nonexceptional pairs now
needs exactly ONE remaining input — the bivariate dendrite no-relation `hno`, itself isolated to
the Montel→Julia branch-boundary datum in `noRelation_phiMero_of_dendrite_input`.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.RelativeRigidityCapstone
import GaloisForLFunctions.Bottcher.ConnectedTranscendenceUnconditional

open Complex Set Filter

namespace Bottcher

variable {U : Set ℂ}

/-- **The both-connected pair on one input.**  For connected nonexceptional parameters, the pair
independence follows from the bivariate no-relation alone: the `φ_{c₂}`-transcendence input is
now the unconditional Gap 4 theorem. -/
theorem q62_independence_connected_of_hno
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hc₂M : c₂ ∈ mandelbrot)
    (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hno : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        ¬ Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hc₂0 : c₂ ≠ 0 := by
    intro h
    exact hx₂ (by rw [h]; exact Set.mem_insert 0 {-2})
  have hc₂2 : c₂ ≠ -2 := by
    intro h
    exact hx₂ (by rw [h]; exact Set.mem_insert_of_mem 0 rfl)
  exact q62_independence_connected_of_dynamical hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂
    hne hx₁ hx₂
    (phiMero_transcendental_of_mem_mandelbrot hUo hUc hUne hUinf hc₂M hc₂0 hc₂2 hU₂)
    hno

end Bottcher
