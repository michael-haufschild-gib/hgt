/-
# U0 all-nonexceptional canonical Böttcher target

This file states the uncompromised U0 target:

* no large-parameter restriction;
* no viable-region `ψ_N` in the conclusion;
* no anonymous Kummer root in the conclusion;
* the actual Böttcher coordinate `phiMero b` on a faithful escape carrier;
* exactly the nonexceptional parameter range `b ≠ 0, -2`.

The Kummer-provider formulation below is retained as a reusable reduction.  The provider is discharged
without hypotheses in `U0AllNonexceptionalDisconnected`, where the connected and disconnected window
constructions are assembled separately.
-/
import GaloisForLFunctions.U0.U0CardTheorems

open Complex Set Metric Bottcher Filter Topology
open U0MeroCarrier

namespace U0AllNonexceptional

/-- The uncompromised U0 conclusion at a single parameter: on some faithful escape carrier, the
actual canonical Böttcher coordinate `phiMero b` is algebraically independent from `u₀` over `ℂ(z)`.

The carrier is existential because the connected and disconnected constructions may choose different
windows.  The coordinate in the conclusion is not an auxiliary `ψ_N` or a chosen Kummer root: it is
`Bottcher.phiMero b hU_esc`, i.e. the germ of `bottcherCoord b` on the escape carrier. -/
def CanonicalPhiU0IndependenceAt (b : ℂ) : Prop :=
  ∃ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hUinf : U.Infinite) (hU_esc : U ⊆ escapeOpen b),
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) :=
      (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U)
        (u0AnSub (hU_esc.trans (U0CardTheorems.escapeOpen_subset_U0Ext b))))

/-- A legacy provider interface for the all-nonexceptional U0 theorem.

For every `b ≠ 0, -2`, it supplies a faithful escape carrier and the finite Kummer-input data for
the canonical Böttcher coordinate `phiMero b` on that carrier. -/
def CanonicalPhiU0KummerProvider : Prop :=
  ∀ b : ℂ, b ≠ 0 → b ≠ (-2 : ℂ) →
    ∃ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
      (hUinf : U.Infinite) (hU_esc : U ⊆ escapeOpen b),
      U0CardTheorems.PhibKummerInputs hUo hUc hUne hUinf
        (hU_esc.trans (U0CardTheorems.escapeOpen_subset_U0Ext b)) hU_esc

/-- **All nonexceptional canonical U0-Böttcher independence.**

Assuming an all-nonexceptional carrier/Kummer provider, every parameter except the
monomial and Chebyshev exceptions satisfies the genuine canonical conclusion
`u₀ ⟂ phiMero b` over `ℂ(z)` on a faithful escape carrier. -/
theorem u0_phi_independence_all_nonexceptional_canonical_of_provider
    (hprovider : CanonicalPhiU0KummerProvider) :
    ∀ b : ℂ, b ≠ 0 → b ≠ (-2 : ℂ) → CanonicalPhiU0IndependenceAt b := by
  intro b hb0 hb2
  rcases hprovider b hb0 hb2 with ⟨U, hUo, hUc, hUne, hUinf, hU_esc, hKummer⟩
  refine ⟨U, hUo, hUc, hUne, hUinf, hU_esc, ?_⟩
  exact U0CardTheorems.u0_phi_independence_all_parameters hUo hUc hUne hUinf
    (hU_esc.trans (U0CardTheorems.escapeOpen_subset_U0Ext b)) hU_esc hKummer

end U0AllNonexceptional
