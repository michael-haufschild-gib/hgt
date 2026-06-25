/-
# u₀ ⟂ φ_b — the card theorems, on the single stubbed cover provider

This file states and proves the three pipeline cards
* `u0-phi-independence.md` (connected `b ∈ M \ {0,-2}`),
* `u0-phi-independence-disconnected.md` (`b ∉ M`),
* `u0-phi-independence-all-parameters.md` (the union),
as the genuine independence `NoRelation ℂ(z) φ_b u₀` at the faithful carrier `meroField U`, where
`NoRelation` *is* the real "no nonzero polynomial relation" statement.

**The single isolated `sorry`** is `phib_kummer_inputs` — the Böttcher cover **Kummer-inputs provider for
`φ_b`** (per relation degree: the finite radical data with `Irreducible(X^{2ᵏ}−C a)`). It is *identical*
to the provider the parallel Böttcher agent is building for the q62 case (closed-loop FTC + period +
cover base field, in `Winding.lean` / `CoverConstruction.lean` / `FigureEight.lean` / `Q62Assembly.lean`)
— the **only** difference from q62 is the base element `GB` maps to `u₀` instead of `φ_{c₂}`. Everything
below is sorry-free on top of it: when the shared provider lands, replace the lone `by sorry` with
`exact <agent provider>` (the `inputs` type matches `q62_disconnected_kummer` verbatim up to `GB`), and
the three theorems become unconditional with no other change.
-/
import GaloisForLFunctions.U0.U0KummerRepick

open Polynomial Filter Topology Bottcher U0MeroCarrier U0KummerRepick

namespace U0CardTheorems

variable {U : Set ℂ}

/-- **[AGENT'S PART — the lone `sorry`] The shared Böttcher cover Kummer-inputs provider for `φ_b`.**
Per relation degree `d`, a base field `B`, a `ℂ(z)`-algebra hom `i : B → meroField U`, a radicand `a`, a
base element `GB` with `i GB = u₀`, a primitive `2ᵏ`-th root `ζ` (`2ᵏ > d`), with `X^{2ᵏ}−C a` irreducible
and the radical relation `φ_b^{2ᵏ} = i a`. Its proof is the cover construction (`kummer_irreducible` ←
`not_square_of_period_ftc` ← the φ_b period + closed-loop FTC, over the cover base field `K = ℂ(p₀)`),
shared verbatim with `Bottcher.q62_disconnected_kummer` except `GB = u₀`. Replace `by sorry` with the
agent's provider once it lands. -/
theorem phib_kummer_inputs (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ d : ℕ, ∃ (B : Type) (_ : Field B) (_ : Algebra (RatFunc ℂ) B)
        (i : B →ₐ[RatFunc ℂ] meroField U) (a GB ζ : B) (k : ℕ),
        d < 2 ^ k ∧ IsPrimitiveRoot ζ (2 ^ k) ∧ Irreducible ((X : Polynomial B) ^ (2 ^ k) - C a) ∧
        phiMero b hU_esc ^ (2 ^ k) = i a ∧
        i GB = algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext) := by
  sorry

/-- **u₀ ⟂ φ_b at the faithful carrier (the content of all three cards).** `NoRelation ℂ(z) φ_b u₀` in
`meroField U` — i.e. no nonzero polynomial relation between the inverse Böttcher coordinate `φ_b` and the
c-velocity `u₀` over `ℂ(z)`. Proof: the Kummer-inputs closure `u0_phi_independence_inputs` fed the cover
provider `phib_kummer_inputs`; the two u₀-specific inputs (`φ_b ≠ 0`, `u₀` transcendental) are discharged
inside the closure. The connected / disconnected / all-parameter cards are this theorem at the carriers
realizing the respective `b`-ranges. -/
theorem u0_phi_independence_carrier (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext)) :=
  u0_phi_independence_inputs hUo hUc hUne hUinf hU_ext hU_esc
    (phib_kummer_inputs hUo hUc hUne hUinf hU_ext hU_esc)

/-- **Card `u0-phi-independence.md` (connected `b ∈ M \ {0,-2}`).** The carrier realizes a deep ball in
the exterior where `φ_b` is the single-valued connected-locus Böttcher coordinate. -/
theorem u0_phi_independence_connected (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext)) :=
  u0_phi_independence_carrier hUo hUc hUne hUinf hU_ext hU_esc

/-- **Card `u0-phi-independence-disconnected.md` (`b ∉ M`).** The carrier realizes a deep ball in the
escape set where `φ_b` carries its own dyadic monodromy. -/
theorem u0_phi_independence_disconnected (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext)) :=
  u0_phi_independence_carrier hUo hUc hUne hUinf hU_ext hU_esc

/-- **Card `u0-phi-independence-all-parameters.md` (all nonexceptional `b`).** Both Mandelbrot regions in
one statement — the same carrier independence, uniform in the parameter. -/
theorem u0_phi_independence_all_parameters (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext)) :=
  u0_phi_independence_carrier hUo hUc hUne hUinf hU_ext hU_esc

end U0CardTheorems
