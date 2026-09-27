# Universal unit differential-order cost for first-order entire cascades — Lean certificate

- **ID:** `universal-first-order-entire-cascade-unit-cost-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `universal-first-order-entire-cascade-unit-cost.md` (with the repaired
  Reduction III, section "Repair of Reduction III: the compatibility gap closes by regularity")
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Capstones

`GaloisForLFunctions.HTGeometry.exactDifferentialOrder_entireCascade_of_lt`
(`HTGeometry/EntireCascadeLaurentTower.lean`) — the card's theorem verbatim:

    (hall : ∀ k, k < n → TranscendentalEntire (f k))
    (h1   : ∀ k, k < n → DifferentiallyAlgebraicOfOrder (f k) 1) :
    ExactDifferentialOrder (entireCascade f n) n

with `entireCascade f n = f (n-1) ∘ ⋯ ∘ f 0`.  No further hypothesis.

Also: `exactDifferentialOrder_entireCascade_unconditional` (all `f i` transcendental entire) and the
lower bound `algebraicIndependent_jets_entireCascade`: the first `n` derivatives of the last state
are algebraically independent over `ℂ(z)` in the global meromorphic field.

Axiom audit (all three and every intermediate capstone listed below):
`[propext, Classical.choice, Quot.sound]`.

## What the corpus already had

The upper bound `ord ≤ n`, the reduction of exactness to jet independence
(`exactDifferentialOrder_entireCascade_of_transcendental`), Reduction I (the Wiman initial data and
the top-symbol Laurent root of each layer), the actual branch fields `B_N` of the cascade with their
derivation, inclusions, transcendence of the new state over the lower branch, generation by lower
branch + state + velocity, and the layer relation on the local jet.

## What was built

Generic (field theory / Laurent series):

- `LaurentCoefficientEulerDerivation`, `LaurentOutputJacobianLead` — coefficientwise and Euler
  derivations of `K((t))`; the leading term of an output-jet Jacobian (Bell/terminal-scaled row
  reduction).
- `LaurentLeadCalculus` — inverses, strict degree comparison, `t ↦ tᵐ` dilation.
- `CascadeLaurentLevelJacobian` — the layer derivations `δ = δ_K − (A/N) t d/dt`,
  `∂ = −(1/N) tᴺ t d/dt`, and the Jacobian descent: base, step (`δV/V + λW`), top.
- `FirstOrderRelationLaurentBranch`, `FirstOrderWimanRootBaseChange` — Newton–Puiseux branch with
  prescribed top-symbol lead over any algebraically closed char-0 field; Wiman root base change.
- `RegularExtensionMinpoly` — minimal polynomials over relatively algebraically closed subfields,
  degree exchange, and `irreducible_map_of_regular_embedding`.
- `FirstOrderRelationSpecialization` — Zariski specialisation of a factorization to a finite
  extension of `ℂ(U)`.
- `TwistedDerivationKernel`, `RationalFunctionFieldRootExtension` — derivations along field maps
  vanish on separable algebraic elements; extension of a field map across `X` transcendental and
  `v` a root of an irreducible `Q(X, W)`.
- `CascadeTowerStep` — `CascadeModel` (algebraically closed model with time and coordinate
  derivations and a differential embedding), `WimanLead`, the tower step `exists_step`, the next
  model, `model_top`, `model_wimanLead`, and the Jacobian criterion `algebraicIndependent_iterate`.

Analytic:

- `EntireAlgebraicRatioRational`, `MeromorphicRationalRelativeClosure` — `ℂ(z)` is relatively
  algebraically closed in the global meromorphic field.
- `FirstOrderRelationAbsoluteIrreducibility` — `relIrrVia_wiman`: the first-order relation of a
  transcendental entire function is irreducible over `F(V)` for every field `F ⊇ ℂ(U)`.

Concrete assembly: `EntireCascadeLaurentTower` — base model `ℂ(z)̄`, layer-0 Wiman lead (nonzero
top-symbol root), the tower induction `exists_cascadeModel_wimanLead`, and the capstones.

## Mathematical note

The paper's original Reduction III (terminal-inward valuation prolongation) had an unclosed
compatibility step.  The Lean proof follows the repaired argument recorded on the paper card:
regularity of `ℂ(z)` in the meromorphic field makes every layer relation absolutely irreducible,
so every root of the layer relation in any extension defines an embedding; the tower is then built
bottom-up and the Jacobian descends by the invariant `(Inv_j)`.
