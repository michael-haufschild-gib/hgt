# Event–boundary identity conjecture and causal-slice no-go (2026-07-29)

## Frozen physical conjecture
Card: `docs/drafts/pipeline/1-in-progress/event-boundary-identity-spacetime-law.md`.
Frozen before proof-route search under the truth-hunch rule in `mem:research/conjecture-selection-truth-hunch-before-proof`.

Public law:
> Time does not pass through space. Every event creates space, and gravity is the disagreement between those creations.

Event-boundary identity:
> An event and a boundary are the same act of reality viewed in two directions: as change in time, and as separation in space.

TOE separation:
> The three quantum forces govern what can differ across a boundary. Gravity governs what a boundary is.

The exact surviving open core is whether one source-complete primitive actualization determines both admissible succession and objective joint variability without importing time, causal order, or a subsystem split. Priority and truth remain open. Nature verdict remains DO NOT WRITE MANUSCRIPT.

## Hostile frontier result
Causal sets already derive causal direction and spatial antichains from one order, so that slogan is occupied. A stronger causality-only realization fails exactly.

For a poset, define augmented incomparability by
`x ~ y ↔ ¬ x < y ∧ ¬ y < x`.
Every event has a greatest antichain through it iff augmented incomparability is transitive. Hence its classes are antichains and the quotient is linearly ordered: the poset is a strict weak order, an ordinal stack of simultaneity layers. In finite posets this is equivalent to each element lying in exactly one maximal antichain.

This is rediscovered order theory, not new scientific knowledge.

Paper card:
`docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/canonical-event-slice-weak-order-collapse.md`

Lean card:
`docs/drafts/pipeline/3-formalized/canonical-event-slice-weak-order-collapse.md`

Lean:
`formal/GaloisForLFunctions/HTGeometry/CanonicalEventSlice.lean`
imported by `formal/GaloisForLFunctions/HTGeometry.lean`.

Exact formal theorem:
`orderGreatestCausalSlices_iff_augmentedIncomparable_transitive`.
Related pointwise formulation:
`greatestCausalSlices_iff_augmentedIncomparable_transitive`.

Verification:
- `lake env lean GaloisForLFunctions/HTGeometry/CanonicalEventSlice.lean` passed.
- Final audit `lake build GaloisForLFunctions.HTGeometry.CanonicalEventSlice` passed (429 jobs).
- Axiom audit: main exact theorem uses only `propext`; quotient corollaries additionally use standard `Classical.choice` and `Quot.sound`.
- `scripts/formal_tools.py lint` passed.

## Scientific consequence
Causal order alone cannot canonically assign one complete space to each event without collapsing to absolute ordered simultaneity layers. Therefore the event-boundary identity, if true, needs primitive joint-variability/compatibility data richer than order. Multiple slices already occur in flat relativity and cannot themselves be gravity. Gravity must be sought in nonintegrability of comparing admissible event-relative boundaries after compatibility is operationally defined.

Next core:
Can one source-complete datum determine succession and joint variability without importing causal order or subsystem factorization?