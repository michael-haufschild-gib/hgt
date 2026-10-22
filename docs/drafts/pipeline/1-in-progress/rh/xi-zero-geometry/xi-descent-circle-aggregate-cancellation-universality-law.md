# Xi-descent circle aggregate-cancellation universality law

- **ID:** xi-descent-circle-aggregate-cancellation
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** whole-corpus theorem-generated closure
- **Statement:** On every zero-avoiding Xi-descent circle, additive loop-charge vanishing and
  multiplicative cancellation of all enclosed local carrier charges are both equivalent to
  dyadic divisibility of total enclosed multiplicity.

## Goal

Classify global cancellation across an arbitrary finite family of enclosed Xi-descent zeros, rather
than requiring each local charge to vanish separately.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, proof generated from existing Lean theorems
- [x] 1 → 2 fully-proven: dependency-closed proof
- [x] 2 → 3 formalized: exact source check recorded below
- [ ] 3 → 4 publication-ready: deferred until global exhaustion and final audit

## Lean sources

- `GaloisForLFunctions.RHTower.XiDescentCircleLocalGlobalDeckChargeUniversalityLaw`
- `GaloisForLFunctions.RHTower.DeckChargeCalculus`

## Corpus gap

The corpus separately supplied the unconditional circle census, additive local-charge sum,
multiplicative local-carrier product, injectivity of `deckChar`, and the charge/divisibility
criterion. No theorem combined them into the exact aggregate-cancellation classification.

## Proof

Use `xiDescent_circle_localGlobalDeckCharge` for one exact finite census. Rewrite its sum of local
charges as `wCharge` of total enclosed order. `wCharge_eq_zero_iff` classifies additive vanishing.
For the multiplicative face, replace the product by `deckChar` of loop charge and use
`deckChar_injective` against `deckChar_zero`.

No numerical computation is used.

## Novelty status

Post-proof searches recovered the classical argument principle and generic Kummer/monodromy
language: winding counts total enclosed multiplicity, and an `n`-th-root obstruction is controlled
by the resulting residue class. No searched source stated the exact `xiDescent` specialization with
one unconditional finite census and the simultaneous equivalence between additive loop-charge
vanishing, cancellation of the product of every enclosed local `carrierCharge`, and dyadic
divisibility of total enclosed order. Novelty claim is restricted to that formal connector.

## Lean result

`formal/GaloisForLFunctions/RHTower/XiDescentCircleAggregateCancellationUniversalityLaw.lean`
proves `xiDescent_circle_aggregateCancellation`.

Exact check passed without warnings:

`lake env lean GaloisForLFunctions/RHTower/XiDescentCircleAggregateCancellationUniversalityLaw.lean`

## Log

- 2026-07-23 — theorem generated from existing circle census and charge-character theorems; card
  opened in progress.
- 2026-07-23 — exact Lean check passed; post-proof novelty search found generic argument-principle
  support but no exact Xi-descent aggregate-cancellation package.
