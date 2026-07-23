# Prime first-trace closed-relation/rigging universality law

## Status

Formalized in Lean and wired into the RHTower umbrella. Kept in progress until global exhaustion
and final audit complete.

## Lean sources

- `GaloisForLFunctions.RHTower.PrimeFirstTraceExactGraphClosureUniversalityLaw`
- `GaloisForLFunctions.RHTower.ArithmeticSchurExactNormRiggingNoGo`
- `GaloisForLFunctions.RHTower.ArithmeticLogClockBoundedCompletionSaturation`

## Conjecture

The minimal closed linear relation containing the actual-prime first-trace graph has full source
domain and vertical multivalued part equal to the zero-vacuum Hardy hyperplane. Consequently
every closed linear relation extending the graph contains that entire vertical hyperplane and
cannot be single-valued.

This exact multivalued defect persists under every pair of complete source/response riggings that
preserve the arithmetic-Schur source norm and first-trace response norm: such a realization
cannot be sequentially closable.

## Corpus gap

The exact graph-closure module classifies membership in the minimal closed graph. The bounded
completion module proves existence of a nonzero vertical vector, and the rigging module proves
nonclosability under exact norm transport. No theorem turns exact closure into a universal
containment theorem for arbitrary closed relation extensions or joins that obstruction to the
exact-rigging no-go.

## Proof plan

1. Use minimality of topological closure to place the exact graph closure inside any closed
   relation extension.
2. Rewrite exact closure membership to show that every zero-vacuum response occurs vertically.
3. Use the nonzero first Hardy basis vector to contradict single-valuedness.
4. Combine exact pair classification and the closed-relation no-go with the exact-norm rigging
   theorem.

No numerical computation is used.

## Novelty status

Post-proof searches found the standard theory of multivalued closed linear relations, canonical
operator/multivalued decompositions, and the classical criterion that a graph is closable exactly
when its closed vertical fiber is trivial. No searched source identified the actual-prime
first-trace graph, its exact zero-vacuum multivalued hyperplane, or persistence under
arithmetic-Schur exact-norm riggings. Novelty claim is restricted to that exact arithmetic
realization and joint package.

## Lean result

`formal/GaloisForLFunctions/RHTower/PrimeFirstTraceClosedRelationRiggingUniversalityLaw.lean`
proves:

- every closed relation extension contains the full vertical zero-vacuum Hardy hyperplane;
- no closed single-valued relation extension of the first-trace graph exists;
- the joint exact graph-closure, relation-extension, and exact-rigging no-go.

Exact check passed without warnings:

`lake env lean GaloisForLFunctions/RHTower/PrimeFirstTraceClosedRelationRiggingUniversalityLaw.lean`
