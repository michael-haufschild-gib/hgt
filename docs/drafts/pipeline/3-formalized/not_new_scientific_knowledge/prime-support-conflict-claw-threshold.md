# Prime-support conflict claws require a three-label center

- **ID:** `prime-support-conflict-claw-threshold`
- **Stage:** 3-formalized
- **Type:** `THEOREM (Lean) / [NO-GO] [POSITIVE TWO-PORT RESIDUE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeWordClawFreeConflictNoGo.lean`
- **Consumer:** `../../1-in-progress/prime-word-claw-free-hardcore-rh.md`

## Theorem

Join two finite prime supports when they intersect.  If one center support intersects three leaf
supports and the leaves are pairwise disjoint, choose one center--leaf intersection label from
each leaf.  Pairwise disjointness makes the three chosen labels distinct.  Therefore

```text
induced support-conflict claw centered at C  ->  3 <= |C|.
```

The bound is sharp.  The center `{0,1,2}` and singleton leaves `{0}`, `{1}`, `{2}` induce a claw.
Thus the unrestricted prime-support intersection graph is not claw-free.

## Positive residue

Every support of cardinality at most two has a claw-free conflict neighborhood: it cannot intersect
three pairwise disjoint leaves.  This identifies the exact finite two-port regime in which raw
support conflict retains the claw-free property.

For two-element packets this regime tends toward a line-graph/matching model, so a strict successor
to the failed Wick/matching route must preserve the two-port neighborhood law while adding
completion-dependent clique junctions that are not merely line-graph edges.

## Formal certificate

The module proves:

- `supportConflict_claw_forces_three_le_card`;
- `not_isSupportConflictClaw_of_card_le_two`;
- `primeWordSupportConflict_explicit_claw`;
- `primeWordSupportConflict_no_claw_of_center_card_le_two`.

The exact module build is green.  Axiom audits report only `propext`, `Classical.choice`, and
`Quot.sound`.

## Gates

- [x] abstract three-witness cardinality theorem proved
- [x] sharp three-label prime-word claw proved
- [x] positive two-port no-claw theorem proved
- [x] exact Lean build
- [x] accepted-axiom audit

