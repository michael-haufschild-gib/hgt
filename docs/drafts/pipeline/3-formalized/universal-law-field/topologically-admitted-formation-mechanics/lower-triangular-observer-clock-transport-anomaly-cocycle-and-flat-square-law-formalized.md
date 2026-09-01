# Lower-triangular observer-clock transport, anomaly cocycle, and flat-square law — Lean formalization

- **ID:** ULF-TAFM-21
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / TRIANGULAR REPRESENTATION / EXACT COCYCLE
- **Paper source:** `lower-triangular-observer-clock-transport-anomaly-cocycle-and-flat-square-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ObserverClockTriangularRepresentation`
- **Status:** `[FORMALIZED] [NO SORRY] [NO ADDED AXIOMS] [NOT RH]`

## Certified law

The module proves:

1. Canonical marginal recovery plus anchored interaction reconstructs every joint observable.
2. Marginal recovery vanishes and interaction extraction is identity on the anchored sector.
3. Images of recovery and interaction extraction are exactly the marginal and anchored sectors;
   the two submodules are disjoint and span the full joint-observable space.
4. Both recovery maps are idempotent projections.
5. Pointwise scale-clock multiplication preserves that interaction sector.
6. Every transported observable splits exactly into observed marginal plus lifted interaction.
7. Under marginal recurrence, full lifted closure is equivalent to zero anomaly.
8. The marginal diagonal block composes multiplicatively.
9. The interaction diagonal block composes multiplicatively.
10. The off-diagonal anomaly obeys the exact cocycle
   `H(rate₁*rate₂) = H(rate₁)A(rate₂) + D(rate₁)H(rate₂)`.
11. Commutativity of clock rates forces the corresponding flat-square conservation identity.
12. A constant clock acts by the same scalar on both diagonal sectors and creates zero anomaly.

This upgrades one-step non-descent into a compositional mechanism. Relative to marginal recovery
plus interaction history, every clock change is lower triangular. Pre-existing interaction never
returns to the marginal observer, but marginal data can create new interaction and earlier anomaly
is carried by later interaction transport.

## Verification

- Scratch elaboration passed before tree edit.
- Direct foreground elaboration passed.
- Targeted leaf build passed: `8780/8780` after the exact completion additions.
- Module is imported by `HTGeometry.UniversalLawField`; umbrella was not built.
- Twelve newly added theorem declarations were audited and depend only on `propext`,
  `Classical.choice`, and `Quot.sound`.
- Module contains no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.

## Exact boundary

Flatness constrains anomaly composition but does not bound anomaly magnitude. Remaining RH producer
is a source-specific signed admission theorem placing the literal arithmetic cocycle in a bounded
bilateral interaction chamber. Without that theorem, calling flat-square conservation “the RH
mechanism” would be theatre.
