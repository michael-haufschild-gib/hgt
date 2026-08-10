# Nested-observer two-level maximal-coupling law — formalized

- **ID:** ULF-FKT-HMCF-1-CORE
- **Stage:** 3-formalized
- **Type:** ROUTE-INDEPENDENT MECHANISM THEOREM (Lean-certified)
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveHierarchicalMaximalCoupling`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified laws

For finite nonnegative profiles with equal total mass and composable deterministic observers
`X -> K -> L`, Lean certifies:

1. every coupling's agreement at either observer is bounded by the corresponding overlap capacity;
2. within-block product plans remove exactly the available overlap and leave one-sided residuals;
3. a second plan couples residuals inside coarse blocks without recreating fine agreement;
4. the final residual product plan completes both marginals without adding fine or coarse agreement;
5. one explicit coupling therefore saturates both observer capacities simultaneously.

No `sorry`, `admit`, added axiom, `opaque`, `unsafe`, or computational proof is used.

## Audit

- direct foreground elaboration: pass, no warnings;
- `scripts/formal_tools.py lint`: pass;
- axiom print on the capacity bound and simultaneous-maximality capstone:
  `[propext, Classical.choice, Quot.sound]`;
- final foreground umbrella build: pass, 11,514 jobs.

## Certification boundary

This module certifies two nested levels, the first nontrivial hierarchy.  The paper theorem for an
arbitrary finite chain, the full collision-stratum decomposition, and the incomparable-partition
countermodel remain Lean-pending and do not count as certified.

## Field meaning

Positive higher interaction lives in a compatible witness face, not an alternating scalar Möbius
coefficient.  Nested observer exits permit one witness to be extremal at multiple resolutions.
That is a mechanism law, not an RH route theorem.
