# Bipolar invariant envelope, ordered repair, and determinization -- Lean certification

- **ID:** ULF-RLR-2
- **Paper card:**
  `2-fully-proven/universal-law-field/relational-law-renormalization-mechanics/bipolar-invariant-envelope-ordered-repair-and-determinization-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveBipolarObserverRepair`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-PROVED] [AXIOM-AUDITED] [ROUTE-INDEPENDENT] [NOT RH]

## Certified surface

Lean defines finite law words and the greatest law-invariant relation inside a supplied observer:

- `UnaryLawWordRun`, `UnaryLawWordAdmitted`, `UnaryLawInterior`;
- `unaryLawInterior_equivalence`, `_subset`, `_preserves`, `_greatest`, `_fixed_iff`;
- `unaryLawClosure_interior_absorb` and `unaryLawInterior_closure_absorb`;
- `bipolarRepair_exchange_iff`;
- `bipolarRepairInterior_eq_equality` and `bipolarRepairClosure_eq_universal`;
- `bipolarRepair_observedLaw_not_rightUnique`; and
- unconditional capstone `bipolarObserverRepair_unconditional`.

The generic theorem imports the already-certified least invariant coarsening from
`ConstitutiveUnaryLawRepair` and the effective relational semantics from
`ConstitutiveRelationalLawRenormalization`.  No route, analytic hypothesis, target theorem, or RH
definition appears.

## Exact theorem

For every set, unary law family, and observer equivalence, the least invariant coarsening and
greatest invariant refinement absorb in opposite order.  Their schedules agree iff the original
observer is already law-invariant.  The unconditional three-state cell proves the fine repair is
equality, the coarse repair is the universal relation, and the unrepaired observed law is not
right-unique.

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveBipolarObserverRepair.lean`: pass,
  no warnings;
- leaf build: 2,999 jobs, pass;
- axiom prints on generic extremality, both absorptions, exchange, both cell endpoints,
  nondeterminism, and capstone: only `propext` and `Quot.sound`;
- final `HTGeometry.UniversalLawField` umbrella build: 11,578 jobs, pass;
- full-tree lint reaches the owned module but is presently blocked by two unrelated concurrently
  unwired modules; the exact external failures are recorded on the paper card.

## Scope

This certifies set-level deterministic repair mechanics.  It does not select fine versus coarse
repair and contains no topology, positive admission, recursive law genesis, route handoff, or RH
claim.
