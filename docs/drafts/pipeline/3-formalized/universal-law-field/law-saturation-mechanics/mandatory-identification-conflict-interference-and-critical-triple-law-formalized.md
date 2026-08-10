# Mandatory-identification conflict interference and critical-triple law — formalized

- **ID:** ULF-LSM-5
- **Stage:** 3-formalized
- **Type:** ROUTE-INDEPENDENT MECHANISM THEOREM (Lean-certified)
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveIdentificationConflictInterference`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified laws

For finite source and observer types, Lean certifies:

1. an observer respects supplied identifications iff it respects their generated equivalence;
2. every respecting lossless observer forces generated identifications to avoid all TV conflicts;
3. the canonical quotient is lossless iff that compatibility condition holds;
4. a respecting width-`q` observer exists iff the quotient conflict graph is `q`-colorable;
5. any generated conflict forces strict total-variation loss;
6. the same strict law holds when the critical path uses two identification doctrines;
7. in the three-state model, each identification separately has an explicit lossless observer;
8. their join connects the conflict endpoints, so no observer respecting both remains lossless.

No `sorry`, `admit`, added axiom, `opaque`, `unsafe`, or computational proof is used.

## Audit

- direct foreground elaboration: pass;
- project formal lint: pass;
- axiom print: no axioms for the pure equivalence theorem; otherwise only `propext`,
  `Classical.choice`, and `Quot.sound`;
- final foreground Universal Law Field umbrella build: pass, 11,519 jobs.

## Certification boundary

Lean certifies the finite compatibility, strict-loss, quotient-width, and critical-triple laws.
The paper card's minimality discussion and signed-graph interpretation are not separate formal
claims.  No topology, cofinal closure, analytic admission, physical route, or RH selector is
inferred.

## Field meaning

This is the first exact universal-law-field mechanism in which every doctrine pair can be
realizable while the full triple is not.  The obstruction is produced by composition: two harmless
identification closures jointly complete a path across a fidelity-forbidden edge.  The response is
not an invented defect scalar; strict loss occurs in the previously fixed TV reporter.
