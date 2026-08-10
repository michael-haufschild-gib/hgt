# Conservative repair, viability--coercivity transmutation, and open-history law

- **ID:** ULF-ALM-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean-certified)
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveViabilityCoercivityTransmutation`
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/conservative-repair-viability-coercivity-transmutation-and-open-history-law.md`

## Certified mechanism

Lean proves the general conservative-repair range law and exact zero-history criterion. It then
certifies the canonical two-resource transmutation cell:

1. old and repaired semantic boundaries remain surjective;
2. repaired kernel is exactly the born lineage line `((t,t),t)`;
3. feasible kernel is its nonnegative ray;
4. unit normalization selects the unique carrier `(1/3,1/3,1/3)`;
5. every coordinate is load-bearing;
6. old rules admit strict scalar progress, while repaired support admits none;
7. repeated carrier histories have zero semantic boundary and unbounded positive execution size;
8. unit execution cost cannot descend to a potential of semantic endpoints.

Capstone declaration:
`viabilityCoercivityTransmutationMechanism_unconditional`.

## Audit

- direct foreground elaboration: passed;
- leaf build: passed, 8,655 jobs;
- `UniversalLawField` umbrella build: passed, 11,586 jobs;
- axiom print: `propext`, `Classical.choice`, `Quot.sound` only;
- no `sorry`, `admit`, new `axiom`, `opaque`, `unsafe`, or computational decision procedure.

Full formal lint reached the module and reported only an unrelated umbrella-reachability failure for
`GaloisForLFunctions.HTGeometry.AffineFunctionSystemEnvelope`.

## Meaning

This closes the third Autopoietic Law Mechanics laboratory. One conservative repair preserves
semantic reach but simultaneously creates viable cyclic lineage, destroys strict scalar progress,
and generates an endogenous next challenge through repeatable positive-cost histories. It certifies
a route-independent regime-change mechanism, not autocatalysis, repair selection, a universal
field representation, or RH.
