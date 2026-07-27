# Differential-clock strict conservative universality law

## Status

Fully proven on paper; formalized in Lean 4.

## Theorem-first source

- `differentialAlgHom_comp_preserves_derivation`: differential embeddings close under composition.
- `jetObservableFieldEmbeddingEquiv_comp`: finite clock-frame equivalences compose strictly.
- `jetObservableField_map_algHom_eq_iff_resolution_eq`: a differential embedding preserves and
  reflects the numerical resolution of a hypertranscendental clock slice.

Corpus search found no theorem applying resolution rigidity to a composite chain or joining that
conservativity with strict frame composition.

## Universal law

Every two-step derivation-preserving field-embedding chain transports a hypertranscendental finite
clock strictly and conservatively: the induced frame is literal composition, and a transported
resolution-`P` source field equals a resolution-`Q` target field exactly when `P = Q`.

## Paper proof

Composition of the algebra embeddings preserves derivation by the composition theorem.  Apply
single-embedding resolution rigidity to this composite and the hypertranscendental source: field
equality is equivalent to `P = Q`.  Independently, strict frame composition identifies the finite
slice equivalence of the composite with the transitive composite of the two slice equivalences.
The two conclusions share the same composite embedding and resolution and therefore give the
strict conservative law.

## Lean formalization

- Module:
  `GaloisForLFunctions.HTGeometry.DifferentialClockStrictConservativeUniversalityLaw`
- Theorems:
  `jetObservableField_comp_map_eq_iff_resolution_eq`,
  `differentialClockEmbeddingChain_strictConservative`
- Exact check:
  `lake env lean GaloisForLFunctions/HTGeometry/DifferentialClockStrictConservativeUniversalityLaw.lean`
  passed on 2026-07-22.

## Novelty audit

Pending literature audit after theorem-generation phase.  Corpus audit is negative.
