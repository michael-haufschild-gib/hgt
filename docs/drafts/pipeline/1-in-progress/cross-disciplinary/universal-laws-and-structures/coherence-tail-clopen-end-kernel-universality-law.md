# Coherence-tail/clopen-end kernel universality law

## Status

In progress — paper proof and Lean formalization complete; literature novelty audit pending.

## Theorem-first provenance

- `HTGeometry/CoherenceTailQuotient.lean`
  - `coherenceTailMap_eq_allPositive_iff_negativeDomain_finiteBoundary`
  - `coherenceTailMap_injective_iff_finiteBoundaryOneEnded`
- `HTGeometry/CoherenceEndClopen.lean`
  - `finiteBoundaryEndClopen_eq_iff_symmDiff_finite`
  - `finiteBoundaryEndClopen_empty`
  - `finiteBoundaryEndClopen_univ`
  - `finiteBoundaryBooleanRingQuotientEquivClopens`

The first terminal module computes the finite-defect coherence kernel through finite edge boundary.
The second terminal module identifies finite-boundary vertex sets modulo finite changes with clopen
sectors of conventional graph-end space.

## Universal law

For an infinite locally finite connected graph, fix a Boolean orientation whose negative domain
has finite edge boundary. Its projective tail class maps to the all-positive edge-coherence class.
That invisible class is nevertheless nontrivial exactly when its negative domain determines a
clopen end sector different from both the empty and full sectors. Thus proper nonempty clopen ends
are precisely the surviving geometry inside the nontrivial coherence kernel.

## Lean status

Formalized in
`formal/GaloisForLFunctions/HTGeometry/CoherenceTailClopenEndKernelUniversalityLaw.lean`.

Exact check:

```text
lake env lean GaloisForLFunctions/HTGeometry/CoherenceTailClopenEndKernelUniversalityLaw.lean
```

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only.
