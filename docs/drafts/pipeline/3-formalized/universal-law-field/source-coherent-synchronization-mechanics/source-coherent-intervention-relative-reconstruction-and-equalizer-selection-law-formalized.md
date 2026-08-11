# Source-coherent intervention relative reconstruction — formalized

- **ID:** ULF-SCSM-1-FORMAL
- **Stage:** 3-formalized
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/source-coherent-synchronization-mechanics/source-coherent-intervention-relative-reconstruction-and-equalizer-selection-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.SourceCoherentInterventionSynchronization`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified content

Lean proves without `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declarations:

1. invariance of relative response under one global diagonal intervention;
2. exact relative-response cocycle composition;
3. reconstruction from one anchor plus relative responses;
4. equality of complete relative packets iff packets differ by one global intervention;
5. vanishing response iff the packet is globally diagonal;
6. source response differences are difference representations;
7. synchronization is membership in the intersection of response-difference kernels;
8. a trivial synchronization kernel selects zero displacement;
9. one capstone theorem combines reconstruction, cocycle coherence, and selection.

The module imports the previously certified quotient--fusion and four-organ conservation kernel, so
source synchronization and information genesis share one formal dependency chain.

## Audit commands

```text
cd formal
lake env lean GaloisForLFunctions/HTGeometry/SourceCoherentInterventionSynchronization.lean
lake build GaloisForLFunctions.HTGeometry.SourceCoherentInterventionSynchronization
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Axiom and repository lint audits are recorded in the universal-law-field Lean certification ledger.
