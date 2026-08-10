# Three-stage downstream-kernel obstruction filtration and exact-tower law — formalized

- **ID:** ULF-DKO-1
- **Stage:** 3-formalized
- **Paper:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/three-stage-downstream-kernel-obstruction-filtration-and-exact-tower-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveObstructionFiltration`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-CERTIFIED] [AXIOM-AUDITED] [UMBRELLA-BUILT]

## Certified declarations

| paper clause | Lean declaration |
|---|---|
| two quotient transitions and their composite | `tripleCarrierFirstTransition`, `tripleCarrierSecondTransition`, `tripleCarrierTotalTransition` |
| nested survival filtrations | `tripleCarrierFirstFiltration`, `tripleCarrierSecondFiltration`, `tripleCarrierFirstFiltration_le_second` |
| canonical filtration inclusion | `tripleCarrierFiltrationInclusion`, `tripleCarrierFiltrationInclusion_injective` |
| restricted middle-layer map | `tripleCarrierMiddleLayerMap`, `tripleCarrierMiddleLayerMap_surjective` |
| middle-layer exactness | `range_tripleCarrierFiltrationInclusion_eq_ker_middleLayer` |
| first and second downstream-kernel layer identifications | `tripleCarrierFirstLayer_identification`, `tripleCarrierSecondLayer_identification` |
| explicit first, middle, and outer graded isomorphisms | `tripleCarrierFirstLayerEquiv`, `tripleCarrierMiddleGradedEquiv`, `tripleCarrierOuterGradedEquiv` |
| total transition surjectivity | `tripleCarrierTotalTransition_surjective` |
| short exact filtration step | `tripleCarrierFiltration_short_exact` |
| unconditional capstone | `threeStageDownstreamKernelMechanism_closed` |

## Verification

Foreground direct elaboration passed:

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveObstructionFiltration.lean
```

Source-level axiom audit of the nested-filtration theorem, surjectivity, middle exactness,
short-exactness, and capstone reports only `propext`, `Classical.choice`, and `Quot.sound`. The
module contains no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, or computation-backed proof.

Global lint remains blocked by unrelated shared-worktree debt already recorded under ULF-CHM-1.
Final foreground umbrella audit passed:

```text
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Build completed successfully with `11,547` jobs; both the new module and umbrella built cleanly.
