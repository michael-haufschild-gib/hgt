# Boundary-wedge uniform HT dimension gap — formalization certificate

- **ID:** `boundary-wedge-uniform-ht-dimension-gap`
- **Stage:** 3-formalized
- **Paper proof:**
  `other/boundary-wedge-uniform-ht-dimension-gap.md`
- **Umbrella:** `formal/GaloisForLFunctions/HTGeometry.lean`
- **Status:** `[UNCONDITIONAL LEAN]`

## Formalized theorem

For every wedge of two simplex boundaries with block parameters `r,s ≥ 2`, the same finite facet
system has:

- minimal periodic-pencil dimension `2`;
- minimal entire HT-realization dimension `2`;
- minimal faithful facet-separation dimension `4`.

Thus its intrinsic and periodic-pencil dimensions agree, while faithful separation has an exact
factor-two gap.

## Source modules and capstones

```text
formal/GaloisForLFunctions/HTGeometry/PPMatrixRankFormulaConsequences.lean
formal/GaloisForLFunctions/HTGeometry/WedgeFacetLowerBound.lean
formal/GaloisForLFunctions/HTGeometry/BoundaryWedgeExponentialRealization.lean
formal/GaloisForLFunctions/HTGeometry/BoundaryWedgeUniformHTDimensionGap.lean

boundaryWedge_ppDim_eq_two
boundaryWedgeHTRealizable_two_uncond
boundaryWedge_htDim_eq_two
faithfulSeparation_fin_four_and_minimal
boundaryWedge_uniformHTDimensionGap
```

## Verification and boundary

All source modules are registered in the `HTGeometry` umbrella.  Direct
`lake env lean GaloisForLFunctions/HTGeometry/BoundaryWedgeUniformHTDimensionGap.lean` and targeted
`lake build GaloisForLFunctions.HTGeometry.BoundaryWedgeUniformHTDimensionGap` pass.  Scratch
`#print axioms` checks for all four dimension capstones and the combined theorem report only
`propext`, `Classical.choice`, and `Quot.sound`.

The certificate covers the exact dimension law of the card.  It does not claim the separately
identified strengthening in which every entire carrier must itself be hypertranscendental; that
strengthening does not affect any of the three dimension values formalized here.
