# Boundary-wedge representation-dimension gap universality law

## Status

Fully proven on paper; Lean 4 formalization exact-checks.

## Theorem-first source

- `boundaryWedge_ppDim_eq_two`: every nondegenerate boundary wedge has exact periodic-pencil
  dimension `2`.
- `faithfulSeparation_fin_four_and_minimal`: the same two-block boundary-wedge incidence geometry
  admits faithful facet separation in dimension `4`, and no lower dimension works.

Both source theorems use the boundary-wedge vertex carrier `Option (Fin r ⊕ Fin s)` and the same
left/right boundary-facet incidence pattern. Corpus research found no theorem comparing their two
optimal representation dimensions.

## Universal law

For every `r,s ≥ 2`, let `p` be periodic-pencil dimension of the two-boundary wedge. Then `p = 2`,
faithful facet separation exists in dimension `2p`, and every faithful separation has dimension at
least `2p`. Thus the two realization models have an exact universal factor-two dimension gap.

## Paper proof

The periodic-pencil rank theorem gives `p = 2`. The faithful-separation construction and
obstruction theorem give existence at dimension `4` and lower bound `4 ≤ d` for every faithful
realization. Substituting `p = 2` identifies `4 = 2p`. No numerical computation is used.

## Lean formalization

Module:
`GaloisForLFunctions.HTGeometry.BoundaryWedgeRepresentationDimensionGapUniversalityLaw`.

Exact command:
`lake env lean GaloisForLFunctions/HTGeometry/BoundaryWedgeRepresentationDimensionGapUniversalityLaw.lean`.

## Novelty audit

Pending literature audit after theorem-generation exhaustion. Corpus audit is negative.
