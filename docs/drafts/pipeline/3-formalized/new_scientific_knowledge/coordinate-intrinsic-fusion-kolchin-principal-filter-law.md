# Coordinate-intrinsic fusion--Kolchin principal-filter law — formalization certificate

- **ID:** `coordinate-intrinsic-fusion-kolchin-principal-filter-law`
- **Stage:** 3-formalized
- **Paper proof:**
  `../../2-fully-proven/new_scientific_knowledge/other/coordinate-intrinsic-fusion-kolchin-principal-filter-law.md`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/PrimeValuationCoordinateFusionCompletion.lean`
- **Umbrella:** `formal/GaloisForLFunctions/HTGeometry.lean`
- **Status:** `[UNCONDITIONAL LEAN] [NOT RH]`

## Formalized theorem

Over the embedded coordinate field, Lean proves finite-rectangle and all-layer differential
independence, exact next-layer relative HT and strict frontier growth, construction and
derivation-closure of the canonical fusion completion, the principal-filter classification, and
the pairwise-coprime actual-prime specialization with the totient rank law.

## Capstones

```text
cofiniteTailDenseOn_primeResidueValuationUpperEndCarrier_differentialIndependent_over_coordinate
cofiniteTailDenseOn_primeResidueValuationUpperEndAllLayerCarrier_differentialIndependent_over_coordinate
cofiniteTailDenseOn_primeResidueValuationUpperEndNextLayer_relativeHT_over_coordinate
cofiniteTailDenseOn_primeResidueValuationUpperEndCoordinateDepthPrefixField_strictMono
primeResidueValuationUpperEndCoordinateFusionCompletion_principalFilter_iff
pairwiseCoprimePrimeResidueValuationUpperEndCoordinateFusionCompletionLaw
```

## Verification and boundary

Serialized direct checks and the `HTGeometry` umbrella build pass.  Combined scratch
`#print axioms` audits use only `propext`, `Classical.choice`, and `Quot.sound`.  This is the exact
coordinate-relative fusion-completion classification.  It constrains finite differential-rational
Euler closures but supplies no global zero-selecting mechanism or RH conclusion.
