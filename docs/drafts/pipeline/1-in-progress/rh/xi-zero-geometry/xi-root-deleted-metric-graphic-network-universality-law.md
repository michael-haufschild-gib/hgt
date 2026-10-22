# Xi root-deleted metric/graphic-network universality law

## Status

Fully proven on paper; Lean 4 formalization pending dependency build.

## Theorem-first source

- `xiTransversePrimeJetApertureGram_cofinite_posDef_iff_injective_ne_zero`: cofinite strict
  positivity exactly detects nonzero, collision-free integral shift packets.
- `xiTransverseShiftPairDifferenceUpperEndCarrier_differentialMatroid_eq_rootedIncidenceMatroid`:
  corrected shift differences realize the rooted incidence matroid over the coordinate base.
- `xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_differentialMatroid_eq_rootedIncidenceMatroid`:
  the same realization holds after adjoining every scalar valuation layer.
- `xiTransverseShiftPairDifferenceUpperEndCarrier_differentialMatroid_base_eq_allValuation`:
  the complete edge-packet matroid is base-invariant.

The shared shift map is literal. Deleting the distinguished zero-shift root makes the vertex Gram
strictly positive precisely when all remaining vertices are separated from the root and one
another.

## Universal law

For every finite rooted shift network with root shift zero, cofinite strict positivity of the
prime-jet aperture metric on nonroot vertices forces the whole shift map to be injective. Every
corrected directed edge packet then has exactly the rooted incidence matroid over both coefficient
bases, and adjoining all scalar valuations preserves the complete differential matroid.

## Paper proof

The cofinite Gram classification gives injectivity and nonvanishing on the nonroot subtype.
Nonvanishing separates each vertex from the zero root; subtype injectivity separates all nonroot
pairs, proving global injectivity. Apply the two rooted-incidence realization theorems and the
valuation-base invariance theorem. No numerical computation is used.

## Lean formalization

Module: `GaloisForLFunctions.RHTower.XiRootDeletedMetricGraphicNetworkUniversalityLaw`.

Exact audit is deferred because imported pairwise-rank modules currently lack compiled `.olean`
artifacts; final audit will build the precise module dependency before rerunning `lake env lean`.

## Novelty audit

Pending literature audit after exact Lean formalization. Corpus audit is negative.
