# Faithful-facet minimum-dimension universality law

## Status

Fully proven on paper; formalized in Lean 4; **verification gate passed**.

`lake build` succeeds on the module inside the `GaloisForLFunctions.HTGeometry` umbrella (which imports it), and `#print axioms` gives exactly `propext, Classical.choice, Quot.sound` for

```text
GaloisForLFunctions.exists_faithfulFacetMinDimensionSeparation
```


## Theorem-first source

- `exists_faithfulFacetSeparation`: a covered finite vertex set has a faithful separation in
  facet-coordinate dimension `m`.
- `exists_faithfulFacetSeparation_vertexDim`: every finite facet family has a faithful separation
  in vertex-coordinate dimension `|V|`.

Both constructions provide rationally independent vertex vectors, exact facet-complement zero
patterns, and rationally independent nonzero values on each facet.  The corpus docstring announced
the resulting minimum bound but contained no theorem realizing it in one common target space.

## Universal law

Every finite vertex set covered by `m` facets admits a faithful facet separation in the canonical
complex coordinate space of dimension `min(m, |V|)`.  All three fidelity conditions survive:
global rational independence, exact zero-pattern recovery, and facetwise rational independence.

## Paper proof

If `m ≤ |V|`, use the facet-coordinate construction and coordinate projections as facet forms.
If `|V| < m`, use the vertex-coordinate construction and reindex its ambient function space along
the canonical equivalence `V ≃ Fin |V|`.  Transport vertex vectors through this linear equivalence
and precompose each facet form with its inverse.  Injectivity preserves rational linear
independence; inverse cancellation preserves every evaluation, hence both the zero patterns and
facetwise value independence.  In each case the target dimension reduces definitionally to the
minimum.

## Lean formalization

- Module: `GaloisForLFunctions.HTGeometry.FaithfulFacetMinDimensionUniversalityLaw`
- Certificate: `GaloisForLFunctions.FaithfulFacetMinDimensionSeparation`
- Theorem: `GaloisForLFunctions.exists_faithfulFacetMinDimensionSeparation`
- Exact check:
  `lake env lean GaloisForLFunctions/HTGeometry/FaithfulFacetMinDimensionUniversalityLaw.lean`
  passed on 2026-07-22.

## Novelty audit

Pending literature audit after theorem-generation phase. Corpus audit is negative.
