# Universal facet-source countable point-finite constraint universality law

## Status

In progress — paper proof and Lean source complete; exact check and literature novelty audit pending.

## Theorem-first provenance

- `HTGeometry/CountablePointFiniteConstraintCarrier.lean`
  - `universalFacetOrbit_finsuppDifferentialMatroid`
  - `universalFacetOrbit_countablePointFiniteConstraintDifferentialMatroid`
  - `linearIndependent_pointFiniteFacetRow_iff`
- `HTGeometry/UniversalFacetSourceStanleyReisnerMatroidLaw.lean`
  - `UniversalFacetSource.stanleyReisnerLaurentDifferentialFamilyMatroid_eq`
- `HTGeometry/UniversalFacetSourcePhase.lean`
  - `UniversalFacetSource.differentialIndependent`

## Universal law

Every point `u` of the universal facet-source phase—not only the fixed canonical gauge—realizes
the exact nonlinear differential relation packet of every finite structural family on every
nonempty countable point-finite facet geometry. Explicitly, differential independence of the
finite source outputs is equivalent to linear independence of their classes in the corresponding
possibly infinite Stanley–Reisner quotient.

The law therefore makes the countable carrier construction phase-invariant: source and
orientation choice cannot change any finite constraint relation supported by a countable
point-finite geometry.

## Paper proof

Restrict a finite `Finsupp` row family to its common finite support. Embed that countable support
into the universal facet-orbit palette. Differential independence of an arbitrary
`UniversalFacetSource` survives the injective restriction; scalar restriction from `RatFunc ℂ` to
`ℂ` preserves it. The differential-operator row theorem identifies output independence with row
independence. Finally, the point-finite facet observation theorem identifies those rows with the
corresponding Stanley–Reisner quotient classes.

## Lean status

Source complete in
`formal/GaloisForLFunctions/HTGeometry/UniversalFacetSourceCountablePointFiniteConstraintUniversalityLaw.lean`.

Direct source check is deferred to final audit because the cached `UniversalFacetSourcePhase`
artifact predates its `differentialIndependent` theorem; no early `lake build` was run.

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only; corpus search found
phase-wide finite facet matroids and one-source countable point-finite completeness separately,
but no phase-wide countable point-finite constraint theorem.
