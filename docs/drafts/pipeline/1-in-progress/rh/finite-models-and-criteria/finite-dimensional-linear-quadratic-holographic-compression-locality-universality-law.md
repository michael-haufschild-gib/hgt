# Finite-dimensional linear–quadratic holographic compression–locality universality law

- **ID:** finite-dimensional-linear-quadratic-holographic-compression-locality-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated transport closure of finite-dimensional coordinate-free linear
  holography, quadratic principal-symbol completion, and detector compression/locality
- **Statement:** Every finite-dimensional scalar law admits coordinate-free linear- and
  quadratic-width holographic completions with one exact dependence horizon and maximal exterior
  symbols; from four law directions onward the linear detector is strictly smaller, yet every
  bounded-valence coordinate membrane for either completion obeys the same pair-covering bound.

## Goal

Remove the remaining coordinate asymmetry. Existing finite-dimensional theorem transports only
the linear completion to an arbitrary law space. Existing linear/quadratic comparison lives only
on `Fin n → K`. Transporting the quadratic completion through the same finite basis should make
the comparison invariant and connect it to both membrane locality laws.

## Gates

- [x] 0 → 1 in-progress: full read of the finite-dimensional/locality terminal component
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check
- [x] 3 → 4 novelty audit: post-proof literature search found no collision

## Corpus inputs

- `finiteDimensionalLinearHolographicCompletion_fieldHorizon_and_maximalPrincipalSymbol`
- `quadraticWidthPrincipalSymbolCompletion_pow`
- `quadraticWidthPrincipalSymbolCompletion_endomorphismCommutatorMap_injective`
- `principalSymbolDetectorCompression_localityUniversality`
- `finiteDimensionalLawCoordinates`

## Proof

**[PROVED HERE]** Let `e : V ≃ₗ[K] (Fin n → K)` be a linear coordinate equivalence. Compose the
original pencil with `e.symm`, apply the quadratic-width completion, and compose the result with
`e`. Its `d`-th power at `v` is the scalar law at `e.symm(e v)=v`; this follows from the quadratic
scalar-preservation theorem. The exterior commutator map is injective because the coordinate
quadratic map is injective and the exterior power of an injective linear equivalence is
injective. The generic dependence-horizon theorem then gives the exact zero locus and maximal
exterior symbol for the transported quadratic completion.

Choose the canonical finite-dimensional basis for `e`. The existing linear theorem and the new
quadratic transport each identify their dependence locus with `{v | F v = 0}`, hence their
horizons coincide on `V`. Instantiate the coordinate linear/quadratic detector comparison with
the transported pencil and scalar law. It supplies strict linear-width compression when
`4 ≤ finrank K V`, pair completeness for both membrane presentations, and the same
`choose(finrank V,2)` bounded-valence covering lower bound. All clauses use one coordinate
equivalence and one original scalar pencil. ∎

## Strict gain over corpus endpoints

No corpus endpoint defines a coordinate-free quadratic holographic completion or compares both
detector scales directly on an arbitrary finite-dimensional law space. The result makes detector
compression basis-invariant while proving that membrane pair-covering cost survives that
compression.

## Lean formalization

- Transport:
  `coordinateFreeQuadraticWidthPrincipalSymbolCompletion`
- Transport laws:
  `coordinateFreeQuadraticWidthPrincipalSymbolCompletion_pow`,
  `coordinateFreeQuadraticWidthPrincipalSymbolCompletion_endomorphismCommutatorMap_injective`,
  and
  `coordinateFreeQuadraticWidthPrincipalSymbolCompletion_fieldHorizon_and_maximalPrincipalSymbol`
- Finite-dimensional realization:
  `finiteDimensionalQuadraticHolographicCompletion`
- Main theorem:
  `finiteDimensionalLinearQuadraticHolographicCompletion_compressionLocalityUniversality`
- Module:
  `GaloisForLFunctions.HTGeometry.FiniteDimensionalLinearQuadraticHolographicCompressionLocalityUniversalityLaw`
- Verification:
  `lake env lean GaloisForLFunctions/HTGeometry/FiniteDimensionalLinearQuadraticHolographicCompressionLocalityUniversalityLaw.lean`
  passed without warnings.
- Umbrella:
  imported by `GaloisForLFunctions/HTGeometry.lean`.

## Novelty audit

Post-proof arXiv searches found nearby holographic quantum-code compression/locality tradeoffs,
bilocal reconstruction, and finite-dimensional twisted-commutator results. No source states the
coordinate-free linear/quadratic scalar-law completion with identical algebraic-dependence
horizon, injective exterior derivation symbols, strict detector-width separation, and invariant
pair-covering membrane cost. Novelty remains a negative-search conclusion, not a claim of
bibliographic completeness.

## Log

- 2026-07-23 — finite-dimensional linear, quadratic locality, and compression modules read in
  full.
- 2026-07-23 — dependency-closed transport and common-law proof completed before Lean source or
  literature search.
- 2026-07-23 — exact-file Lean verification passed; module wired into the HTGeometry umbrella.
- 2026-07-23 — post-proof literature audit found no exact or equivalent transport/compression
  law.
