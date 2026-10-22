# Single-witness Hamburger maximal-TV continuum-polarization universality law

- **ID:** single-witness-hamburger-maximal-tv-continuum-polarization-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** strict strengthening of LAW413 by the moment-indeterminacy
  maximal-total-variation theorem
- **Statement:** One bounded complex kernel witness for a normalized positive Hamburger moment
  form forces global first/second-kind polarization and a real continuum of moment-identical
  probability measures whose every distinct pair is mutually singular with total-variation
  mass exactly two.

## Goal

LAW413 propagates one bounded-kernel witness globally and obtains an injective Nevanlinna family,
but stops short of the strongest separation theorem already available for the origin kernel.
Use the propagated origin witness to upgrade the family from merely distinct to pairwise
maximally separated.

## Gates

- [x] 0 → 1 in-progress: LAW413 and maximal-total-variation endpoint read in full
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check
- [x] 3 → 4 novelty audit: post-proof literature search found no collision

## Corpus inputs

- `boundedKernel_global`
- `singleWitness_hamburgerContinuumPolarizationUniversality`
- `exists_momentIdentical_pairwiseMaximalTotalVariation_family`

## Proof

**[PROVED HERE]** Global bounded-kernel propagation carries the given witness at `z₀` to the
origin. The maximal-total-variation theorem applied there produces a real-parameter family of
probability measures with the prescribed complete Hamburger moments. Distinct parameters give
mutually singular measures; because both are probabilities, the total variation of their signed
difference has mass exactly two.

LAW413 supplies from the same witness failure of uniqueness and, at every real observation
point, bounded kernel, positive Christoffel limit, first-kind square summability and decay, and
recurrence-weighted second-kind escape. Pair the maximally separated family with those unchanged
global conclusions. ∎

## Strict gain over corpus endpoints

LAW413 only records injectivity of a continuum family. The new theorem proves the sharp metric
separation of every distinct pair while retaining its full continuum polarization payload.
The maximal-total-variation endpoint previously required an origin witness rather than accepting
an arbitrary complex one.

## Lean formalization

- Main theorem:
  `singleWitness_hamburgerMaximalTVContinuumPolarizationUniversality`
- Consolidated module:
  `GaloisForLFunctions.HTGeometry.SingleWitnessHamburgerContinuumPolarizationUniversalityLaw`
- Verification:
  `lake env lean GaloisForLFunctions/HTGeometry/SingleWitnessHamburgerContinuumPolarizationUniversalityLaw.lean`
  passed without warnings.
- Umbrella:
  existing import in `GaloisForLFunctions/HTGeometry.lean`.

## Novelty audit

Post-proof searches checked classical Nevanlinna parametrization, N-extremal measures,
determinate/indeterminate criteria, and first/second-kind orthogonal-polynomial theory. These
sources contain the classical ingredients. No located source states the exact arbitrary-complex-
witness theorem with pairwise maximal total variation together with the complete global
first/second-kind polarization payload. Novelty is therefore only in the integrated universal
statement; it remains a negative-search conclusion, not a claim that its classical components
are new.

## Log

- 2026-07-23 — post-LAW432 scan and connector audit exposed the unconsumed sharp family theorem.
- 2026-07-23 — dependency-closed proof completed before Lean source or literature search.
- 2026-07-23 — theorem consolidated into LAW413 source; exact-file Lean verification passed and
  existing HTGeometry umbrella wiring retained.
- 2026-07-23 — post-proof literature audit found no exact integrated statement.
