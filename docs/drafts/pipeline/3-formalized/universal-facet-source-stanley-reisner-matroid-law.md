# Universal facet-source Stanley–Reisner matroid law

- **ID:** universal-facet-source-stanley-reisner-matroid-law
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** whole-corpus closure of `UniversalFacetSourcePhase` and `LocalizedStanleyReisnerMatroidRank`
- **Statement:** Every universal facet source represents the complete localized Stanley–Reisner differential matroid, hence every subset rank and circuit, not merely independence of the whole output family.

## Goal

Promote source-phase universality from one full-family independence proposition to equality of the
entire represented matroid.

## Gates

- [x] 0 → 1  in-progress: exact missing matroid conclusion identified from Lean statements
- [x] 1 → 2  fully-proven: dependency-closed restriction-and-application proof
- [x] 2 → 3  formalized: exact Lean theorems for matroid equality, rank, circuits, and subset independence
- [ ] 3 → 4  publication-ready: novelty and exposition audit pending

## Approach

Membership in `UniversalFacetSource` gives differential independence over `RatFunc ℂ` of the full
universal orbit palette.  Compose with the finite facet-orbit index map; its injectivity preserves
independence.  Restrict constants to `ℂ`, obtaining independence of the exact coordinate source used
by the localized Laurent rows.  Apply
`differentialFamilyMatroid_stanleyReisnerLaurentRows_eq`.  Equality of extended ranks on every index
set follows by congruence.

## Audit

- **[CORPUS]:** `UniversalFacetSource.stanleyReisnerLaurentDifferentialMatroid` proves only whole-family independence iff quotient-row independence
- **[CORPUS]:** `differentialFamilyMatroid_stanleyReisnerLaurentRows_eq` supplies the unconsumed complete matroid conclusion
- **Hostile verdict:** `SURVIVES PRELIMINARY ATTACK`; subset dependence, circuits, and ranks are absent from the source theorem
- **Status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED]`

## Log

- 2026-07-22 — cross-module theorem closure found and paper proof completed

## Unconditional Lean formalization

`formal/GaloisForLFunctions/HTGeometry/UniversalFacetSourceStanleyReisnerMatroidLaw.lean`

- `UniversalFacetSource.stanleyReisnerLaurentDifferentialFamilyMatroid_eq` — the represented
  differential matroid of the localized Stanley--Reisner outputs of a universal facet source is
  the Stanley--Reisner quotient-class matroid itself.
- `UniversalFacetSource.stanleyReisnerLaurentDifferentialFamilyMatroid_eRk` — equal extended rank
  on every index set.
- `UniversalFacetSource.stanleyReisnerLaurentDifferentialFamilyMatroid_isCircuit_iff` — equal
  circuits.
- `UniversalFacetSource.stanleyReisnerLaurentDifferentialFamilyMatroid_indep_iff` — independence of
  every selected subfamily is exactly linear independence of the corresponding quotient classes.

The route is the one in the Approach: `UniversalFacetSource.differentialIndependent` composed with
the injective finite facet-orbit index map, constants restricted from `RatFunc ℂ` to `ℂ` by
`differentialIndependent_upperEnd_restrictComplex`, then
`differentialFamilyMatroid_stanleyReisnerLaurentRows_eq`.

Axiom audit: `propext, Classical.choice, Quot.sound`.
