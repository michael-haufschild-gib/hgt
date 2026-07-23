# Universal facet-source Stanley–Reisner matroid law

- **ID:** universal-facet-source-stanley-reisner-matroid-law
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** whole-corpus closure of `UniversalFacetSourcePhase` and `LocalizedStanleyReisnerMatroidRank`
- **Statement:** Every universal facet source represents the complete localized Stanley–Reisner differential matroid, hence every subset rank and circuit, not merely independence of the whole output family.

## Goal

Promote source-phase universality from one full-family independence proposition to equality of the
entire represented matroid.

## Gates

- [x] 0 → 1  in-progress: exact missing matroid conclusion identified from Lean statements
- [x] 1 → 2  fully-proven: dependency-closed restriction-and-application proof
- [ ] 2 → 3  formalized: exact Lean theorem and final formal gates pending
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
