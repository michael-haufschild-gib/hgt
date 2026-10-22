# Explicit digit-local temporal-support capstone

- **ID:** `explicit-digit-local-temporal-capstone`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Date:** 2026-08-17
- **Statement:** Every finite Hermitian local interaction family on (n) (m)-level sites, equipped with base-(m) digit onsite energies and a positive switch-on weight, obeys the observer temporal-support law with its canonical weighted Steiner number, with no spectral-separation or geometric-lower-bound premise.

## Goal

Close the two avoidable hypotheses in the local observer theorem: construct a separating onsite
spectrum and instantiate the sharp geometric lower bound rather than asking the reader for either.

## Gates

- [x] 0 → 1: exact target and corpus dependencies identified
- [ ] 1 → 2: complete paper proof
- [ ] 2 → 3: Lean theorem `digitOnsiteLocalHermitianObserverTemporalSupportLaw`
- [ ] 3 → 4: publication integration

## Approach

Use `digitOnsite n m`; base-(m) uniqueness makes the product onsite energy injective. Use
`observerWeightedSteinerNumber` and its unconditional lower-bound theorem. Apply
`localHermitianObserverTemporalSupportLaw`. Locality is carried by the explicit
`FiniteLocalInteractionFamily` datum and Hermiticity remains the sole physical structural input.

## Log

- 2026-08-17 — created in Stage 1 after corpus search.

