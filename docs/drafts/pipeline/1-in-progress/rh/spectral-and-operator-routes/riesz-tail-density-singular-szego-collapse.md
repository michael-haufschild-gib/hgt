# Riesz tail density forces singular Szegő collapse

- **ID:** `riesz-tail-density-singular-szego-collapse`
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) / classical bridge
- **Scientific status:** `[BRIDGE] [FORMALIZATION]`
- **Parent:** `cofinal-cholesky-carrier-selection-threshold-law.md`
- **Statement:** For a finite infinite-support circle measure singular to Haar measure, the exact
  Riesz-brothers density conclusion alone forces the consecutive Toeplitz determinant ratios to
  tend to zero; hence the pure-singular carrier trichotomy needs no separate Szegő hypothesis.

## Goal

Remove the redundant `HasSzegoFirstLimitConclusion` input from the singular-carrier capstone.  The
constraint is density of the analytic monomial span.  Multiplication by the circle coordinate is
unitary, so it sends that dense span to the dense positive-frequency tail.  Approximating the
constant function by the tail makes the reversed monic extremum tend to zero, and the already
proved determinant-ratio identity transfers this to the Toeplitz tower.

This is a parent-theory bridge, not candidate new scientific knowledge.  Its value is to reduce
the paper's formal literature boundary from two circle theorems to the exact F. and M. Riesz leaf.

## Gates

- [x] 0 → 1 in-progress: exact redundant hypothesis identified and source-pure attack fixed
- [ ] 1 → 2 fully-proven: complete proof that analytic-span density forces zero Gram infimum
- [ ] 2 → 3 formalized: theorem with only `HasRieszBrothersDensityConclusion`, module build and
  axiom audit pass
- [ ] 3 → 4 publication-ready: carrier paper dependency statement updated without overclaiming

## Approach

1. Bundle multiplication by the circle coordinate as a surjective linear isometry.
2. Prove the span of strictly positive analytic monomials is dense whenever the full analytic
   monomial span is dense.
3. Approximate the constant monomial by a finite positive-frequency polynomial.
4. Shift that approximation to a competitor for the degree-`N` Gram--Schmidt extremum and force
   the infimum of squared norms to zero.
5. Use the existing monotone determinant-ratio limit and the Riesz-brothers completeness theorem.

## Log

- 2026-07-14 — created after the live dependency audit exposed the separate Szegő input as
  potentially redundant in the purely singular application.
