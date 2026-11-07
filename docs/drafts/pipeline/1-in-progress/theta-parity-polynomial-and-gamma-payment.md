# Theta parity-polynomial and Gamma payment

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** TH; `ThetaCuspSections/TheEleventhSectionFromHeightSixtySeven`, `EverySectionFromItsVerifiedHeight`; `CompletedArithmeticForms/WeightedSuccessorReserve`.
- **Goal:** Extend unconditional full-source finite-rank positivity and identify an aggregate compensation inequality valid at every rank.

## Established boundary

Rank eleven is positive for `0<a≤1/2`. Its polynomial splits into an even quintic and odd quartic in `b²`. Current is nonnegative through `|b|≤66`, bounded below by `0.0006a` on `|b|≤5`, and bounded in absolute value by `3.6·10⁷a exp(-7|b|/5)`. The general verified-height transfer requires `41+6(N+2)log(N+2)`; arbitrary-height verification is not available.

Native tails have positive Gamma/Hermite reserves at every rank beyond explicit rank-dependent horizons. Fixed diagonal repairs, a fixed finite-head Gaussian margin, and a fixed successor/diagonal fraction cannot close every rank.

## Conjectures

1. General parity-polynomial estimates retain enough positive current mass to extend the unconditional rank range. Rank twelve needs two quintics; the odd block carries an additional `b²` weight.
2. Keeping the natural weighted polynomial energy and sharper current decay improves payment beyond the existing scalar tail bounds.
3. Rank-dependent allocation of exact Gamma reserves pays the complete signed center contribution, including every unequal theta pair and the infinite remainder. No compact payment inequality is assumed.

## Required conclusions

- Concrete unconditional source bounds and rank positivity, not a receiver with an unpaid verification premise.
- Every completed paper theorem followed by its exact Lean formalization and transitive axiom audit.
- New leaves in `ThetaCuspSections/` or `CompletedArithmeticForms/`; individual foreground Lean checks only.

## Active payment

The squared parabolic core `(a/300)(1-b²/36)²` on `[-6,6]` has a dependency-closed paper proof; exact Lean formalization is in progress. Multiplying a degree-eleven polynomial by `1-b²/36` reduces rank-twelve payment to a degree-thirteen Legendre exterior estimate. The existing height-67 verification and current tail remain unchanged.
