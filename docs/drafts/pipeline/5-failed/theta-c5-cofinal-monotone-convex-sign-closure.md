# Theta C5 cofinal monotone-convex sign closure

- **ID:** theta-c5-cofinal-monotone-convex-sign-closure
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** theta-c5-cofinal-functional-absorption
- **Statement:** The corpus signs for the cofinal likelihood factor alone imply the
  nonpositive functional absorption budget in every modular-center first-fibre-rise chamber.

## Goal

This proposed shortcut would have closed the modular-center rise chamber of source C5 from
`L >= 0`, `L' <= 0`, and `L'' > 0`. That chamber feeds source odd-wall positivity, physical
center-mixed rank four, and—only after still-open higher-packet and cofinal no-escape joins—the
universal tilt-flux/Weil positivity endpoint equivalent to RH.

## Gates

- [x] 0 → 1 in-progress: corpus-derived factorization and exact RH chain identified
- [x] 1 → 5 failed: sign-only mechanism killed by exact positive tax
- [x] no-go survivor dependency-closed on paper and formalized in Lean

## Approach

Differentiate the corpus identity

```text
higherTail = firstFiber * L,
L = R * (2 + R),
```

twice, substitute into the fifth-root total-variance budget, and use the corpus likelihood signs.

## No-go closure

- **Exact killing theorem/mechanism:** Lean proves

  ```text
  functionalBudget = likelihoodBaseBudget + convexityTax,
  convexityTax =
    -5*t^2*A_first*A_source*A_tail*F_first*L''.
  ```

  In a first-fibre-rise chamber, `A_first < 0`, while `A_source`, `A_tail`, `F_first`,
  and `L''` are strictly positive. Therefore `convexityTax > 0`. Projective-flux mismatch is
  another nonnegative term. Monotonicity and convexity do not absorb either contribution.
- **Strongest positive survivor:** exact sharp replacement

  ```text
  functionalBudget = driftBudget + slopeSquareTax + convexityTax,
  functionalBudget <= 0
    iff driftBudget <= -(slopeSquareTax + convexityTax).
  ```

  The literal cofinal tail also satisfies

  ```text
  D_tail = D_first*L - F_first*L',
  J_tail = J_first*L + 2*D_first*L' - F_first*L''.
  ```

  Lean also proves `L' < 0` and

  ```text
  slopeSquareTax = -4*t^2*A_first*A_tail*F_first^2*(L')^2 > 0.
  ```

- **New insight:** Infinite-tail regularity is not open, and likelihood convexity is not a helpful
  sign. Remaining C5 core is a strict negative-reserve theorem for the base budget. Any surviving
  proof must exploit quantitative covariance/cumulant cancellation from the theta likelihood
  hierarchy, not generic monotone-likelihood-ratio orientation.
- **Status:** Dependency-closed Lean theorems in
  `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureLikelihoodTax`, especially
  `thetaCuspCompletedProductFiberCofinalLikelihoodConvexityTaxAtZero_pos` and
  `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureLikelihoodSlopeTax`, especially
  `thetaCuspCompletedProductFiberCofinalLikelihoodSlopeSquareTaxAtZero_pos` and
  `thetaCuspCompletedProductFiberCofinalFunctionalBudget_nonpos_iff_drift_le_neg_twoTaxes`.
  Parent cofinal functional-absorption conjecture remains open.

## Log

- 2026-08-29 — Retired sign-only subroute after exact Lean product-jet and convexity-tax
  decomposition. Positive survivor formalized; no computation used.
