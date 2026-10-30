# Formalization of the finite and quantitative frontier

- **ID:** review-3010-work-items
- **Stage:** 1-in-progress
- **Source:** `docs/reports/review-3010/obstacles-summary.md`, §2.1
- **Scope:** Complete A1–A15 at their stated ranges. Existing theorems require source and dependency audits; existence of a receiver does not discharge its analytic inputs.

| Item | Required conclusion | Current evidence |
|---|---|---|
| A1 | Pole-row estimate and joint top-band cancellation | Both named theorems exist in `SuccessorShellArithmetic/TheShellsAndThePoleCancelOnTheTopBand`; audit pending |
| A2 | Growing Euler heads have arbitrarily large negative dimension | Named theorem exists in `ArithmeticIndexDescent/TheIndexOfAGrowingEulerHeadIsUnbounded`; audit pending |
| A3 | Effective conductor confinement for finite sieve profiles at fixed overlap | `exists_sieveProfile_ramanujan_approximation` and exponential defect cutoff exist; scope audit pending |
| A4 | Effective positivity/index horizons; full-index exhaustion for Steklov schedule | Unfinished |
| A5 | First-prime, coarse, polar and head payments on finite Haar cells/sources | Several separate payments exist; joint scope audit pending |
| A6 | Matched finite-sieve Hodge index | Existing formalized card and theorem; audit pending |
| A7 | Further finite theta Hankel ranks as square-plus-flux domination | Unfinished |
| A8 | Exact graded implications from heat-count growth to deep-zero density | Persistence/counting theorem available; implications unfinished |
| A9 | Further finite log2/log3-grid and Jensen degrees | Unfinished |
| A10 | Further fixed-radius floors, odd witnesses and effective collar shifts | Unfinished |
| A11 | Exact overlap thresholds for further finite flip families | Unfinished |
| A12 | Native two-response action on source data without zero-copy indexing | Existing native action still uses `XiZeroCopy` |
| A13 | Elliptic base over F₃: product formula, quotient measures, Iwasawa characters, unfolding | Unfinished |
| A14 | Actual Ξ-divisor identity `(σ−1/2)S=Re(ξ′/ξ)+D` | Finite identity and actual real reciprocal field available; infinite transport unfinished |
| A15 | Growing-modulus shell transfer; general scalar jets; terminal/Euler completion | Unfinished |

## Current mathematical target

For every regular `s` with `Re s>1/2`, transport line-reflection symmetrization to the
multiplicity-exact Ξ divisor. Prove summability before splitting infinite sums. Identify the
explicit term with the actual real logarithmic derivative, and prove that the nonnegative
depth defect vanishes exactly under RH.

Inputs: `pair_depth_resolvent`, `sub_inv_re_eq`,
`re_logDeriv_xi_eq_realReciprocal_tsum`, and the existing inverse-square divisor sums.

## Gates

- [x] Full task scope preserved.
- [ ] Every item has its exact Lean theorem and paper argument.
- [ ] Named leaf checks, transitive axiom audits and umbrella imports complete.
