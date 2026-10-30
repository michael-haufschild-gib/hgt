# Formalization of the finite and quantitative frontier

- **ID:** review-3010-work-items
- **Stage:** 1-in-progress
- **Source:** `docs/reports/review-3010/obstacles-summary.md`, §2.1
- **Scope:** Complete A1–A15 at their stated ranges. Existing theorems require source and dependency audits; existence of a receiver does not discharge its analytic inputs.

| Item | Required conclusion | Current evidence |
|---|---|---|
| A1 | Pole-row estimate and joint top-band cancellation | Both named theorems proved in `SuccessorShellArithmetic/TheShellsAndThePoleCancelOnTheTopBand`; direct Lean check and capstone axiom audit passed; umbrella wired |
| A2 | Growing Euler heads have arbitrarily large negative dimension | `eventually_eulerHead_negative_family` and its log-power corollary passed direct Lean and transitive axiom audits; umbrella wired |
| A3 | Effective conductor confinement for finite sieve profiles at fixed overlap | `exists_sieveProfile_ramanujan_approximation` and exponential defect cutoff exist; scope audit pending |
| A4 | Effective positivity/index horizons; full-index exhaustion for Steklov schedule | Full-index Steklov exhaustion formalized in `TheSteklovScheduleReachesTheIndex`, direct Lean and axiom audits passed; effective horizons remain unfinished |
| A5 | First-prime, coarse, polar and head payments on finite Haar cells/sources | Several separate payments exist; joint scope audit pending |
| A6 | Matched finite-sieve Hodge index | Existing formalized card and theorem; audit pending |
| A7 | Further finite theta Hankel ranks as square-plus-flux domination | Unfinished |
| A8 | Exact graded implications from heat-count growth to deep-zero density | Stretched-exponential and subpower rungs formalized in `RHTower/Heat/TheHeatCountGrowthLadder`; direct Lean and axiom audits passed, including existing polynomial rung |
| A9 | Further finite log2/log3-grid and Jensen degrees | Unfinished |
| A10 | Further fixed-radius floors, odd witnesses and effective collar shifts | Unfinished |
| A11 | Exact overlap thresholds for further finite flip families | Every nonempty finite prime set covered; explicit tilted-spline specialization added; direct Lean and transitive axiom audits passed |
| A12 | Native two-response action on source data without zero-copy indexing | Existing native action still uses `XiZeroCopy` |
| A13 | Elliptic base over F₃: product formula, quotient measures, Iwasawa characters, unfolding | Principal ideal norms, local integrals and finite approximation proved; global product formula, quotient covolume and arithmetic unfolding remain open |
| A14 | Actual Ξ-divisor identity `(σ−1/2)S=Re(ξ′/ξ)+D` | Shared-corpus `TheXiResolventDepthIdentity` now proves full-divisor identity for `σ>1`, absolute convergence and nonnegative depth; source reviewed, existing card records direct Lean and axiom audits |
| A15 | Growing-modulus shell transfer; general scalar jets; terminal/Euler completion | Unfinished |

## Heat-count ladder

At heat time `t=δ²/(C log⁴ X)`, the proved persistence estimate gives
`#F≤C log X N(t)` for every finite multiplicity-exact deep-zero window.
An envelope `N(t)≤exp(A t^(−α))` gives `#F≤C log X exp(K(log X)^(4α))`.
For `α<1/4`, this is at most `X^ε` eventually, for every `ε>0`.
These implications are formalized; no actual small-time growth envelope is assumed true.

Input: `exists_card_deep_le_mul_nonrealZeroCount`. The bounded-count equivalence and
`polylog_deep_density_of_polynomial_nonrealZeroCount` already exist.

## Steklov index target

For every `β>2`, the atomic Gram matrices of `steklovDCProfile` at width
`superGevreyRatio β N / N` have negative indices converging in `ℕ∞`
to `HeckeKreinToeplitz.negIndex zetaKernel`.
`TheExplicitSchedulesReachTheIndex` supplies finite spline families, Gram convergence,
the atomic index upper bound and residue-class assembly.
`SuperGevreyCriticalGrowth` supplies `exists_dcLogSynthesis` and the explicit schedule's
`OverlapGrowthSuperGevrey` law. Its mollification and synthesis-error proofs already
give the required logarithmic derivative class. The full-index transport is now
formalized in `TheSteklovScheduleReachesTheIndex`.

## Gates

- [x] Full task scope preserved.
- [ ] Every item has its exact Lean theorem and paper argument.
- [ ] Named leaf checks, transitive axiom audits and umbrella imports complete.
