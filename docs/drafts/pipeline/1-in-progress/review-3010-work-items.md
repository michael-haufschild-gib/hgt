# Formalization of the finite and quantitative frontier

- **ID:** review-3010-work-items
- **Stage:** 1-in-progress
- **Source:** `docs/reports/review-3010/obstacles-summary.md`, §2.1
- **Scope:** Complete A1–A15 at their stated ranges. Existing theorems require source and dependency audits; existence of a receiver does not discharge its analytic inputs.

| Item | Required conclusion | Current evidence |
|---|---|---|
| A1 | Pole-row estimate and joint top-band cancellation | Both named theorems proved in `SuccessorShellArithmetic/TheShellsAndThePoleCancelOnTheTopBand`; direct Lean check and capstone axiom audit passed; umbrella wired |
| A2 | Growing Euler heads have arbitrarily large negative dimension | `eventually_eulerHead_negative_family` and its log-power corollary passed direct Lean and transitive axiom audits; umbrella wired |
| A3 | Effective conductor confinement for finite sieve profiles at fixed overlap | Explicit sieve horizon/conductor cutoffs and complete negative-packet cutoff `exp(D(Cc^16+1))` at `N≥Hc^8` passed direct Lean and axiom audits; umbrellas wired |
| A4 | Effective positivity/index horizons; full-index exhaustion for Steklov schedule | Full-index Steklov exhaustion, coordinate mass `≥1/18` at `N≥Q⁴`, and explicit positivity horizons for all `c>0` passed direct Lean and axiom audits. Constructed finite-family Euler–Maclaurin and exact Steklov index certificates at every integer horizon also passed; umbrellas wired |
| A5 | First-prime, coarse, polar and head payments on finite Haar cells/sources | Full-Weil negative dimension bound `R+A` at fixed coarse cutoff `R`, and joint finite first-prime/nonfirst/full-polar reserve with dimension bound `A+1`, passed direct Lean and transitive axiom audits; umbrella wired |
| A6 | Matched finite-sieve Hodge index | Source and dependency chain reviewed; existing named leaf check and axiom audit recorded in `matched-prime-form-hodge-index-uniform-in-the-sieve.md`. One horizon works for every sieve; umbrella wired |
| A7 | Further finite theta Hankel ranks as square-plus-flux domination | `CompletedArithmeticForms/SeamCoercivity` proves every rank on an explicit seam interval and beyond `2*nativeMixedHorizon N`. Ranks nine and ten still require the intervening compact interval |
| A8 | Exact graded implications from heat-count growth to deep-zero density | Stretched-exponential and subpower rungs formalized in `RHTower/Heat/TheHeatCountGrowthLadder`; direct Lean and axiom audits passed, including existing polynomial rung |
| A9 | Further finite log2/log3-grid and Jensen degrees | Every fixed Jensen degree is eventually real-rooted; direct Lean and transitive axiom audits passed, umbrella wired. Grid extension remains |
| A10 | Further fixed-radius floors, odd witnesses and effective collar shifts | Formalized and audited: closed shift thresholds; odd zeta/Liouville witnesses for every `r>27/50`, with margins `1/25` and `−3/10`; explicit aperture `a₊>181/500` retaining full real and complex Weil floor `1/8000` |
| A11 | Exact overlap thresholds for further finite flip families | Every nonempty finite prime set covered; explicit tilted-spline specialization added; direct Lean and transitive axiom audits passed |
| A12 | Native two-response action on source data without zero-copy indexing | Raw source-data action, exact theta-data pullback, absolute admission, contact and exhaustion limit passed direct Lean and transitive axiom audits. No analytic proof fields |
| A13 | Elliptic base over F₃: product formula, quotient measures, Iwasawa characters, unfolding | Actual completed-place product formula, closed-point count, unordered analytic Euler product on `|u|<1/3`, completed pole reduction, unique additive gap representatives and quotient Haar probability with covolume one passed direct Lean and transitive axiom audits; umbrella wired. Valued rank-one and loop Iwasawa existence, the exact rank-one torus valuation, and continuous idele spectral characters trivial on diagonal units also passed. Unipotent quotient, loop Iwasawa characters and arithmetic unfolding remain open |
| A14 | Actual Ξ-divisor identity `(σ−1/2)S=Re(ξ′/ξ)+D` | Shared-corpus `TheXiResolventDepthIdentity` now proves full-divisor identity for `σ>1`, absolute convergence and nonnegative depth; source reviewed, existing card records direct Lean and axiom audits |
| A15 | Growing-modulus shell transfer; general scalar jets; terminal/Euler completion | Logarithmic-conductor shell transfer, arbitrary-prime support-size scalar recovery, and explicit Euler-completion schedules passed direct Lean and transitive axiom audits; umbrellas wired. All-order Euler/scalar transfer and multiplicity-to-jet vanishing also passed direct Lean and axiom audits; umbrella wired. Same-order scalar/mixed-jet converse needs a separate homogeneous-logarithm argument |

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
