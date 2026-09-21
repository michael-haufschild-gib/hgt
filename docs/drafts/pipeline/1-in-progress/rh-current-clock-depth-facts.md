# Current-clock repayment depth

- **Route:** cumulative signed payment → bounded critical action → RH.
- **Status:** paper argument; Lean verification pending. No exhaustive construction.
- **Source question:** can unrestricted numbers of helper primes near the current cutoff pay a fixed inherited prime debt?

## Paper facts to verify in Lean

Write `W(P,M)` for `mobiusDivisorFiniteClockEnergy 1 M P` and
`C(P) = (3/5) * 2^(P.card-1)` (natural subtraction).

If every helper prime `q ∈ S` satisfies `M/q ≤ K`, then processing `S`
preserves every old sample with `K < r` and no helper dividing `r`:
`M/r+1 ≤ q` makes both clipped child endpoints inactive. All discarded old
samples lie in the union of `[1,K]` and `q*[1,K]` over primes `q ≤ M`.
Their number is at most `K*(1+π(M))`. Nonnegative new sample squares give

`W(P,M) - W(P∪S,M) ≤ C(P)^2 * M * (1+log M) * K*(1+π(M))`.

This is uniform in the helper set, its size, and the changing threshold `K`.
It retains the actual finite arithmetic counting measure and clipped endpoint.
Its positive survivor is the preserved-source lower bound, not a monotonicity
assumption on the newly merged receiving squares.

For a fixed nonempty even prime core, actual prime-correlation orientation
provides arbitrarily distant omitted primes `r` with positive complete
coefficient debt `κ(P∪{r})-κ(P)`. Since
`W(P,M)/(M²*(1+log M)) → κ(P)`, any same-clock net repayment after inserting
such `r` must have `K*(1+π(M)) ≥ η*M` for some `η>0`.
Consequently fixed quotient windows cannot repay this debt. A moving window
must reach depth comparable to `M/(1+π(M))`, which PNT makes logarithmic.

The same obstruction persists when the repayment cutoff advances arbitrarily
from `M` to `L ≥ M`: normalized clock debt is at least `δ*(1+log L)` once
`M` crosses one fixed threshold. The lower coefficient of the inserted core
exceeds the upper coefficient of the starting core; positivity and
`log M ≤ log L` retain the gap. Thus advancing the clock does not evade the
required helper depth at `L`.

## Method audit

- Classification: derived source-preservation boundary, not a proposed new
  universal law or substitute for the schedule conjecture.
- The quotient restriction is used in exactly two places: child inactivity
  for retained samples and counting cofactors of discarded samples.
- The invariant is the old sampled field outside the explicitly counted set;
  arbitrary newly merged fields are retained as nonnegative squares.
- No prime order or auxiliary preparation budget enters the invariant.
- The risky source-level consequence is a fresh helper with quotient at least
  a positive multiple of the current logarithmic clock, even with arbitrary
  helper cardinality and arbitrary forward cutoff growth.

## Whole-route consequence

The existing bounded-quotient stream and two-coordinate repairs cannot alone
pay arbitrary inherited debt at the current clock. Required producer must
control deeper actual child sources and their cross terms, while completing
all primes below each original action cutoff. The argument does not exclude
such a producer or RH.

## Rejected shortcuts

- Successor-envelope repair bounds a prepared envelope; it does not pay its
  difference from the starting state's energy.
- Eventual insertion release after auxiliary preparation omits the preparation
  cost and chooses the current-cutoff threshold afterward.
- A small terminal head is insufficient for complete monotone processing;
  the corpus already proves this obstruction in
  `MobiusDivisorWeightedTerminalHeadBarrier`.
