# Almost every base detects an isolated top

- **Stage:** 2-fully-proven; formalization in progress, not yet a verified contribution.
- **Type:** THEOREM (paper)
- **Obstacles:** B13, B112; detection beyond the exceptional-rank density barrier.
- **Statement:** For an absolutely summable exponential trace with a finite visible isolated top exponent `Theta`, almost every positive sampling base `ell` has `|S(n ell)|>C exp(a n ell)` at every sufficiently large integer level, simultaneously for every `a<Theta` and `C>=0`. For actual zeta AAL failure, `Theta` is the rightmost real part minus `1/2`.
- **RH criterion:** RH is equivalent to zeros approaching the line together with a positive-measure set of positive bases having infinitely many subexponential lag readings at every positive exponent. Constants and subsequences may depend on the base and exponent; no thickness or density condition is imposed on the levels.
- **Novelty boundary:** Bounded gaps and coefficient-dependent lower density hold at every base. Periodic root packets show that eventual detection at every level cannot hold at every base. The exceptional bases retaining infinitely many exponentially small readings form a null set.

## Proof

Merge equal real frequencies and write the normalized top as `P(t)=sum_(j<k) c_j exp(i gamma_j t)`, with distinct `gamma_j` and some `c_j!=0`. Its derivative chain is
`P_m(t)=sum c_j (i gamma_j)^m exp(i gamma_j t)`.
The fixed Vandermonde matrix on `i gamma_j` sends the coefficient vector `c_j exp(i gamma_j t)` to `(P_m(t))_(m<k)`. A row of its inverse recovering a nonzero coefficient gives `eta>0` such that every `t` has some `m<k` with `|P_m(t)|>=eta`. At least one real component then has absolute value at least `eta/2`.

Each `P_m`, `m<k`, has Lipschitz constant `sum |c_j (i gamma_j)^m| |gamma_j|`; their finite sum plus one gives a common positive bound `B`. Choose `r=eta/(8B)`. The chosen real component of `P_m` has absolute value at least `eta/4` throughout `(t-r,t+r)`.

For a real derivative chain whose derivative of order `m>=1` has absolute value at least `A>0` on an interval, each of the two levels `+epsilon,-epsilon` is attained at most `m` times. These cuts partition the sublevel set into at most `2m+1` intervals. The corpus's `interval_length_le` bounds each such interval by
`(m+2) (((m+1)! epsilon)/A)^(1/m)`.
Hence the sublevel measure is at most
`(2m+1)(m+2) (((m+1)! epsilon)/A)^(1/m)`.
For `m=0`, the sublevel set is empty below `A`; above `A` its measure is bounded by the interval length. Taking the maximum of finitely many constants, using `epsilon^(1/m)<=epsilon^(1/k)` for `0<epsilon<=1`, and the interval-length bound for `epsilon>=1`, gives constants `K,r>0` with
`volume{y in (t-r,t+r) : |P(y)|<epsilon} <= K epsilon^(1/k)`
for every center and every positive threshold.

Cover the positive line by `[jr,(j+1)r]`, contained in the radius-`r` interval about `(j+1/2)r`. For any `delta>0`, on this cell `exp(-delta t)<=exp(-delta jr)`. Apply the preceding bound with twice this threshold to include equality. The measures of
`B_delta={t>=0 : |P(t)|<=exp(-delta t)}`
are bounded by a convergent geometric series, so `volume B_delta<infinity`.

The corpus theorem `RHTower.AlmostEverySpacing.ae_eventually_mult_notMem` then gives eventual avoidance of `B_delta` along almost every progression in each dyadic interval of positive bases. Take the countable union of these intervals and the countable intersection over `delta=1/(m+1)`. Monotonicity upgrades this to every `delta>0`: almost every positive base satisfies `|P(n ell)|>exp(-delta n ell)` eventually, simultaneously for all positive `delta`.

For the full trace, absolute summability and the isolated gap give
`|exp(-Theta t)S(t)-P(t)|<=W exp(-(Theta-Theta2)t)` for `t>=0`.
Given `a<Theta`, choose `0<delta<min(Theta-a,Theta-Theta2)`. Exponential domination makes the normalized remainder and `C exp(-(Theta-a)t)` together smaller than `exp(-delta t)` eventually. This proves the full-trace assertion. Failure of actual zeta AAL supplies the finite isolated top; actual lag weights are summable and merged coefficients are nonzero by positive real parts.

If subexponential lag readings recur infinitely often at a positive-measure set of bases, failure of AAL contradicts the almost-everywhere eventual lower bound at the positive rate `(Theta-1/2)/2`. Thus AAL holds. Combining it with zeros approaching the line gives RH. Conversely, RH bounds the lag uniformly at every base, supplying the metric condition on the interval `[1,2]`.

## Corpus audit

- `TheExceptionalRankDecidesTheWindow`, `TopCoefficientWindowDensity`, `IsolatedTopExcursionDensity`: all-base bounded gaps and density, without almost-everywhere eventual detection.
- `KleinbockMargulis/SmoothGoodOne`, `CutInterval`: derivative-chain interval lengths and finite-cut measure bounds.
- `TrigonometricSumWindowMean`: explicit Lipschitz bound for finite complex phase sums.
- `WeilLagAlmostEverySpacingBlind`: finite-measure bad-time transfer by Borel–Cantelli. Its infinite-layer counterexample concerns a one-sided real-part bound and does not contradict this absolute-value statement.
- Existing lag integral and finite-measure excursion criteria control continuous sets of times. The metric criterion here requires only infinitely many readings in each of a positive-measure family of progressions.

## Formalization gate

Formalize absolute sublevel control, uniform finite-jet separation, finite bad-time measure, and actual-zeta metric detection. Count only after direct Lean and transitive-axiom audits.
