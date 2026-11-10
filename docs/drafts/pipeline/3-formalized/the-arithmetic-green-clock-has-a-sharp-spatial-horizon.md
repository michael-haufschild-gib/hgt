# The arithmetic Green clock has a sharp spatial horizon

- **ID:** the-arithmetic-green-clock-has-a-sharp-spatial-horizon
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** B133; arithmetic-clock Green realization.
- **Statement:** The cumulative prime Green capacity satisfies
  `cumulativeCapacity(N+1)/√N→4`. For
  `r_N=√(1−exp(−κ√N))`, the clock covers the complete prime horizon through
  `N` eventually when `κ>4`, and fails to cover it when `0<κ<4`.
  Above the threshold, every smooth packet supported in
  `[-log(N)/2,log(N)/2]` has signed Weil error at most
  `exp(−κ√N)∫(f')²/2`.

## Goal

Replace fixed-support convergence by a sharp law for the spatial reach of
the arithmetic Green construction. The threshold concerns completion of
the prime horizon; it makes no positivity assertion about Weil's form.

## Proof

For every prime `p`, set `s=√p`. Since `s≥4/3`,

`0≤2log(p)/(s−1)−2log(p)/s=2log(p)/(s(s−1))≤8log(p)/p`.

Mertens' upper bound therefore gives, for `N≥1`,

`0≤C_{N+1}−2Σ_{p≤N}log(p)/√p≤8(log N+log4)`.

The weighted prime-number theorem gives `Σ_{p≤N}log(p)/√p ∼2√N`.
Dividing the preceding bound by `√N` proves `C_{N+1}/√N→4`.

For `κ≥0`, the explicitly defined damping satisfies `0≤r_N<1` and
`1−r_N²=exp(−κ√N)`. The self-energy bounds give

`κ√N+4−π²/24+geometricScalar ≤ arithmeticClock(r_N)`

`arithmeticClock(r_N) ≤ κ√N+4+geometricScalar`.

Thus its ratio to `√N` tends to `κ`. Strict comparison of the limits proves
eventual full capacity for `κ>4` and insufficient capacity for `0<κ<4`.
In the latter case some prime `p≤N` has weight below one: otherwise summing
its fully filled capacities would give `C_{N+1}=arithmeticClock(r_N)`, a
contradiction. The clock is eventually positive because its normalized
limit is positive.

For `N≥1`, `lagRange(log N/2)=N+1`. Above the threshold, the established
common-support prime cancellation and Sobolev error theorem give

`0≤weilQuad(f)−coupledGreenEnergy(r_N,f)≤exp(−κ√N)H(f)/2`

simultaneously for all smooth compact packets supported in
`[-log N/2,log N/2]`, where `H(f)=∫(f')²`.
More generally, if `H(f)≤M exp(η√N)` with `η<κ`, their errors are at most
`M exp(−(κ−η)√N)/2→0`, uniformly over this expanding family.

## Boundary

The equality case `κ=4` is not decided. Below-threshold failure means an
unsaturated prime horizon; it does not assert failure of convergence for
every individual packet. No full Weil positivity or Green kernel on the
refuted glued adelic carrier is inferred.

## Inputs and verification

Corpus inputs: `RHTower.tendsto_primeRpowLogSumLE` in
`RouteESaddlePntTransport.lean`, `Sieve.mertensFirst_upper`, the existing
clock, self-energy bounds, and uniform Green error theorem.
Both modules passed plain `lake --old env lean` checks and are imported by
the `HyperbolicArakelovTheory` umbrella. All six printed axiom audits give
only `[propext, Classical.choice, Quot.sound]`.

In namespace `GaloisForLFunctions.HyperbolicArakelovTheory.PrimeSuspension`:

- `ThePrimeGreenCapacityHasSquareRootGrowth.lean`:
  `cumulativeCapacity_excess_bounds`, `tendsto_cumulativeCapacity_div_sqrt`.
- `TheArithmeticGreenClockHasASharpSpatialHorizon.lean`:
  `tendsto_spatialClock_div_sqrt`, `eventually_spatialClock_covers_capacity`,
  `eventually_spatialDamping_has_unfilled_prime`,
  `eventually_growingWindow_Green_error`, `growingWindow_Green_uniform`.
