# Finite clock counting: source cancellation and endpoint test

Owner: critical-clock product task. RH route remains open.

## Verified corpus facts

- `MobiusDivisorQuadraticCompletionSPEWeld` already closes uniform quadratic
  completion → original bounded Abel action → RH. Another conditional endpoint
  theorem supplies no missing mathematics.
- `FixedCoreSquarefreeDensity.fixedCoreSquarefreeCount_insert` is an exact
  finite prime-exclusion recurrence. Its density limit quantifies a fixed core.
- `MobiusDivisorFixedCorePrimeCorrelation` already cancels copied diagonals
  in the unweighted finite counting measure. Its signed correlation is not
  bounded cumulatively.
- `MobiusDivisorArityCharge` already has an analogous weighted finite balance;
  its zero weight on the empty retained label prevents head control.
- `MobiusDivisorDilationMeanUniformCoreNoGo` excludes a bound uniform after
  each separate prime insertion. It does not exclude cumulative cancellation.

## Closed finite source results

Module: `formal/GaloisForLFunctions/RHTower/MobiusDivisorFiniteClockCountingCancellation.lean`.
All seven public statements passed `lake env lean` in scratch. Axiom audits
report only `propext`, `Classical.choice`, and `Quot.sound`.

Named final audit passed:
`lake build GaloisForLFunctions.RHTower.MobiusDivisorFiniteClockCountingCancellation`.
The module is imported by the RH umbrella. Index refresh passed. Global lint
still reports the four pre-existing unrelated unreachable modules:
`ThetaCuspHawkingBMLiteralCyclicPeierlsLowerWeylRadialDetector`,
`ThetaCuspHawkingBMLiteralCyclicPeierlsSelfInverseSquarePhysical`,
`ThetaCuspHawkingBMLiteralCyclicPeierlsSelfMixedCuspFlux`, and
`XiHeatCassiniWoldJointDepthMöbiusSourceTransport`.
No umbrella or full build was run. Owned Lean processes exited; scratch Lean
files were removed. Audit logs use `/tmp/hgt-finite-clock-counting-*`.

Put `F_P(M,r) = mobiusDivisorInterpolatedFibre M r P ∅`, and
`W_c(P,M) = Σ_{r squarefree, r≤M, (r,P)=1} (c+log r) r F_P(M,r)^2`.
The triangular clock age `log M - log(M/r)` is exactly `log r`.

- At complete processing, `W_c = c E_full`. Thus `c=0` loses the entire
  endpoint, while `c=1` retains it. This is a boundary test of the proposed
  finite-count counterpart, not a disproof of the continuous pairing route.
- For a fresh prime, finite source splitting and the exact clipped merger give
  `W_c(P+p,M)-W_c(P,M)+2 sqrt(p) Σ (c+log r) r F_P(M,r) F_P(M,pr)
   = -p log(p) Σ r F_P(M,pr)^2`.
  Both sums use the actual new-core indices through M. No density limit enters.
- Since `log r≥0` on those indices, `E(P,M)≤W_1(P,M)` uniformly in both
  arguments. This is not a comparison to the previous density-weighted
  continuous pairing.
- The clock identification itself is checked: `W_c/M²` is the finite sum
  of `(c+T-t_r) g_P(t_r)^2/r`, with `T=log M`, `t_r=log(M/r)`, and
  `g_P` the original critically normalized head. At complete positive
  integer walls, `W_1/M²` is exactly that original head squared.

## Route consequence

The original cumulative signed-correlation bound and uniform comparison to
the continuous profile remain unproved. Exact finite cancellation can remove
the density approximation from a local identity, but cannot infer the needed
upper action bound from that identity: the remaining mixed sum has no proved
lower bound. The offset also changes the initial budget; do not claim a
uniform quadratic cap without proving it.

For changing cutoffs, the missing bound must also pay
`W_1(P_k,M_(k+1))/M_(k+1)^2 - W_1(P_k,M_k)/M_k^2`.
Dropping that source-growth term, reversing the sign of the mixed sum, or
identifying this actual counting measure with fixed-core density would leave
an unproved premise. The next substantive target is a source-specific lower
bound for the cumulative mixed terms plus their copied-square payments minus
these cutoff-growth terms along an exhaustive order.

The subsequent audited `MobiusDivisorFiniteClockCutoffGrowth` sharpens this
target: at every fixed finite prime core, `W_1/M²` diverges at least
logarithmically. For any prescribed core sequence, strictly increasing
cutoffs beyond its primes can force arbitrary prescribed action heights.
Consequently a payment lower bound covering arbitrary cutoff schedules is
false. A deliberately coupled exhaustive schedule remains open. Exact source
formula, proof names, and quantifier boundary are recorded in
`rh-finite-clock-growth-boundary.md`.

## Search coverage

Four deep corpus searches completed without a partial flag. Count search
found the exact recurrence; method search returned squarefree reindexing and
log-moment methods, not the missing cumulative bound. Compiler metadata is
mostly source-only; Lean validation is still necessary.

A broad arXiv renewal search returned older papers despite requesting 2026.
The abstract of [Caravenna–Doney](https://arxiv.org/abs/1612.07635) (revised 2019) concerns
random-walk renewal hypotheses. No theorem from it is used here.
