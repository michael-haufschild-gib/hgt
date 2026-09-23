# Growing-depth current-clock payment

Owner: critical-clock product task. Full RH construction remains open.

## Frozen target

Construct current-clock payments including prescribed omitted primes, with
quantitative growing child depth, full weighted energy and cutoff control,
and an exhaustive continuation. Do not replace this target by finite-field
sign cancellation or an assumed schedule.

## Proved local producer [BRIDGE]

Module: `MobiusDivisorGrowingDepthCurrentPayment`.

For the literal initial core, Lean proves payment for every prescribed prime q satisfying
`A*(1+log M) <= q` and `16*q <= M`, uniformly after a clock threshold chosen
before q. Insert q at the current clock, then use the actual shallow helper
batch to repay its complete cost. Retain a quadratic reserve on the original
fourth-root cutoff interval. An actual prime in
`A*(1+log M) < q < 2*A*(1+log M)` is produced at every sufficiently large
clock. Its child depth is at least `M/(2*A*(1+log M))-1`; that lower bound
is proved to tend to infinity. This is not payment for every fixed omitted
prime at all later clocks. Helper child quotients remain `2,7,14`.

Public producers:

- `eventually_exists_mobiusDivisorGrowingDepthOmittedPrimePayment` chooses
  `b,R,delta,A`, then a clock threshold, then accepts every prime in the
  stated range. No assumed payment, correlation sign, or energy bound.
  The actual helper list excludes q, is fresh and has no duplicates.
  Every prefix is controlled at every integer cutoff in the fourth-root
  interval. The terminal inequality retains the whole old receiving pair
  and an additional `delta*M^2` reserve.
- `eventually_exists_mobiusDivisorLogarithmicPrime_paid_extension` constructs
  q and its full extension Q, with `W(Q,L)+delta*M^2 <= W(P,M)` on the same
  interval. These choices are independent at distinct clocks.
- `tendsto_mobiusDivisorLogarithmicChildDepth` certifies divergence of the
  explicit lower bound; no unbounded-depth premise is assumed.

## Source facts / whole-route implications

- Existing finite-depth source cancellation does not give a quantitative
  dependence of its constants on depth. Increasing the projection alone does
  not pay the additional coordinates.
- Existing prescribed-pair reserve chooses its eventual cutoff threshold after
  the prime pair. It does not directly give continuation at an earlier clock.
- Exact weighted insertion retains a negative logarithmic copied square.
  Only residual cofactors at most M/q contribute to its mixed term.
- Each clipped literal source fibre satisfies
  `sqrt(r)*abs(H_P(M/r)) <= D(P)*sqrt M`, with
  `D(P)=(3/5)*2^(card(P)-1)`. The exact square-root interpolation identity
  proves this also at nonintegral child cutoffs.
- `mobiusDivisorFiniteClockEnergy_insert_cost_le` proves the complete
  weighted insertion cost is at most `2*D(P)^2*M^2*(1+log M)/q`.
- The current-clock batch produces a core-uniform quadratic reserve under
  its explicit admission conditions. A prescribed prime above 15 and below
  M/16 preserves its shallow source profiles and stays outside its pool.

## Dependency-closed paper proof

1. Keep the exact weighted insertion identity. Its logarithmic copied-square
   term is nonpositive. The mixed term vanishes outside `r <= M/q`.
2. The two clipped source amplitude bounds control each remaining weighted
   mixed term by `2*D(P)^2*M*(1+log M)`. There are at most M/q such terms.
3. Set `E=(3/5)*2^(card(P)+1)` and `A=16+8*E^2/delta0`, where delta0 is
   the existing current-clock batch reserve. The q lower bound makes the
   complete insertion cost at most `delta0*M^2/4`.
4. Inserting q preserves the shallow source profile and leaves the whole
   helper pool fresh: `M/q >= 16`, whereas pool quotients are 2,7,14.
   Source amplitude supplies the receiving-pair admission. The actual
   current-clock producer supplies the helper list and full weighted payment.
5. Its prefix energy bound permits core-uniform fourth-root cutoff transport.
   Spend `delta0*M^2/4` on transport and retain `delta0*M^2/2` at the end.
   This controls the full energy, including coordinates newly active at L.
6. PNT supplies a prime in the logarithmic window. Since log M / M tends
   to zero, that prime also satisfies `16*q <= M`. Integer division gives
   the stated depth bound; the same logarithmic limit proves divergence.

## Whole-route consequence and remaining obstacle

The growing-depth omitted-prime range is now nonvacuous and paid at the
current clock, including all weighted coordinates and local cutoff changes.
This does not give an exhaustive continuation. Fixed primes eventually fall
below the moving logarithmic threshold. In particular the literal seed and
its helper batches retain the omission of 2. The constants depend on the
fixed seed; their exponential cardinality estimate cannot be silently reused
as a uniform bound over accumulated cores. Extensions at successive clocks
have not been proved nested, and future helper windows can overlap old cores.

The attempt to iterate this local producer therefore has an unproved
induction step, not a completed schedule. Existing current-clock depth and
delayed-half-repayment theorems already rule out paying all inherited debts
by uniformly shallow or bounded-mass delayed helpers. The next construction
must use retained correlations across the evolving core to pay fixed omitted
primes and admit fresh deep helper windows before their current-clock
thresholds. Bounded critical action and RH remain open.

## Search and audit facts

- Corpus hybrid/deep/method searches, plus source checks, identified the
  current-clock producer, weighted insertion identity, clip identity, source
  amplitude, cutoff transport and inherited-debt obstructions. Search hits
  were not accepted as discharged premises; used statements were Lean checked.
- Broad 2026 arXiv discrepancy/renewal searches found the Bansal--Nikolov
  discrepancy monograph, arXiv:2608.00140. Its abstract supplied no arithmetic
  payment law and no result from it is used in this proof.
- Scratch `lake env lean /tmp/hgt-deep-payment.lean` passed without warnings.
  All four public axiom audits contain exactly `propext`, `Classical.choice`,
  and `Quot.sound`. No added axiom or proof hole.
- The leaf is wired into `RHTower.lean`. Named build
  `lake build GaloisForLFunctions.RHTower.MobiusDivisorGrowingDepthCurrentPayment`
  passed without new-module warnings; existing dependency diagnostics were
  replayed. No full or umbrella build was run.
- Source indexes refreshed. `scripts/formal_tools.py lint` has no new-leaf
  error; it still fails on the four pre-existing unrelated unreachable
  modules `ThetaCuspHawkingBMLiteralCyclicPeierlsLowerWeylRadialDetector`,
  `ThetaCuspHawkingBMLiteralCyclicPeierlsSelfInverseSquarePhysical`,
  `ThetaCuspHawkingBMLiteralCyclicPeierlsSelfMixedCuspFlux`, and
  `XiHeatCassiniWoldJointDepthMobiusSourceTransport`.
- All owned Lean and search processes exited. Audit logs remain under
  `/tmp/hgt-deep-payment-*.log`.
