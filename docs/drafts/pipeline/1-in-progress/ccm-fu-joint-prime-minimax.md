# CCM-FU: complete raw-energy orders from joint prime choices

- Type: derived selection diagnostic for the existing PE4 target, not a
  primary universal conjecture or a changed energy ceiling.
- Status: protocol frozen before execution.
- Chain: actual divisor source → a complete prime order with raw energy
  at most the original diagonal → O(M) Abel bound → CCM-FU → RH.
- Frontier map read only. No endpoint bound is assumed.

## Question and evidence

The coarea and corrected coarea envelopes are formally excluded for every
complete prime order. The raw-energy target survives. One-prime greedy
and fixed-sector greedy diagnostics have failures; positive scalar supply
and terminal-order theorems do not exhaust the interacting middle primes.
The corpus supplies exact joint-prime mixed energy differences and a sharp
two-coordinate minimax formula. None determines whether the following
fixed two-prime policy succeeds on the actual source.

The experiment asks whether joint choices give complete factor-one paths,
and which signed cofactor interactions make them differ from one-prime
greedy. A failure concerns this policy, not existence of another PE4 order.
No numerical experiment can establish an all-cutoff theorem.

## Frozen policy

At each state P, retain the complete literal signed field F and raw
energy Q=Σ F². For each distinct unused pair p,q, compute both first-step
energies Q_p,Q_q and the common two-step endpoint Q_pq. Its best internal
peak is `max(min(Q_p,Q_q),Q_pq)`. Choose the pair minimizing, in order:

1. that internal peak;
2. the two-step endpoint;
3. the smaller first-step energy;
4. increasing unordered prime pair.

Within the selected pair, process the lower-energy first step, breaking
ties by smaller prime, then process the other prime. Continue through
every prime, even after crossing the original ceiling. A final unpaired
prime is processed normally. The one-prime raw greedy control always
chooses the smallest next raw energy, with smaller prime breaking ties.

For a cofactor r, write h=F_r,a=F_pr,b=F_qr,c=F_pqr. The exact mixed
second energy difference is `2Σ_r(hc+ab)`. Use sparse matrix products
for the cross-child sum and literal product-incidence sums for the joint
child. Recompute every selected successor directly and check identities.
All source indices, labels, and intermediate one-prime states are retained.

## Frozen experiment and falsifiers

- Cutoffs: 512, 1024, 2048, 8192. Four independent worker processes;
  BLAS/OpenMP restricted to one thread each.
- Run only on the supplied RunPod. Use the existing complete source
  generator unchanged; recompute this new policy and raw greedy control.
- Save every selected prime and prefix energy, original diagonal and
  terminal sum, peak ratios, first ceiling crossing, and all selected
  pairs' mixed terms. Record choices that abandon the current greedy
  prime, and positive first steps followed by a nonpositive total change.
- A strict ceiling failure exceeds `1e-10 max(1,Q_empty)`.
- Screen deadline: 90 seconds, with a 100-second outer timeout. Partial
  completion is recorded; a timeout is not evidence against PE4.
- Independent 80-digit audit: choose the smallest cutoff where the pair
  path crosses the ceiling; audit its first offending pair from the
  original time-sum source. If no pair path fails, use the smallest cutoff
  with a pair choice different from greedy and its first such pair.
  If neither occurs, audit the first pair at 512.
- Audit every available pair at that selected state by direct sequential
  fibre regrouping, independently of the mixed-difference scoring code.
  Compare the chosen pair and its two prefix energies, report close ties,
  and retain signed cofactor terms. Audit deadline: 90 seconds plus a
  100-second outer timeout. No interval certificate is claimed.
- Download scripts/results to `2-fully-proven/computations`; remove owned
  remote jobs/files and local scratch. No numerical result enters Lean.

## Expected discrimination

Success would expose actual complete orders and the cofactor terms that
permit joint improvement. Failure would identify an actual state where
this two-step choice cannot retain the original ceiling, or where an
earlier locally optimal choice loses later capacity. The signs, active
products, and order conflicts decide which arithmetic statement deserves
a proof attempt. No prediction of either outcome is asserted.

## Corpus search

Broad OR searches used `--any` for middle/mixed primes, paired overlaps,
signed batches, lookahead, minimax, joint primes, order conflicts, and
global orientation. Relevant leaves include `MobiusDivisorLocalizedInteractions`,
`TwoCoordinateMergerCeiling`, `MobiusDivisorGrowingSignedPrimeBatches`,
`MobiusDivisorSquareRootTerminalOrder`, and `PositivePrimeCubeEnergyBarrier`.
The last is a generic source-shape obstruction, not an actual-source
counterexample. The scientific-method protocol was read before freezing.
