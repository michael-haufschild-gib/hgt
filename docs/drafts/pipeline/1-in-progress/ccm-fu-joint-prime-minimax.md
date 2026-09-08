# CCM-FU: complete raw-energy orders from joint prime choices

- Type: derived selection diagnostic for the existing PE4 target, not a
  primary universal conjecture or a changed energy ceiling.
- Status: frozen experiment and independent audit completed; exact
  two-step source selection law kernel checked. PE4 remains open.
- Chain: actual divisor source → a complete prime order with raw energy
  at most the original diagonal → O(M) Abel bound → CCM-FU → RH.
- Frontier map read only. No endpoint bound is assumed.

## Question and evidence

The coarea and corrected coarea envelopes are formally excluded for every
complete prime order. The raw-energy target survives. Universal stepwise
contraction and fixed-sector greedy diagnostics have failures; the
factor-one raw greedy ceiling remains open. Positive scalar supply
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

## Observed discrimination

Both joint minimax and raw greedy completed every prime at 512, 1024,
2048, and 8192 without exceeding the original diagonal. Joint minimax
abandoned the current raw greedy choice 3, 4, 10, and 25 times,
respectively. This establishes no ceiling advantage over the control.
The screen took 2.78 seconds on four RunPod workers. An initial output
serialization failure was repaired without changing the frozen policy;
that failed attempt is retained separately.

The independent 80-digit original-time-sum audit checked all 1953 pairs
at the first changed choice at M=512. It confirmed the unique optimal
unordered pair {23,467}, ordered 467 then 23. Both first steps increase
energy; the pair has peak 33.33113 versus current energy 33.18634 and
original diagonal 311.55127. There are 34 active nonscalar labels.
Permitting each cofactor to select its own order would underestimate
the best genuine first step by 2.43416. These are floating diagnostics,
not interval certificates or Lean proof premises.

## Exact consequence [PROVED HERE]

At a fixed actual state put f=F_empty, a=F_{q}, and
G=Q(P+q)-Q(P), retaining every transverse cofactor in G. For an unused
isolated late prime p distinct from q, write C_p=-b. Exact source laws give

    Q(P+p)-Q(P) = -2 f b,
    Q(P+p+q)-Q(P) = G-2(f+a)b.

The best two-step internal peak above Q(P) is therefore

    L(b) = max(min(-2 f b,G), G-2(f+a)b).

In the audited sign regime f<0<f+a, G>0, its continuous minimum is
`-f G/a`, attained exactly at `b*=G/(2a)`. To prove the minimum, split
at b*: below it the endpoint is at least the claimed minimum; above it
both possible first steps are at least that minimum. At b* the late-first
gain and common endpoint coincide. Strict slopes give unique equality.

More usefully, if the remaining ceiling budget H satisfies H<G, then

    L(b) <= H  iff  (G-H)/(2(f+a)) <= b <= H/(-2f).

The first inequality pays the endpoint, the second pays the genuine first
step. This follows by eliminating the inadmissible q-first choice and
dividing by the two strictly positive denominators. The interval is
nonempty exactly when `-f G <= a H`. Continuous feasibility is not
actual prime supply: the amplitude of a still-unused late prime must lie
in this interval. No hypothesis about sign coherence of transverse cells
is used, and no statement chooses that prime independently of the source.

This identifies the next hard arithmetic obligation: prove suitable
unused source amplitudes and sufficient remaining budget continue to
exist as interacting middle primes are consumed. A local minimax formula
alone does not discharge that obligation or bound the terminal sum.

For the weaker uniform-quadratic existence target needed by RH, the
[global late-order rounding theorem](ccm-fu-late-order-rounding.md) removes
late-prime permutation as an essential choice: any successful order can
be transformed to any prescribed late-prime relative order, with another
uniform quadratic constant and every intermediate stage controlled.
Thus exact single-prime window supply remains relevant to the factor-one
policy, while the RH search can fix late order and attack the interacting
middle-core trajectory. Existence of that trajectory is still unproved.

## Formal certificate and scope

[MobiusDivisorLatePairMinimax](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorLatePairMinimax.lean)
contains nine new public theorems. `mobiusDivisorPairGain_late_eq`
identifies the best genuine two-step gain with the complete-source
scalar profile. `latePrimePairGain_optimal` proves the sharp continuous
minimum and unique equality amplitude. `latePrimePair_interval_nonempty_iff`
classifies continuous feasibility. `mobiusDivisorPairGain_late_le_iff`
gives the exact admissibility test on a literal unused prime coefficient.
The other five theorems establish the budget and balance laws used here.

These are derived exact laws, not a replacement of the frozen PE4 target.
They introduce no source bound or prime-supply assumption into an RH
endpoint. Scratch and installed-leaf `lake env lean` checks passed.
The nine new theorem axioms were checked once in an external scratch
file: only `propext`, `Classical.choice`, and `Quot.sound`. No old theorem
was re-audited, and no numerical result enters the proofs. The leaf is
imported by RHTower.

Full experiment scripts, paths, pair candidates, failure metadata,
independent audit, timings, and hashes are recorded in the
[computation directory](../2-fully-proven/computations/ccm-fu-joint-prime-minimax-2026-09-08/README.md).

Final exact-module `lake build` compiled the byte-identical leaf in 7.7
seconds in an isolated temporary package using the repository toolchain
and existing dependency oleans. Only the new leaf compiled. No umbrella,
full, or dependency-source build ran. An initial empty-target package
configuration did not compile a leaf; its glob was corrected before the
actual final audit. Temporary cache-package manifest warnings concerned
packaging; the new Lean source emitted no warnings or tactic diagnostics.

Indexes were regenerated. Global `scripts/formal_tools.py lint --check-generated`
reported five unrelated modules without umbrella reachability:
`SelbergLocalTestGreen`, `FokasLenellsOrbitDecay`, `FokasLenellsOrbitEntries`,
`FokasLenellsOscillatoryOrbit`, and `FokasLenellsScatteringDecay`. A passing
global lint gate is not claimed. Own source, unique import, proof-debt,
whitespace, and local-link checks passed. Owned remote experiment files,
local scratch, and the final audit package were removed; all owned jobs
terminated. The frontier map was read only.
