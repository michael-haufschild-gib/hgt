# CCM-FU: middle selection with prescribed late order

- Type: derived diagnostic for the unchanged quadratic-order/RH target.
- Status: frozen screen and independent audit complete; uniform estimate open.
- Chain: actual divisor source → complete quadratic raw-energy order →
  O(M) Abel bound → CCM-FU → RH. Frontier map read only.

## Question

The global late-order rounding theorem permits any fixed late relative
order whenever some uniform quadratic order exists. It does not say a
greedy middle selector can realize one. Test that missing selector on the
literal full field, retaining every nonempty cofactor and every prime.
Neither outcome is inferred from the rounding theorem. Monotone transverse
contraction is already false; no such constraint is imposed here.

## Frozen diagnostic

- Cutoffs: 512, 2048, 8192, 32768; four independent RunPod workers.
- Two fixed late orders: increasing prime and decreasing prime. A late
  prime has M/2<p<M. Every other prime remains an independently available
  middle/small choice. Reuse the unchanged source generator.
- At each state choose the minimum next complete raw energy among every
  unused nonlate prime and the next prime in the fixed late order. Break
  exact ties by smaller prime. Process all primes, even after a failure.
- Compute all signed one-prime gains from literal source incidences;
  regroup every selected successor directly. No transverse coordinate or
  signed mixed term is omitted.
- Record every prime and prefix energy, head, remaining late mass and
  squares, energy in the nonempty nonlate cells, all positive-gain states,
  the first crossing, and the largest post-initial energy state. At a
  crossing, save every allowed successor and its complete gain.
- A factor-one crossing exceeds `1e-10 max(1,Q_empty)`. Such a crossing
  refutes this selector's factor-one behavior at that cutoff, not the
  uniform quadratic existence target or RH.
- Compare original diagonals and source totals at the three repeated
  cutoffs with saved joint-minimax data; do not rerun its policies.
- Use four processes with BLAS/OpenMP/MKL each limited to one thread.
  Internal deadline 90 seconds; outer timeout 100 seconds. Preserve
  completed cutoff records if interrupted. No cutoff extension in this run.

## Frozen independent audit

If a path crosses, select the smallest failing cutoff, increasing-late
policy first on a tie, and its first crossing state before insertion.
If neither path crosses, select the first state with strictly positive
minimum allowed gain and at least one active nonscalar label, in cutoff
order and then increasing-late policy order. If none exists, use the
largest post-initial energy state with an available successor at the
largest completed cutoff.

Reconstruct the selected state from independently factored original
time-sum coefficients at 80 digits. Check every allowed successor by
direct fibre regrouping, selected minimum, its margin, and source energy
decomposition. Retain complete signed cofactor products of the selected
middle prime (or the least-energy middle alternative if a late prime is
selected). Audit uses at most four workers, 90 seconds internally and
100 seconds externally. High-precision floating results are not interval
certificates and never become Lean premises.

## Discrimination and scope

A crossing exposes an actual coupled field where this history leaves no
allowed continuation below the original diagonal. A pass supplies a
complete path only at the tested cutoff. Signs and nonlate energy at the
audited state will determine whether the next proof attempt should bound
transverse growth, head compensation, or the cost of postponing a middle
prime. No unseen all-cutoff conclusion is asserted.

All scripts and results are downloaded under
[`2-fully-proven/computations/ccm-fu-fixed-late-greedy-2026-09-08`](../2-fully-proven/computations/ccm-fu-fixed-late-greedy-2026-09-08/README.md).
Hashes agree with RunPod. Owned remote jobs, remote directory and local
scratch are removed. Broad corpus OR searches used `--any` for
transverse dissipation, middle/child transport, and exhaustive histories.
The scientific-method protocol was read before freezing this diagnostic.

## Audited result

Both policies complete every tested cutoff, with maximum energy equal to
the initial diagonal. Screen: four workers, 2.705 seconds. Original time-sum
audit: 80 digits, four workers, 0.093 seconds. These are floating diagnostics,
not interval certificates or Lean premises. No new Lean declaration or
build was needed.

The frozen audit selects `M=512`, increasing-late policy, state index 20.
All 41 allowed moves strictly increase raw energy. Its 43 active nonscalar
labels coexist with the selected scalar-only move `p=131`. The selected
gain is `0.0035562454474282`; its margin over the next best move is
`0.0037358390855893`. This is a local rise below the original diagonal,
not a ceiling failure.

The saved trajectory then processes `131,137,139,149,151,157,13`.
Energy rises from `35.0297470636` to `35.3128500025`, then returns to
`35.0247365588`. The original diagonal is `311.5512693800`.
Only the first state and every one-step alternative there were independently
audited; continuation values are from the directly regrouped screen.

## Direct proof attempt and remaining estimate

Write a still-available interacting prime's full gain as `2 f a + T`,
where `f` is the current head, `a` its singleton coefficient, and
`T = 2 sum_{R nonempty} F_R F_{R union {q}}`, over labels avoiding `q`.
If preceding operations merge isolated negative scalar leaves of total
mass `t`, then this gain becomes `2(f-t)a+T`. All nonhead products stay
in the formula. For `a>0`, making the head sufficiently negative can
therefore turn a costly interacting step into a contracting one.

At the audited state, prime 13 has `a=1.51416685499` and
`T=1.48378516593`, while its head contribution is `-0.20074559169`.
The six scalar moves change the head from `-0.06628912495` to
`-0.58510678786`; the following prime-13 insertion contracts. These
scalar labels have no interaction with 13, by their product cutoffs.
The corresponding identities already follow from the literal merger
and isolated-leaf transport laws; numerical values prove no general sign.

The attempted source estimate must control **both** the quadratic cost
of reaching this compensation head and the availability of a useful
interacting packet before the scalar supply ends. Neither is supplied
by the observed excursion. A tiny positive `a` can make `T/(2a)` large;
the quotient transport bound controls the full gain, not this ratio.
After a genuinely interacting insertion, all future `a` and `T` must
be recomputed from the changed source. No fixed-head or fixed-packet
induction is justified across that insertion.

The broader corpus audit found these precise limits:

- `MobiusDivisorUniformSuccessorTransport` bounds every complete move,
  but its additive quotient sum is too large through the unbounded front.
- `MobiusDivisorQuotientWindowOrder` controls a whole quotient window
  by three source endpoints; it does not bound those endpoints globally.
- `MobiusDivisorPrescribedWindowRepair` supplies actual compensators
  while its bounded-quotient pools remain fresh. It does not exhaust the
  unbounded middle front or replenish used primes.
- `MobiusDivisorFixedCoreEnergyLimit` has a core-dependent error;
  its limit cannot be applied uniformly to growing processed cores.
- `PositivePrimeCubeEnergyBarrier` prevents a generic positivity plus
  small-final-total argument from proving the original-diagonal ceiling.
- `MobiusDivisorContinuousHeadMoment` gives a uniform signed moment,
  but does not supply unused prime samples or a transverse gain bound.

No selector is retired, and no all-cutoff conjecture is inferred from
these finite passes. The missing uniform interacting-prime estimate,
complete prime exhaustion, Abel bound and unconditional RH term remain open.
