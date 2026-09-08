# CCM-FU: middle selection with prescribed late order

- Type: derived diagnostic for the unchanged quadratic-order/RH target.
- Status: protocol frozen before execution.
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

All scripts and results will be downloaded under
`2-fully-proven/computations`; owned remote jobs and files and local
scratch will be removed. Broad corpus OR searches used `--any` for
transverse dissipation, middle/child transport, and exhaustive histories.
The scientific-method protocol was read before freezing this diagnostic.
