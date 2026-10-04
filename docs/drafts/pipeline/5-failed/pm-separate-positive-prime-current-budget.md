# PM: a separate subpower budget for the positive prime-update current is false

- **ID:** pm-separate-positive-prime-current-budget
- **Stage:** 5-failed
- **Type:** FALSIFIED; positive survivor formalized
- **Source:** Route PM; `../3-formalized/pm-prime-update-positive-current.md`
- **Statement rejected:** for every positive damping, the positive quadratic terms of the canonical prime-update energy admit a uniform budget, or a budget by every positive power of the horizon.

## Exact obstruction

`pmPrimeUpdateQuadraticCurrent_div_rpow_tendsto_atTop` proves that for `0<epsilon<1/4` and `0<=kappa<1/2-2*epsilon`,

`Q_epsilon(8*P^2)/(8*P^2)^kappa -> infinity`.

Here `Q` is the sum over the actual canonical prime cores, with the physical cutoff and dilation retained. This is not an arbitrary-coefficient example. The separate budget conjecture is therefore false. The complete signed energy and RH are not falsified.

## Positive survivor and new insight

Below twice the prime aperture threshold, the core equals the full source plus the explicit missing-prime mass. On reciprocal slab `[3P/2,7P/4]`, the full source is uniformly negligible relative to this positive mass, and the core approaches that mass with relative error tending to zero. This forces a localized energy floor of order `P^(1-2*epsilon)/log(P)^2` in the literal canonical prime core.

The exact decomposition, uniform relative statement and energy floor are formalized in `PMPowerDampedMobiusPrimeSlab`, `PMPowerDampedMobiusPrimeSlabBounds`, and `PMPowerDampedMobiusPrimeCurrent`. These are non-trivial positive statements about the original source, not a restatement of the budget failure. They identify the physical slab producing the divergent current and require any admission proof to retain its complete mixed compensation.

## Closure status

Dependency-closed paper proof and Lean certificate: `../3-formalized/pm-prime-update-positive-current.md`. Actual-file checks and targeted old leaf builds passed; all exported theorem axiom lists contain only standard Lean logical axioms. No new premises, axioms, numerical experiments or heartbeat changes. Global lint retains unrelated failures recorded on the certificate card.

This closes only the separate positive-current budget branch. The hard PM target is the full cutoff-dependent combination `Q_epsilon(N)-2*M_epsilon(N)`, or equivalently the actual signed energy bound. That target remains open.
