# Completed occupation forces quantitative same-draw circuit-hard intervals

- **ID:** `completed-occupation-quantitative-same-draw-hard-gap-law`
- **Stage:** 3 -- formalized in Lean 4
- **Type:** theorem / deterministic occupation packing / static Choi plateau
- **Status:** `[FORMALIZED] [FRONTIER ADVANCE] [NOVELTY AUDIT PENDING]`
- **Date:** 2026-08-21

## Public theorem

For one fixed finite-spectrum Hamiltonian, let `b` bound completed one-sided occupation of the
wide-radius complete depth-`s` circuit union.  Put

`S(E) = 1 + sum_i |E_0-E_i|`,

and choose trace radii `0 <= eps_n < eps_w`.  If

`b < mesh/(W+mesh)`, where `mesh=(eps_w-eps_n)/S(E)`,

then after every time `A0` there is an interval `[u,u+W]`, `u>=A0`, throughout which the exact Choi
orbit is farther than `eps_n` from every padded depth-`s` circuit output.

For maximally projective spectra, `b` is the explicit projective circuit-target Haar-volume bound.
For every parameter in the nearest-neighbour Gaussian growth--maximal event, the same Hamiltonian
therefore has:

1. robust laboratory-time operator-complexity growth;
2. arbitrarily late quantitative continuous hard blocks against the complete circuit dictionary;
3. perpetual recurrence--hardness--recurrence alternation.

No Hamiltonian is redrawn.

## Conjecturing ledger

### C1 -- completed occupation cannot produce a pathwise continuous plateau

**Falsified.**  Every narrow hit has positive time thickness in a wider target.  If every interval
of length `W` contained a narrow hit, disjoint widened visit cells would force completed wide-target
density at least `delta/(W+delta)`.  This contradicts any smaller completed upper density.

### C2 -- visit thickness is necessarily non-effective

**Falsified.**  The normalized projective Choi vector obeys

`||Psi(t)-Psi(u)|| <= S(E)|t-u|`,

and its projected density obeys

`dist(rho(t),rho(u)) <= sqrt(2) S(E)|t-u|`.

The `sqrt(2)` cancels when density radii are translated back to pure-state trace radii, leaving the
explicit `mesh=(eps_w-eps_n)/S(E)`.

### C3 -- one-sided physical time loses the completed target bound

**Falsified.**  Uniform sampling on `(0,T]` pushes forward exactly to the one-sided projective phase
law.  One-sided Kronecker--Weyl plus Portmanteau gives the same Haar upper bound, with no factor two.

## Lean certificate

- `GaloisForLFunctions.HTGeometry.CompletedOccupationHardGapLaw`
  - `exists_late_interval_disjoint_of_limsup_windowProbability_le`
  - `exists_late_interval_metric_hard_of_limsup_windowProbability_le`
- `GaloisForLFunctions.RHTower.StaticChoiContinuousHardGapLaw`
  - exact one-sided physical-time preimage bridge
  - same-H continuous projected and operational Choi hard-block theorems
- `GaloisForLFunctions.RHTower.StaticChoiQuantitativeHardGapLaw`
  - `projectiveChoiSpeed`
  - `norm_fullUniformPhaseChoiVector_time_sub_le`
  - `dist_projectiveChoiDensityFlow_le`
  - `maximallyProjective_pureChoiCircuitTargets_explicit_late_hard_intervals`
- `GaloisForLFunctions.RHTower.NearestNeighborGaussianSameDrawGrowthPlateauRecurrenceLaw`
  - `nearestNeighborPath_sameDraw_growth_quantitative_continuous_hard_intervals`
  - `nearestNeighborPath_sameDraw_growth_hardBlocks_recurrence`

All proof bodies are closed.  Targeted source checks pass.  Both new modules are wired into their
umbrellas; no umbrella build is required.

## Hostile boundary

This closes the pathwise continuous-plateau gap and gives an explicit inverse-occupation duration
law.  It does **not** close Brown--Susskind first onset:

- the first hard block may begin arbitrarily late;
- laboratory growth currently holds on a positive-measure event, not with probability `1-o(1)`;
- no theorem yet excludes every circuit-set hit between the laboratory window and the first late
  hard block;
- recurrence alternation is syndetic but does not provide a matching lower bound for the first
  return measured from the initial departure at time zero.

The remaining frontier is therefore no longer continuous-time filling or completed occupation.
It is an onset theorem: a quenched fixed-time/first-entry bound for the ordinary one-draw static
local ensemble strong enough to connect laboratory growth to the first quantitative plateau block.
