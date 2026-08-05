# Littlewood Z3: per-block estimate now has checkable hypotheses only (2026-08-05)

Extends `route_e/littlewood_z3_schedule_closed_2026_08_05`. Built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

## Changes

`HTGeometry/RatioBoundedWindowLanding.lean` — `exists_mem_window_of_ratio_lower_bound` now takes the
drop witness `k₀` explicitly (`start ≤ k₀`, `u k₀ ≤ U`) and returns `k ≤ k₀` as well. Necessary:
the produced order is the *least* one, so the caller's `k₀` controls the saving exponent.

`RHTower/Sieve/DirichletBlockSchedule.lean`
- `blockLambda_two_ge` : `8π·N^{1/3} ≤ t ⟹ lam₂ ≥ N^{−5/3}`. (`lam₂ = t/(8πN²)`,
  `N²·N^{−5/3} = N^{1/3}`.)
- `blockLambda_le_of_order` : `2 ≤ k`, `k−1 ≤ N`, `t ≤ 2π·2^k·N^{2/3} ⟹ lam_k ≤ N^{−1/3}`.
  Mechanism: `(k−1)! ≤ (k−1)^{k−1} ≤ N^{k−1}` when `k−1 ≤ N`, hence `lam_k ≤ (t/2π)/(2^k N)`.
- `dirichlet_block_saving_of_range` — **capstone, no existential hypotheses**:
  `8π N^{1/3} ≤ t ≤ 2π·2^{k₀}·N^{2/3}`, `k₀ ≥ 2`, `k₀−1 ≤ N`, `N ≤ M ≤ 2N+1`
  ⟹ `‖∑_{Ico N M} n^{−1−It}‖ ≤ 2560·N^{−1/(3·2^{k₀})}`.

Taking `k₀ ≈ log₂(t/(2π N^{2/3})) + 1` recovers the classical `k ≈ log t/log N` and the saving
`exp(−c log N/2^{k₀})`.

## Remaining in Z3

Head/tail split against `Sieve/HarmonicLogBound`; sum the per-block bound over dyadic `N` with the
per-block `k₀`. Then Z4 (PNTPlus truncation), Z5 (rectangle σ-version).

## Lean trap that cost several rebuilds

`field_simp` sometimes closes a goal outright and sometimes leaves an algebraic residue, and which
one it is changes when a *neighbouring* tactic changes. Do not guess whether to append `ring` /
`norm_num` — when the error is "No goals to be solved" at line L, print the file with line numbers
(`awk 'NR>=a && NR<=b {printf "%d: %s\n", NR, $0}'`) and confirm which tactic block line L is in.
Twice I moved a `ring` between two different `have` blocks because I mis-attributed the line.
Also: `gcongr` closed a whole `have` here, so the following `positivity` errored with "No goals".
