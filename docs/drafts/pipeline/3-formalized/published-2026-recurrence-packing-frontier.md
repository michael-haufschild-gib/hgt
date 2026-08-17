# Published 2026 recurrence-packing frontier

- **ID:** `published-2026-recurrence-packing-frontier`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Marcin Kotowski and Michał Oszmaniec, *Tight bounds on recurrence time in closed quantum systems*, arXiv:2601.10409v3 (3 August 2026), Proposition 1
- **Statement:** For a metric-invariant one-parameter flow, if every finite set of points separated by at least `ε` has cardinality at most `N`, then every positive sampling interval `T` contains a return at some time `kT`, with `1 ≤ k ≤ N`; hence the return occurs by `TN`.

## Goal

Kernel-check the current deterministic recurrence-time frontier before attempting any extension.

## Gates

- [x] 0 → 1: primary source, exact statement, and proof dependencies identified
- [x] 1 → 2: complete paper proof reproduced
- [x] 2 → 3: Lean theorem `published2026_flow_recurrence_packing_frontier`; targeted build and axiom audit pass
- [ ] 3 → 4: not a publication target; this is an external-frontier baseline

## Paper proof

Sample the orbit at `0,T,…,NT`. If no sampled point returns within distance `ε` of the initial
point, metric translation invariance implies every pair of sampled points is separated by at least
`ε`: for `i<j`, translate the pair at times `iT,jT` backwards by `iT`, reducing its distance to the
distance between times `0,(j-i)T`. The `N+1` samples are therefore distinct and form an
`ε`-separated set, contradicting the packing bound `N`. Thus some `1≤k≤N` returns, and positivity
of `T` gives `T≤kT≤NT`.

## Audit note

The primary source uses the weak separation convention `d(x,y)≥ε`; the formal definition
`ClosedPackingBound` preserves that convention exactly instead of silently substituting mathlib's
strict `IsSeparated` convention.

## Log

- 2026-08-17 — exact primary-source statement frozen before further conjecturing.
- 2026-08-17 — paper proof closed and scratch Lean proof passed.
- 2026-08-17 — targeted module build passed; both frontier theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.
