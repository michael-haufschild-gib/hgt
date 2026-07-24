# CCM Block--Fock / First-Trace Strict Closure-Jump Universality Law

- **ID:** LAW441
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Lean-corpus synthesis of `CCMBlockFockCodiagonalNoGo.lean` and
  `PrimeFirstTraceExactGraphClosureUniversalityLaw.lean`
- **Statement:** The actual-prime first-trace graph closure is a proper submodule of the
  block--Fock shifted-tail graph closure; the latter fills exactly the one vacuum response channel
  omitted by the former and hence jumps from a codimension-one response constraint to the whole
  product Hilbert space.

## Goal

Compare two arithmetic-Schur nonclosability mechanisms on their common ambient
`WithLp 2 (PrimeHardy × PrimeHardy)`.  The result identifies the exact severity increase caused by
the block--Fock shifted tail, rather than merely conjoining their separate no-go statements.

## Gates

- [x] 0 → 1 in-progress: both closures are exact corpus theorems in the same ambient submodule
- [x] 1 → 2 fully-proven: dependency-closed proof below
- [x] 2 → 3 formalized:
  `primeFirstTraceClock_graphClosure_lt_blockFockTailClock_graphClosure`;
  `lake env lean GaloisForLFunctions/RHTower/CCMBlockFockCodiagonalNoGo.lean` clean
- [ ] 3 → 4 publication-ready: pending standalone exposition and external novelty review

## Statement

Write

`F = closure(graph(primeHardyKernelMap, primeFirstTraceClock))`

and

`B = closure(graph(ccmPrimeOddBlockFockSourceMap,
                  ccmPrimeOddBlockFockTailClock))`.

Then

`F < B`.

More exactly, membership in `F` is equivalent to the single constraint `y 0 = 0`, whereas
membership in `B` is automatic.  Thus the strict inclusion is witnessed by the vertical vacuum
vector `(0, e₀)`.

## Paper proof

The exact first-trace closure theorem gives

`(x,y) ∈ F ↔ y 0 = 0`

for every `x,y : PrimeHardy`.  Therefore `F ≤ B` once the block--Fock saturation theorem identifies
`B = ⊤`.

Strictness is explicit.  Let `e₀ = lp.single 2 0 1`.  The vector `(0,e₀)` belongs to `B = ⊤`.
If it belonged to `F`, the exact first-trace characterization would give `e₀ 0 = 0`; evaluation of
the singleton instead gives `e₀ 0 = 1`, a contradiction.  Hence `F ≠ B`, and therefore `F < B`.
All inputs are existing proved Lean theorems; no analytic, numerical, or conjectural dependency
remains. `[PROVED HERE]`

## Novelty boundary

Claim only the joint strict closure-order law for these two corpus-specific actual-prime carriers.
The individual hyperplane closure, whole-product closure, and their separate nonclosability
consequences are pre-existing corpus facts.

## Log

- 2026-07-23 — Discovered bottom-up from the common ambient graph-closure theorems; prior corpus
  search found no comparison theorem.
- 2026-07-23 — Dependency-closed paper proof completed before external literature search.
- 2026-07-23 — Formalized in the already umbrella-imported
  `CCMBlockFockCodiagonalNoGo.lean`.
- 2026-07-23 — Post-proof literature search found general Hardy/Schur and Fock-space operator
  literature, but no occurrence of these two actual-prime graph closures or their strict
  hyperplane-to-top comparison.  No collision found; this is a scoped novelty audit, not a claim
  that generic strict submodule comparison is new.
