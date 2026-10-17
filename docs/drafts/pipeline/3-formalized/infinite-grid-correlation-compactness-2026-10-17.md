# Compact correlation limits with preserved Lévy energy

- **ID:** infinite-grid-correlation-compactness-2026-10-17
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scope:** Independent BiScaleUncertainty; certified package 8/100.
- **Statement:** Every bounded-energy sequence of normalized infinite-grid source correlations
  has a globally uniform convergent subsequence; the limit preserves positivity, zeros,
  vanishing at infinity, and the energy ceiling.

## Plan and gates

- [x] Corpus search and exact reusable compactness/energy APIs inspected.
- [x] Dependency-closed paper proof in `InfiniteGridCorrelationCompactness.md`.
- [x] Formalize actual source class, compact closure, and uniform subsequence extraction.
- [x] Formalize limit geometry, finite Gram positivity, Fatou bound, and actual integrability.
- [x] Direct leaf checks, complete axiom audit, umbrella wiring, generated API, formal lint.

## Certificate

`InfiniteGridCorrelationCompactness.lean` (nine public theorems) and
`InfiniteGridLimitEnergy.lean` (eight public theorems) passed without diagnostics.
All seventeen endpoint dependency audits contain only `propext`, `Classical.choice`,
and `Quot.sound`; the private identity is covered transitively. Both imports and all
generated API entries verified. Capstone: `exists_infiniteGrid_finite_energy_limit`.
Logs: `/tmp/infinite-grid-{compactness,limit-energy}-leaf.log` and
`/tmp/infinite-grid-compactness-{axioms,index,lint}.log`.
Global lint reports three concurrent foreign unwired modules, named in the paper.
Neither owned leaf has a lint error. Count the connected compactness/energy theorem once.

## Boundary

Compactness is in the global correlation supremum norm. No compact-source or L²-source
representation of the limit is assumed. This topology alone supplies no bound on the
exponentially weighted polar moment; its closedness remains a separate problem.

`HTGeometry.totallyBounded_bcf_of_uniform_tails` already supplies the noncompact-domain
Ascoli argument for complex bounded continuous functions. Reuse it by complexifying real
correlations, then take real parts of limits. New work derives every compactness and energy
condition from actual sources and their normalized energy bound.
Search: `/tmp/infinite-grid-compactness-deep-search.txt`, complete discovery with source-only
candidates, older-generation coverage snapshot, semantic coverage unmeasured.
