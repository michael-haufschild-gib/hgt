# Analytic zero-level support cellularization

- **ID:** `analytic-zero-level-support-cellularization`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** irregular microlocal RH foundation audit
- **Statement:** Sampling a nonzero analytic Stokes phase at canonical chamber midpoints recovers
  exactly the alternating cyclic exponential boundary representation.

## Goal

Build an unconditional generator-level bridge from actual compactified exponential epigraph
support to the existing cellular Stokes category, without assuming an irregular RH functor.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack identified
- [x] 1 → 2 fully-proven: trigonometric chamber-sign proof is dependency-closed
- [x] 2 → 3 formalized: Lean theorem, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone exposition and external novelty audit

## Approach

Use midpoint between each labelled analytic wall and its cyclic successor. Multiplication by pole
order moves phase argument by `π/2`, so midpoint phase is `-‖c‖` on active arcs and `‖c‖` on
inactive arcs. Zero-level epigraph therefore selects exactly Boolean arc label; walls lie on
support. Lift resulting support-indexed quiver prefunctor to entrance-path category and identify it
with `exponentialBoundary`.

## Log

- 2026-08-24 — opened after corpus audit found analytic wall/support realization and cellular
  boundary object but no exact support-to-cellular generator bridge
- 2026-08-24 — formalized in `StokesAnalyticSupportCellularization.lean`; actual Puiseux branch
  pairs specialize to their contact-order exponential boundary; direct Lean check and targeted
  build pass; all declarations use only `propext`, `Classical.choice`, and `Quot.sound`
- 2026-08-24 — linked support-cellularized boundaries to local exponential germs and actual
  wallwise microstalk modules, then to analytic-wall functor ranks, including Puiseux branch pairs
