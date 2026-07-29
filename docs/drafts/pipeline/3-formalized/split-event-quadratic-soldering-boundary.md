# Split-event quadratic soldering boundary

- **ID:** `split-event-quadratic-soldering-boundary`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Status:** `[LEAN-PROVEN] [AXIOM-AUDITED] [REDISCOVERED] [BRIDGE]`
- **Paper proof:**
  `../2-fully-proven/not_new_scientific_knowledge/split-event-quadratic-soldering-boundary.md`
- **Lean module:**
  `../../../formal/GaloisForLFunctions/HTGeometry/EventSecondOrderSoldering.lean`
- **Statement:** A split event admits two arbitrary one-way off-diagonal channels but no universal
  nonzero endpoint soldering; their quadratic composite obeys an exact covariant cancellation law,
  and an invertible parallel composite locks endpoint endomorphisms by conjugacy.

## Formal theorem inventory

`GaloisForLFunctions.HTGeometry.EventSecondOrderSoldering` proves:

1. `splitEventMap_block_parallel_iff`:
   \[
   BT=TA\iff c=0\ \wedge\ q=0\ \wedge\ s=d
   \]
   for completely general source and target block endomorphisms.
2. `universal_endpoint_solder_eq_zero`: any \(C\to K\) map intertwining every independent pair of
   endpoint endomorphisms is zero.
3. `splitQuadraticSolder_covariant_cancellation`:
   \[
   (ab-bd)r+b(dr-rp)=a(br)-(br)p.
   \]
4. `splitQuadraticSolder_parallel_of_channels`: parallel component channels have a parallel
   quadratic composite.
5. `splitQuadraticSolder_equiv_locks_endpoints`: if that composite is a linear equivalence, the
   endpoint endomorphisms are conjugate.

## Scope boundary

All results hold over an arbitrary commutative ring and arbitrary modules with additive
commutative-group structure. The module assumes no finite dimension, inner product, positivity,
manifold, connection, Lorentz signature, gauge group, spacetime, or dynamics.

The formal result therefore does **not** prove that:

- the off-diagonal channels exist physically;
- their composite is a tetrad or solder form;
- its gluing defect is gravity;
- Einstein or Standard Model dynamics descend from an event law.

Those claims remain inside the stage-1 physical conjecture.

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/EventSecondOrderSoldering.lean`: pass
- scratch `#print axioms` audit:
  - classification: `propext`, `Quot.sound`
  - universal no-go: `propext`, `Quot.sound`
  - cancellation: `propext`, `Classical.choice`, `Quot.sound`
  - parallel-composite and conjugacy: `propext`, `Quot.sound`
- no custom axiom, `sorry`, `admit`, `opaque`, or `unsafe` declaration
- `lake build GaloisForLFunctions.HTGeometry.EventSecondOrderSoldering`: pass
- repository-wide lint: new module reachable and clean; gate remains red only because of
  pre-existing unrelated unreachable modules listed by the lint report

## Gates

- [x] paper theorem dependency-closed
- [x] exact paper theorem reproduced in Lean
- [x] axioms inspected through a `/tmp` scratch file
- [x] physical interpretation excluded from theorem statements
- [x] focused final module build
- [ ] not eligible for stage 4 as a standalone novelty claim

## Log

- 2026-07-29 — formalized classification, obstruction, cancellation, and conjugacy over arbitrary
  commutative rings and modules.
- 2026-07-29 — focused final build passed: 2943/2943 jobs.
