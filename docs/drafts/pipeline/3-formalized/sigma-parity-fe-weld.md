# The σ-parity = FE-parity weld

- **ID:** sigma-parity-fe-weld
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/door-C5-irreducibility-and-door-2-retest.md, ../../door/bucket-ledger-footholds.md · 00-status row #49
- **Statement:** `σ` acts as `(−1)^k` on `∧^k V` (the prime-lattice exterior algebra), so `H^even` is
  FE-surviving and `H^odd` is FE-killed — tying the difference-Galois cohomology grading to the
  functional equation.

## Goal
A native-candidate weld: a parent discipline would not state it without the multi-`q` / prime-lattice
apparatus. A worked example of an item already deep in the pipeline.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: `fe_odd_moment_vanish`, `fe_centered_odd_moment_vanish`,
  `exteriorPower_map_neg_id` — axiom-clean (in the audit)
- [ ] 3 → 4  publication-ready

## Next steps
1. **Door-2 test:** does the weld survive stripping the multi-`q` vocabulary? Record the verdict.
2. If it survives, **write the standalone note** (statement + the exterior-power computation + the Lean
   certificate + the Door-2 argument) — the publication-ready gate.

## Log
- 2026-06-19 — created in 3-formalized (Lean theorems exist; next gate is the writeup + Door-2)
