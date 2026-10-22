# Full-gate verification of the corpus, 2026-07-27

- **ID:** `corpus-full-gate-verification-2026-07-27`
- **Stage:** 1-in-progress
- **Type:** VERIFICATION RECORD (not mathematics)
- **Scientific status:** `[NOT NEW SCIENTIFIC KNOWLEDGE]` `[NOT AN RH PROOF]` — this is an audit
  record, kept because the corpus's per-card Lean claims had drifted and neither agent could tell
  what was actually verified.

## What was run

```
lake build GaloisForLFunctions.MainTheorems
  → ✔ [15093/15093]  Build completed successfully (15093 jobs)

scripts/formal_tools.py lint
  → formal lint passed        (proof debt: 0 — no active sorry/admit/axiom/opaque/unsafe)
```

`MainTheorems` imports all six theorem areas, so this single build covers the whole owned tree:
`RHTower` (3458 modules), `HTGeometry` (2560), `Bottcher` (379), `U0` (74), `Hurwitz` (58),
`HilbertMetric` (49) — about 59,000 declarations.

## Capstone axiom audit

Every area capstone was audited individually. All report exactly
`[propext, Classical.choice, Quot.sound]` — i.e. plain classical logic, no project axiom, no
`sorryAx`:

| Area | Capstone |
|---|---|
| rh_tower | `RHTower.rh_iff_tower`, `RHTower.rh_iff_forall_ladder` |
| ht_geometry | `GaloisForLFunctions.hypertranscendental_gamma`, `GaloisForLFunctions.HTGeometry.exists_wedgeFacetSewnUpperEndSystem` |
| hurwitz | `HurwitzN2Final.hurwitz_n2_unconditional` |
| u0_pui | `U0PhiIndep.u0_phi_independence`, `U0CardTheorems.u0_phi_independence_all_parameters` |
| q62_boettcher | `Bottcher.q62_independence`, `Bottcher.q62_mixed` |
| hilbert_metric | `GaloisForLFunctions.HilbertMetric.gaussianCorrectedDeterminant_mul_sq_le`, `…gaussianDistanceMatrix_det_mul_sq_le` |

## Why this record exists

Individual cards had drifted in **both** directions about what is formalized: some assert that the
tree lacks infrastructure it in fact has (e.g. several cards state "the formal tree has no radial
PSWF / oscillatory-measure interface" while `RHTower/L2FourierIntegralBridge.lean` supplies an
L¹/L² Fourier compatibility that mathlib itself lacks), and some leave `[ ]` on gates closed
elsewhere. A single full-gate run settles all of it at once and is cheaper than card-by-card
checking.

**What this does and does not say.** It says every claimed theorem in the corpus is a genuine
unconditional Lean theorem, and that the conditional results are conditional in their *statements*
(explicit hypotheses or `Prop` interfaces) rather than by hidden axiom. It says **nothing** about
whether any of them bears on the Riemann hypothesis. `RHTower.rh_iff_tower` being axiom-clean means
the *equivalence* is proved, not RH.

## Incidental finding for the Deninger lane

`RHTower/DeningerArithmeticSpectralLine.lean:292` emits a tactic `info` during the build:
`ring` fails there and the suggestion is `ring_nf`. It is not an error and the module builds, but
it is noise on every full build and the project's strict gate
(`lint --check-generated --build`) fails on build warnings. Worth a one-line cleanup by whoever
owns that module.

## Gates

- [x] full `MainTheorems` build
- [x] project lint, proof debt 0
- [x] axiom audit of all six areas' capstones
- [ ] re-run after the HTGeometry elliptic-gamma lane finishes its current batch
