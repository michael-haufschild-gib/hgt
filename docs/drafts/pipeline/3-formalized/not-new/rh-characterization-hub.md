# The Riemann Hypothesis characterization hub (TFAE)

- **ID:** rh-characterization-hub
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED HERE]` consolidation, axiom-clean
- **Statement:** `rh_tfae` — a 14-way `List.TFAE` proving RH equivalent to every representation the development supplies: raw non-vanishing on Re>1/2; coherent Kummer tower on Re>1/2; the 2^k ladder; off-line height locus empty; 2-adic valuation profile ≡ ⊤; census jump ≡ 0; boxZeros empty; variation zero-sets empty; u-plane descent zero-free on the slit plane; ξ_↓ coherent tower on slit plane; deck-charge trivial; line holography; window certificate at every level.
- **Lean:** `RHTower.rh_tfae` in `formal/GaloisForLFunctions/RHTower/RHCharacterizations.lean`. Axiom-clean. `lake build` green.

## What this is
"Bringing it together": the program's ~35 scattered `rh_iff_*` equivalences (each in its own file/representation) are collected into a single theorem showing they are one equivalence class. Consolidation, not new knowledge per piece — but it makes the unity of the diverse handles on ξ visible and machine-checked in one place, and is the reference point for any future characterization to plug into.

## Log
- 2026-07-07 — created directly in 3-formalized.

## Update: per-rung hub added
`rhLadder_tfae (k)` — the parallel `RH_{2^k}` rung TFAE (8 items): abstract ladder, hole-order divisibility, additive ladder charge, geometric deck charge, line holography, window certificate, and the strip/upper-half restrictions. Together with `rh_tfae`, the RH and every rung are now each a single machine-checked equivalence class across all representations. Axiom-clean, full MainTheorems gate green.
