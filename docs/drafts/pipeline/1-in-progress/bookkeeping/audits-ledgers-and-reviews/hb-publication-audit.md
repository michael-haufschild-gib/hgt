# Route HB publication audit

- **ID:** HB-PUBLICATION-AUDIT
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (expository research paper; not an RH proof)
- **Source:** rh-current-frontier-map.md; ../../../../../notes.md; current Lean checkout
- **Statement:** Produce a reproducible, premise-explicit account of HB, its verified mathematics, obstructions, and remaining problems.

## Plan

1. Inventory both requested documents, linked HB cards, relevant memories, and Lean source modules. Record discrepancies and snapshot hashes.
2. Search the Lean corpus by mechanism; inspect complete theorem signatures and proof dependencies. Compile an explicit declaration/axiom audit in /tmp.
3. Verify primary literature and select defensible mathematical contributions. Draft standalone LaTeX with proofs, precise conditional statements, and open problems.
4. Compile PDF, inspect every page, conduct hostile logical and editorial review, resolve substantiated defects, and report any remaining submission blockers honestly.

## Evidence policy

Standard logical foundations (propext, Classical.choice, Quot.sound) are distinguished from unproved mathematical assumptions. A kernel-checked implication does not establish its hypothesis. No claim is promoted from a ledger label or file name. Working-tree changes predate this task and will be preserved.

## Log

- 2026-09-13 — Audit started. Frontier map has 2026-09-12 evidence cutoff; notes and working tree contain later changes and explicit retractions. No update_plan tool exposed; this card records the plan. Initial search: `scripts/formal_tools.py research 'Hawking extinction Riemann hypothesis' --json`.

- 2026-09-13 — User prohibits builds. Stopped owned Lake build process group 77240; session 33942 exited 143; process-group absence verified. No further Lean builds or compilation. Earlier build was incomplete and is not a certificate. Continue source/dependency audit and existing evidence. Author: Michael Haufschild; journal unspecified.
