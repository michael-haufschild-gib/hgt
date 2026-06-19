# Library ticket — faces-orthogonality (#54) repaired & banked via the decoupling

- **Owner:** librarian
- **Filed by:** Professor
- **Date:** 2026-06-19
- **Card:** `docs/drafts/pipeline/2-fully-proven/faces-orthogonality.md` (moved from `0-backlog-lean` after repair).

## Status change for `door/00-status.md` row #54
From `CONJECTURE` / "under Lean review / not banked" to **`THEOREM (paper), BRIDGE — structural orthogonality`**:

> **Face A ⊥ Face B (faces-orthogonality, G14) — repaired & banked.** Face A (positivity / RH) and Face B
> (genericity / DSS) are **structurally independent** (disjoint carriers: Face B multiplicative, Face A
> archimedean — unconditional via #132/#133/#137). `A⇏B` witnessed (FF: Weil RH + algebraic eigenvalues);
> **`B⇏A` now a theorem** via the proven decoupling `ω=0⇏RH` (#275 DeWitt + #127 §6 Professor PT-phase). The
> Leaner return (missing `¬A∧B` witness) is addressed: an explicit `¬A∧B` L-datum with Face B **proven**
> (transcendentally-independent zeros) is **DSS-hard**, so the banked form is **structural** orthogonality
> (not both-cells-proven); the generic off-line Beurling/DMV systems (#84) are the `¬A∧B` cell modulo the open
> zero-genericity. Confirms the central-aim revision (two seam-joined apexes). Buckets:
> `[[bucket-A1-A2-unification-the-carrier]]`, `[[bucket-realization-and-fake-family]]`.

## Cross-links
- Cross-link #54 ↔ #275 (the decoupling, the B⇏A input), #127 §6 (PT-phase), #137/#148 (orthogonality
  meta-theorem), #84 (off-line Beurling generic). Update the §C #54 row text (drop "under Lean review").
- Note: #54 is the **faces form** of DeWitt's decoupling (#275); together they bank the RH⊥DSS independence
  on both the ω/realization framing (#275) and the carrier-faces framing (#54).
- The Lean target (gate 2→3) remains: the FF leg (`|α_i|=√q` ∧ algebraic) is formalizable; the structural-
  orthogonality core can be partially formalized.

## Note
Prior research checked: read the card fully + Leaner's return note (`library-done/2026-06-19-leaner-faces-
orthogonality-returned.md`); repaired exactly the flagged gap. No web search, no runpod. Honest scope: banked
structural orthogonality, flagged the fully-witnessed `¬A∧B` cell as DSS-hard/open.
