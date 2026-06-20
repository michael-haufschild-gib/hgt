# Library update request — DeWitt, 2026-06-19 — sigma-parity-fe-weld resolved (honestly scoped)

Informal ticket for the librarian to fold into `door/00-status.md` (row #49) and `door/00-index.md`.

## Pipeline move
`sigma-parity-fe-weld.md`: `0-backlog-lean → 3-formalized` (Leaner's return closed by honest scoping, option b).

## What changed (statement corrected, Lean unchanged)
The card claimed σ-parity grading **= FE-parity grading** (a weld/equivalence). That isomorphism **does not
exist**: the σ-parity is on the **exterior** algebra `∧^•V` (`∧^k(−id)=(−1)^k`, antisymmetric, bounded by
`dim V`); the FE-moment parity is on the **symmetric/polynomial** Taylor moments `t^k` at `s=½` (unbounded).
Different symmetry types/dimensions ⟹ no natural `∧^k V ≅ moment_k`.

Corrected (and proven, axiom-clean) statement: a **single order-2 FE involution `ι`** (`=−id` on the centered
direction) induces **both** `(−1)^k` on `∧^•V` (`exteriorPower_map_neg_id`) and odd-moment vanishing
(`fe_odd_moment_vanish`, `fe_centered_odd_moment_vanish`). The D2-substrate content is the **shared source**
(one involution, two parent-faces), not a graded isomorphism; the explicit formula is the analytic bridge (an
identity, not a grading iso). Grade unchanged: **BRIDGE (substrate)**.

## Status
Row #49 should read: σ-parity/FE-parity = **shared-source D2 unification** (one FE involution), **not** a
grading equivalence. The two parity lemmas are the axiom-clean Lean certificate. Card now in `3-formalized`
(Leaner re-audit pending; Lean content unchanged, only the paper claim scoped honestly).

No edits by me to `00-status.md`/`00-index.md` (race-avoidance rule).
