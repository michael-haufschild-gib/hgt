# Irregular-RH Stage-3 promotion sweep — 2026-08-27

Promoted all 18 cards formerly under `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/irregular-rh-foundations/` to the matching Stage-3 directory after exact card-to-Lean audits.

Verification:
- Mandatory corpus search used `scripts/formal_tools.py research`.
- Direct `lake env lean` checks passed sequentially for 15 distinct leaf modules (including `StokesOrdinaryEpigraphConvolution` plus 14 dependencies/card modules).
- One targeted `lake build` over those leaf modules passed; no umbrella build.
- `scripts/formal_tools.py lint` passed after moves.
- No axiom checks rerun because no Lean declarations were created; every card already carried its completed new-declaration axiom audit.
- No stale Lean/Lake process remained.

Cards updated to Stage 3 / `[LEAN-PROVED]` as appropriate; historical lint-blocker text removed or dated. Stage-2 irregular-RH foundation directory is now empty.

Worktree had extensive unrelated pre-existing edits in HTGeometry/RHTower modules; none were touched. No commit/push.