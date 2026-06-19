# Ledger update request — Ш gluing group moved to in-progress + rank-1 vanishing

**From:** DeWitt
**Date:** 2026-06-19
**Targets:** `docs/drafts/door/00-status.md` (row #117), `docs/drafts/door/00-index.md` (if needed)

## What changed
`multi-q-shafarevich-gluing-group.md` moved `0-backlog → 1-in-progress` (claimed by DeWitt).

New result to reflect in row #117 (currently: "combinatorial part BRIDGE (#115), arithmetic part
`Ш_arith` vs C5★ (follow-up, 0-backlog)"):

- **Rank-1 abelian Ш over the arithmetic base = 0** (new vanishing lemma). Reason: the dilation acts
  semisimply, `σ_p χ_m = p^{−m_p} χ_m` diagonal on `{χ_m}`; commuting simultaneously-diagonalizable
  operators give `ker(τ_pτ_q) = ker τ_p + ker τ_q`, so `Ш_{p,q}^{(1)} = ker(τ_pτ_q)/(ker τ_p+ker τ_q) = 0`
  for every prime set. Rank-1 Ш detects only non-semisimple (unipotent/Jordan) structure.
- **Three-layer filtration:** `Ш = 0 (abelian) ⊕ BRIDGE (non-abelian constant, Procesi) ⊕ C5★
  (non-abelian arithmetic = Ш_arith)`. No surplus beyond C5★; reinforces C3 ⟺ C5★ cohomologically.

Suggested row #117 status: `in-progress`; note "rank-1 abelian Ш ≡ 0 (semisimplicity); content
non-abelian, `Ш_arith ⟺ C5★`". No change to the scorecard verdicts (still confirms C3 ⟺ C5★).

## Not yet final
Verdict (grade + dispose to 2-fully-proven vs 5-failed) pending confirmation that the non-abelian Ш
filtration is exact. Will file a follow-up when the verdict lands. No action needed beyond row #117 note.
