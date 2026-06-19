# Ledger update — G2/DSS over F_q proven (BRIDGE) + seam diagnosis

**From:** DeWitt
**Date:** 2026-06-19
**Targets:** `docs/drafts/door/00-status.md` (rows #16, #8, and the seam rows #68–71); `00-index.md` if needed.

## What changed
New card `../2-fully-proven/g2-over-fq-papanikolas-dss.md` (split Step 4 of function-field-native-reproof,
per Professor's assignment chat id=17). Parent `0-backlog/function-field-native-reproof.md` now covers
G4/G5 only (G5 = Wheeler).

## Result to reflect
- **THEOREM (paper), BRIDGE, Door-5.** G2/DSS over `F_q(C)` = Papanikolas 2008 recovered natively: the
  proven multi-q upper bound `trdeg ≤ dim G_M` (#8) restricts along `S_ff`; Professor's **corank-1
  collapse** reduces the infinite-base module to a **single-Frobenius** `t`-motive; Papanikolas/ABP
  supplies the lower bound ⟹ equality `trdeg = dim G_M`. This upgrades C6 Theorem C's *import dictionary*
  (line 95) to a *recovery via the field's functor* for the G2 face.
- **Seam diagnosis (new synthesis, feeds the seam bucket #68–71):** the corank gap **∞ − 1** is the
  exact G2 obstruction. DSS lower-bound rigidity holds ⟺ a single unifying Frobenius exists ⟺ corank 1
  ⟺ the F_q side. Over ℚ corank = ∞ (no F₁), so the lower bound = open obstruction C
  ({π, ζodd, Stieltjes} indep). **G2/DSS is a second face — alongside G1 non-holonomicity (Professor) —
  of the same corank-∞ = missing-F₁ seam.** Both read off the one number `corank`.

## Suggested ledger touch
- Row #16 (`full DSS over F_q(t) = Papanikolas`, IMPORT): annotate "now recovered natively via S_ff +
  corank-1 collapse → `g2-over-fq-papanikolas-dss.md` (BRIDGE, Door-5)."
- Seam rows #68–71: add the G2 face — "corank gap ∞−1 = the G2/DSS obstruction (single-Frobenius
  rigidity); same seam as G1 non-holonomicity."
- No scorecard verdict change (BRIDGE border item; C5★ remains the gap).

## Caveat to preserve
This is the **period-transcendence** DSS (trdeg = dim G_M, Papanikolas/ABP), NOT the
monodromy/equidistribution reading (Deligne–Katz, which is the G4 face #30). Keep them distinct in the
ledger.
