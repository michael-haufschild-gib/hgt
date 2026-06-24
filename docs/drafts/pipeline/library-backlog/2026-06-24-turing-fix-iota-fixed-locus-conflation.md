# Ticket: correct the systemic "Fix(ι) = critical line" conflation (door rows + framing cards)

- **Filed:** 2026-06-24 (Turing)
- **Type:** ledger/door correction — propagated mathematical mis-identification
- **Severity:** real error, but local relabeling (no proof/grade collapse)

## The error
For the FE involution ι : s ↦ 1−s, **Fix(ι) = {s : 1−s = s} = {½}** — a single point. The **critical line**
{Re s = ½} is **Fix(ι∘conj)** (the conjugate constraint s ↦ 1−s̄: s = 1−s̄ ⟺ s+s̄ = 1 ⟺ Re s = ½).
Multiple cards write "Fix(ι) = {Re=½} = critical line", conflating ι with ι∘conj.

## Ground truth (already correct)
- Lean: `sigma_fixed_iff_eq_half` (σ(s)=s ↔ s=½, the POINT) and `sigmaConj_fixed_iff_critical`
  (σ∘conj fixed ↔ Re=½, the LINE). SigmaOrbit.lean docstring states it explicitly.
- Card `3-formalized/fe-constraint-critical-line-fixed-locus.md` — prose CORRECT (sigmaConj fixes the line).

## To correct (door + framing cards write Fix(ι)=critical line; should be Fix(ι∘conj))
- `door/00-status.md` rows #127, #136, #138 — "Fix(ι)={Re=½}" / "constraint surface Fix(ι)".
- `2-fully-proven/constraint-not-flow-theorem.md` §3 — already annotated with the correction by Turing.
- `0-backlog/completed-connection-category.md` — multiple lines, incl. line 56 with the explicit wrong
  derivation "Fix(ι)={s:1−s=s}={Re=½}" (the LHS = {½}, not {Re=½}).
- `0-backlog/moonshot-dbn-cosmological-constant-wdw.md` — "constraint surface Fix(ι)={Re=½}".
- `0-backlog/moonshot-arithmetic-bulk-hyperbolic.md` — "Fix(ι) is its boundary-at-infinity".

## The fix (everywhere)
Replace "Fix(ι) = {Re=½} = critical line / constraint surface" with: **the critical line / constraint
surface = Fix(ι∘conj)**; the FE involution ι itself fixes only the center point Fix(ι) = {½}. The zeros γ_n
and RH live on Fix(ι∘conj). The "constraint not flow" thrust is unaffected (ι is still order-2 ℤ/2, not an
ℝ flow); only the locus label changes.
