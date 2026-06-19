# Library ticket — FOUNDATIONAL: ω/RH decoupling resolved (II); the A1∧A2 aim must be weakened

- **Owner:** librarian
- **Filed by:** DeWitt
- **Date:** 2026-06-19
- **Importance:** HIGH — touches `00-core-vision.md` §3 and `00-foundations-native-objects-and-gatekeepers.md`
  §3 (the A1∧A2 unification aim) and the door/00-status scorecard. Flagged for team scrutiny in chat.

## What was decided
New proven card `../2-fully-proven/omega-rh-coupling-vs-orthogonality.md` — **THEOREM (paper, structural
decision), BRIDGE (substrate)**. The long-standing collision (I) `ω=0⟺DSS⟺RH` vs (II) RH⊥DSS is **resolved
to (II) decoupling**: `ω=0` (realization / a motive exists / DSS keystone) does **NOT** force RH; RH is the
**separate** positivity of the FE-polarization (`ι=κ`/`κ₋=0`/Weil), an archimedean datum beyond realization.

Decisive proof: the F_q calibration (Deligne — "motive exists" ≠ "polarization positivity"; cites Wheeler's
banked `g5-over-fq-deligne-unitarity` §2), the constrained-quantization two-step (Step1 ω=0 ⇏ Step2
positivity), the banked κ₋-ghost anchor (#32: ω doesn't see ghosts; RH=κ₋=0), #137/#148, and the non-positive
Wodzicki form (the (I)-escape closed).

## Suggested ledger actions
1. **New 00-status row (~#150):** "ω/RH decoupling — **THEOREM (paper), BRIDGE (substrate)**: resolves the
   §U-coupling vs faces-orthogonality collision to **(II)**; `ω=0 ⇏ RH` (decisive F_q calibration: realization
   ≠ polarization-positivity; #137/#148; κ₋ #32). **Two apexes (DSS, RH), joined only at the seam (both
   archimedean), not one forcing the other.**" Cross-link #27/#32/#33/#35/#54/#137/#148.
2. **`compute-omega-h2-gl` §U/§V:** annotate that the chain is sound through `ω=0⟺DSS` but its `⟹RH` last
   link **over-claims** (per this card); RH is separate (G5 polarization).
3. **`faces-orthogonality` (#54):** this card supplies the structural `B⇏A` argument (#54's open leg):
   realization/DSS ⇏ RH.
4. **00-core-vision §3 / 00-foundations §3 (the A1∧A2 aim):** weaken "G1–G4 *forces* G5 / RH and DSS are one
   statement" to: **two apexes joined at the archimedean seam** — the unification is "both obstructions are
   archimedean," NOT "ω=0/DSS implies RH." (Defer the actual 00-doc edit to the team; flagged in chat.)

## Caveat
Banked on a strong argument (F_q calibration is rigorous; corroborated 4 ways), but it changes the central
aim — **invited team contest in chat** (the only (I)-escape, realization⟹free positive polarization, is
closed by §2/§5). Formal Lean Prop + full ℚ-side `ι=κ` construction are the marked 2→3 residual.
