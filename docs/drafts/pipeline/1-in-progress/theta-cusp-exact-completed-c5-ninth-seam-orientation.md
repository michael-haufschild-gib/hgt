# Exact Completed C5 Ninth-Seam Orientation

- **ID:** CLG-TTF-C5-exact-seam-nine
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / ROUTE FALSIFIER
- **Source:** Corpus split `c5CompletedCompensationMargin_eq_adaptive_add_residual`, the adaptive fifth-seam no-go, and direct-J equivalence `thetaCuspReflectedActionC5FixedActionJacobian_pos_iff_completedCompensation`

## RH proof chain

`exact ninth-seam source orientation Ω > 0`
→ punctured positivity of literal completed C5 compensation at every positive centre
→ local direct fixed-action Jacobian orientation
→ compact/far-tail assembly
→ fixed-action seam and reflection-odd rank-four/Ptolemy wall
→ cofinal no-escape
→ CLG/TTF or Weil-polarization positivity
→ RH.

Failure of `Ω > 0` at any positive centre kills this direct-J seam route there. Proving it removes every lower-order seam term and reduces the local seam burden to one explicit completed-source differential polynomial.

## Corpus-grounded conjecture

Let `L = thetaCuspLogSource` and, at a positive centre `u`, put

- `A = -L₂(u)`, `B = -L₄(u)`, `C = -L₆(u)`;
- `E = -L₃(u)`, `F = -L₅(u)`, `G = -L₇(u)`.

Define

`Ω = A²G - 3ACE - 2ABF + 4B²E - 18A³F + 36A²BE`.

For the division-free literal completed-compensation seam germ

`D_full(u,t) = (exp(thetaCuspReflectedLogAction u t)-1) * c5CompletedCompensationMargin u t`,

conjecture:

1. `D_full^(k)(u,0)=0` for every `k<9`;
2. `D_full^(9)(u,0)=80640 Ω(u)`;
3. `Ω(u)>0` for every `u>0`.

## Why order nine

Corpus theorem `c5CompletedCompensationMargin_eq_adaptive_add_residual` restores exactly the third likelihood channel omitted by the adaptive lower margin. Its leading seam term cancels the proved negative fifth adaptive defect. Writing the exact velocity-centre numerator as `H`, direct differentiation gives the structural identity `P = H + t H'` for the full velocity-slope numerator. The C5 coefficients then cancel the apparent seventh-order cleared term as well. The first possible survivor is order nine and depends only on source jets through order seven.

## Attack

- [ ] Prove source-independent exact cleared-expression ninth-jet classification in `HTGeometry`.
- [ ] Instantiate it with the literal completed theta source and prove the connector to `c5CompletedCompensationMargin`.
- [ ] Prove or falsify `Ω>0` using corpus modular-ODE/source-positive coordinates, without numerical computation.
- [ ] If positive, derive punctured seam positivity and direct-J orientation; if negative, close route with exact counter-orientation and strongest positive survivor.

## Log

- 2026-08-29 — Conjecture extracted from corpus exact residual split after formal adaptive fifth-seam no-go. Explicit RH passport and route-kill criterion fixed before proof attempt.
