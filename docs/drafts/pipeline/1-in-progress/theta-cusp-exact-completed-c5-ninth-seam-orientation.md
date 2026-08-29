# Exact Completed C5 Ninth-Seam Orientation

- **ID:** CLG-TTF-C5-exact-seam-nine
- **Stage:** 1-in-progress
- **Type:** FORMALISED REDUCTION / OPEN GLOBAL MONOTONICITY / ROUTE FALSIFIER
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

- [x] Prove source-independent exact cleared-expression ninth-jet classification in `HTGeometry`.
- [x] Instantiate it with the literal completed theta source and prove the connector to `c5CompletedCompensationMargin`.
- [ ] Prove or falsify `Ω>0` using corpus modular-ODE/source-positive coordinates, without numerical computation.
- [x] Derive punctured compensation/direct-J positivity from `Ω>0`, and prove this chamber unconditionally for all sufficiently small positive centres.

## Log

- 2026-08-29 — Conjecture extracted from corpus exact residual split after formal adaptive fifth-seam no-go. Explicit RH passport and route-kill criterion fixed before proof attempt.
- 2026-08-29 — Formalised universal cancellation through order eight and exact ninth jet `80640 Ω`; connected cleared germ to literal completed margin and direct-J iff.
- 2026-08-29 — Discovered and formalised decisive projective reduction. With
  `K₆=A*C-B²-18*A²*B+24*A⁴`, exactly
  `Ω=A*K₆'-4*A'*K₆=A⁵*(K₆/A⁴)'`. Corpus already proves `A>0` and `K₆>0`, so the remaining global burden is strict increase of the normalized positive sixth curvature, not a free seven-jet inequality.
- 2026-08-29 — Formalised arbitrary-centre slope
  `Ω' = A²D-5ABC+4B³-18A³C+36A²B²-AEG+6BEF-2AF²-3CE²-18A²EF+72ABE²`.
  At the modular centre all odd corrections vanish, so existing theorem `thetaCuspC5FixedActionSeamLogValue_pos` gives `Ω'(0)>0`. Hence `Ω(u)>0` for every sufficiently small `u>0`, and each such centre has a punctured positive literal direct-J displacement chamber.
- 2026-08-29 — Open core sharpened: prove or refute strict projective monotonicity of `thetaCuspC5ExactSeamSixthInvariant / thetaCuspLogCurvature^4` on the full positive orbit. One nonpositive derivative value kills this direct-J seam route at that centre; global strict positivity closes its local mathematical burden.
- 2026-08-29 — Killed chamber-only slope proof. The odd-corrected exact C5 slope polynomial admits a state with strict `U,B,Q>0` and strict reconstructed gap but negative value; `not_forall_strictSourcePositiveChamber_c5ExactCompletedSeamSlope_pos` formally refutes the universal sign implication. Therefore abstract source-positive coordinate inequalities cannot establish global `Ω'>0`. Positive survivor is exact seam factorization into `normalizedSourceJet(0)^6` times the fixed-action C5 seam polynomial; remaining attack must use actual modular-orbit incidence/dynamics or a stronger orbit invariant. See `../3-formalized/theta-cusp-exact-completed-c5-slope-chamber-no-go.md`.
