# Hasse's theorem for elliptic curves over finite fields of odd characteristic

- **ID:** aet-hasse-elliptic-odd
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** card `rh-odd-hyperelliptic-curves-all-finite-fields.md`; AET README §10 calibration
  ("Hasse in genus one")
- **Statement:** `W` elliptic over a finite field `F`, `ringChar F ≠ 2`, `q = |F|`:
  `|#W(F) − (q + 1)| ≤ 2√q` (mathlib's `W.toAffine.Point`). At a place of good reduction with odd
  residue characteristic, the trace of mathlib's local polynomial `1 − aT + qT²` has `|a| ≤ 2√q`.

## Proof
`(2y + a₁x + a₃)² = 4x³ + b₂x² + 2b₄x + b₆ =: g(x)`; `disc g = 16Δ ≠ 0`, so `g` has distinct roots
in its splitting field (`Cubic.discr_ne_zero_iff_roots_nodup`), is separable, squarefree, of degree
3. `pointEquiv`: `#W(F) = 1 + #{W(x, y) = 0} = 1 + #{y'² = g(x)}`; apply the odd-degree Hasse–Weil
bound with `m − 1 = 2`.

## Lean
`RHTower/EllipticCurveHasseBound.lean`: `equation_iff_sq_eq`, `squarefree_twoTorsionPoly`,
`card_equation_eq`, `abs_natCard_point_sub_le`, `abs_localTrace_le`. Axioms: propext, choice,
Quot.sound.

## Log
- 2026-10-27 — formalized.
