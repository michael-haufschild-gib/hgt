# The `e − 1` verified in the local model (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **25**.
Continues [[research/kaehler_jacobian_top_form_2026_08_06]].

## `TamePowerMapRamification.lean`

- `powMap R σ e := aeval fun i => X i ^ e` — the coordinatewise power map, local model of a
  totally ramified cover of index `e`.
- `jacobian_powMap` — the Jacobian is `Matrix.diagonal fun i => (e : MvPolynomial σ R) * X i^(e−1)`.
- `det_jacobian_powMap` — `det = ∏ i, e * X i^(e−1)`.
- **`det_jacobian_powMap_eq_unit_mul`** — if `IsUnit (e : R)` then
  `det = u * (∏ i, X i)^(e−1)` for a unit `u`.  So the **order along each coordinate divisor is
  exactly `e − 1`**: this is card equation (8)'s shift, verified.
- `exteriorPower_pullbackDifferential_powMap` — the same statement on top differential forms.

**Tameness is essential, not cosmetic**: in the wild case `(e : R)` is not a unit and the order of
the Jacobian determinant is strictly larger than `e − 1`.  This is the honest boundary of the
card's equation (8).

## Lean traps

- `ext i j` on a `Matrix (MvPolynomial …)` goal **over-applies** — it descends into
  `MvPolynomial.ext` and leaves `coeff m _ = coeff m _`, after which every `rw` fails with a
  confusing "not type-correct under instances transparency" note.  Use
  `refine Matrix.ext fun i j => ?_`.
- `MvPolynomial.pderiv_X_of_ne {i j} (h : j ≠ i) : pderiv i (X j) = 0` — the hypothesis is
  **reversed** relative to the indices in the conclusion.  To rewrite `pderiv j (X i)` supply
  `Ne.symm h` where `h : j ≠ i`.  `Matrix.diagonal_apply_ne` wants `Ne.symm h` too, so both
  arguments look identical but for opposite reasons.

## Remaining for Theorem A

1. The different exponent `e − 1` for a **general** tame extension (beyond the Eisenstein
   presentation and beyond this power-map model).
2. Sheaf of differentials on a scheme — mathlib has only ring-level `KaehlerDifferential`.
3. Step 4's `e > 1`: `N¹` + int-amplification.
4. Corollary B: MMP.

## Repo hazard

Untracked unwired modules from a concurrent agent this round:
`HTGeometry.LastVariableJetLift`, `HTGeometry.PhaseRankFromAutonomousEquation`.
