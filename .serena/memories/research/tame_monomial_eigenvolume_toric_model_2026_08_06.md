# The toric model of Theorem A (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **26**.
Continues [[research/tame_power_map_ramification_2026_08_06]].

## `TameMonomialEigenvolume.lean`

`monomialMap R σ e := aeval fun i => X i ^ e i` — **per-coordinate exponents**, so the ramification
index varies from divisor to divisor exactly as `e_E` does in the card.

- `jacobian_monomialMap` — diagonal, entries `(e i) * X i^(e i − 1)`.
- `det_jacobian_monomialMap`
- **`det_jacobian_monomialMap_eq_unit_mul`** (tame: `∀ i, IsUnit ((e i : R))`) —
  `det = u * ∏ X i^(e i − 1)`, i.e. the **ramification divisor** `R_f = Σ (e_i − 1) E_i`.
- `monomialMap_prod_X`, `prod_pow_sub_one_mul_prod`
- **`exists_unit_det_jacobian_mul_prod`** — `det(Jac) * ∏ X i = u * φ(∏ X i)`, i.e. the
  **logarithmic volume form `∏ x_i^{-1} dx` is an eigenvolume**, its horizon is the union of the
  coordinate hyperplanes, order `−1` on each.

**This is Theorem A realised in the toric case** — it shows the general theorem's hypotheses
(eigenvolume condition, Jacobian order `e − 1`, horizon reduced) are simultaneously satisfiable
and sharp.

## Lean traps

- `IsUnit.prod` does **not** exist as expected — the name resolves to `Function.prod` and produces
  a bizarre universe-constraint error.  Use
  `Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one ?_`.
- `Nat.succ_pred_eq_of_pos` will not rewrite `e i - 1 + 1` (the pattern is `(e i).pred.succ`).
  Use `Nat.sub_add_cancel (he i)`.

## Repo hazard — cascading collision

Concurrent agent's untracked `LastVariableJetLift.jetLift` collided with the tracked
`GenericJetAlgebra.jetLift`, breaking the shared umbrella.  Renamed the newcomer to
`lastVariableJetLift` — which then broke **their own untracked consumer**
`PhaseRankFromAutonomousEquation.lean`, so that file needed the same rename.
Lesson: after renaming to fix a collision, `grep` for consumers of the old name before rebuilding.
Note `\bjetLift\b` does **not** match inside `eval_jetLift` / `jetRelationEval_jetLift`
(underscore is a word character), which is what kept those names stable.
