# Different exponent consolidated (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Extension of module 38,
`EisensteinRootUniformizer.lean`.  See [[research/eisenstein_root_uniformizer_2026_08_06]].

## Added

- **`irreducible_of_addVal_eq_one`** — `addVal B x = 1 ⟹ Irreducible x`.  mathlib has only the
  converse (`addVal_uniformizer`).  Proof: `eq_unit_mul_pow_irreducible` gives `x = u * π^n`,
  valuation forces `n = 1`, then `associated_unit_mul_left … |>.symm.irreducible`.
- **`addVal_eval_derivative_of_eisenstein_root`** — the fully consolidated statement:
  for `ψ : A →+* B` of DVRs with ramification index `e`, `g : A[X]` Eisenstein monic of degree `e`,
  `e` a unit at the place, and **any** root `x` of `g.map ψ`,
  `addVal B (eval x (derivative (g.map ψ))) = e − 1`.

**Hypotheses are now only the extension and its Eisenstein presentation** — irreducibility of the
presented element and the coefficient bound upstairs are both derived.

## Arc summary for the different (modules 36–38)

1. Module 36 freed the computation from the constructed polynomial shape (any monic).
2. Module 37 derived the upstairs coefficient bound from Eisenstein-ness downstairs.
3. Module 38 derived irreducibility of the presented element from the presentation.

What remains is only the **existence** of an Eisenstein presentation (monogenicity of a totally
ramified extension — standard for complete DVRs, needs Hensel/completeness in Lean).

## Note

`formal_tools.py lint --check-generated` **passed cleanly** this round (no unwired modules from the
concurrent agent, no index staleness) — first clean gate in many iterations.
