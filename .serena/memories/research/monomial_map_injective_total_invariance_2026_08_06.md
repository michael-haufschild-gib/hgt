# Monomial map injectivity and total invariance (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **28**.
Closes the blocker recorded in [[research/toric_model_divisor_data_complete_2026_08_06]].

## `MonomialMapInjective.lean`

- `monomialMap_comp` — composing monomial maps **multiplies** exponents.
- `monomialMap_const_eq_expand` — the uniform monomial map **is** `MvPolynomial.expand`.
- **`monomialMap_injective`** — trick: with `E := ∏ e j`, compose with `fun i => E / e i` to get
  `expand E`, which mathlib proves injective (`MvPolynomial.expand_injective`); then
  `Function.Injective.of_comp`.  This sidesteps the missing
  `AlgebraicIndependent (fun i => X i ^ e i)` (mathlib has **no** power lemma for algebraic
  independence).
- `killCoord R σ i := aeval fun j => if j = i then 0 else X j`
- `sub_killCoord_mem_span` — `p − killCoord p ∈ span {X i}`, by `MvPolynomial.induction_on`.
- **`comap_bot_killCoord`** — `ker (killCoord i) = span {X i}`.
- `killCoord_comp_monomialMap` — the two **commute** (needs `e i ≥ 1` for the `zero_pow`).
- **`comap_monomialMap_span_X`** — a monomial map pulls each coordinate divisor back to itself.

That is **Theorem A condition (3), total invariance, proved outright** in the toric model, and it
supplies the divisor map `F` of the abstract ramification system there.

## Key mathlib finding

`MvPolynomial.expand n` (in `Mathlib/Algebra/MvPolynomial/Expand.lean`) is exactly
`aeval fun i => X i ^ n`, and `expand_injective (0 < n)` exists.  Reducing a varying-exponent
monomial map to `expand` is far cheaper than any direct monomial/Finsupp argument.

## Toric model status

Every ingredient of Theorem A is now proved in this model, none assumed:
`c = −1` (`formOrder_coordDivisor_log`), `e = e i` (`orderAt_coordDivisor_monomialMap_X`),
`ord J = e i − 1` (`orderAt_coordDivisor_det_jacobian`), eigenvolume condition
(`exists_unit_det_jacobian_mul_prod`), total invariance (`comap_monomialMap_span_X`).

## Remaining for Theorem A in general

1. Different exponent `e − 1` for a general tame extension.
2. Sheaf of differentials on a scheme.
3. Step 4's `e > 1`: `N¹` + int-amplification.
4. Corollary B: MMP.
