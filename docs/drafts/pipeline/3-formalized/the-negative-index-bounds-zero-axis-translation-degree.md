# The negative index bounds zero-axis translation degree

- **ID:** ZERO-AXIS-TRANSLATION-DEGREE
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Axis-invisible affine polynomials](axis-invisible-affine-polynomials-realize-arbitrary-finite-index.md)
- **Statement:** Let `k:Aff(ℚ)→ℂ` be nonzero and Hermitian, vanish on translations and dilations, and have negative index at most `r<∞`. For every slope `u`, a polynomial of degree below `r` equals `k(T_bD_u)` at every rational `b`.

## Dependency-closed paper proof

Let `V` be the full column space and `W` the span of its translation columns. The [zero-axis rank law](../3-formalized/axis-invisible-finite-index-kernels-have-finite-rank.md) makes `V` finite-dimensional; its subgroup-generator theorem gives `m=dim W≤r`. The identity column is nonzero because `k` is nonzero, so `m>0`.

Every translation preserves `W`. The affine representation on `V` makes each translation unipotent. Restriction to `W` preserves nilpotence, and Cayley–Hamilton bounds its exponent by `m`. Thus `b↦L_(T_(b/u))|W` is a rational one-parameter representation with uniform nilpotence exponent `m`.

Observe a column at `D_u⁻¹`. Applied to the orbit of the identity column, this reads `k(D_uT_(b/u))=k(T_bD_u)`. The [rational Newton-polynomial argument](finite-rank-affine-kernels-have-polynomial-translation-fibres.md) gives degree below `m`, hence below `r`.

## Lean and scope

`HeckeKreinToeplitz/Index/SubgroupColumns.lean` proves the subgroup action, its dimension bound, and restriction of ambient nilpotence. `AdelicKreinGeometry/Haar/PolynomialPerturbations.lean` proves `exists_polynomial_translation_fibre_lt_index`.

Both direct source checks pass. All five public axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`. Both programme umbrellas import the leaves.

This strengthens the dimension-based polynomial bound for zero-axis kernels. It does not construct a decomposition of a general Haar-successor carrier.
