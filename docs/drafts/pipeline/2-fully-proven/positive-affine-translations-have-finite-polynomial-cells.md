# Positive affine translations have finite polynomial cells

- **Stage:** 2-fully-proven
- **Parent:** [Polynomial root cells](../1-in-progress/affine-a1-bruhat-cells-have-one-polynomial-root-coordinate.md).
- **Statement:** For every field `F`, natural `n` and `g` in the positive
  Iwahori subgroup, there are `p∈F[X]` of degree below `2n` and `j∈I`
  with `g D(X^n)=U(p)D(X^n)j`.

## Proof

Write `g=U(u)D(a)L(l)`, with `u,l∈F[[X]]`, `a` a power-series unit
and `l(0)=0`. Exact truncation gives `u=p+X^(2n)t`, `deg p<2n`.
The root conjugation identities give

`g D(X^n)=U(p)D(X^n)[U(t)D(a)L(X^(2n)l)]`.

The bracket lies in Iwahori: the upper parameter is integral, the diagonal
is a power-series unit and the lower parameter has zero constant term.
This includes `n=0`, where `p=0`.

## Lean

`HTGeometry/LoopEisenstein/PositiveTranslationPolynomialCells.lean`:
`exists_upper_polynomial_translation_cell`. Direct audit pending.
