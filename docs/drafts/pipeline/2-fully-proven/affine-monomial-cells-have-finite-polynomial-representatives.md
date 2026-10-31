# Affine monomial cells have finite polynomial representatives

- **Stage:** 2-fully-proven
- **Parent:** [Arithmetic cell coordinates](../1-in-progress/affine-a1-bruhat-cells-have-one-polynomial-root-coordinate.md).
- **Statement:** The remaining negative translation and both reflection families
  have finite polynomial representatives modulo the right Iwahori.

## Proof

Write an Iwahori matrix in upper–diagonal–lower or lower–diagonal–upper
Gauss order. Its upper parameter is an arbitrary power series; its lower
parameter is divisible by `X`; its diagonal parameter is a power-series unit.
For a threshold `N`, exact truncation gives `u=p+X^N t`, with `deg p<N`.
For a lower parameter it gives `l=Xp+X^(N+1)t`.

For `v=X^n`, the negative translation `D(v⁻¹)` sends the lower tail back
into the strictly integral lower root and multiplies the residual upper
parameter by `v²`. Thus `L(Xp)D(X^(-n))` is a representative with `deg p<2n`.

For `W(v⁻¹)=[[0,-v],[v⁻¹,0]]`, conjugation swaps root directions and
changes their signs. Truncating the upper parameter at `2n+1` leaves
`U(p)W(X^(-n))`; the residual lower parameter is `-Xt`, hence strictly
integral, and the residual upper parameter is `-X^(2n)l`, hence integral.

For `W(X^(n+1))`, truncate the lower parameter at `2n+2`. The representative
is `L(Xp)W(X^(n+1))`, with `deg p<2n+1`; the residual upper parameter is
`-t`, while the residual lower parameter is `-X^(2n+2)u`. The latter has
zero constant coefficient. In every case, the residual diagonal remains
a power-series unit. Entrywise Iwahori criteria finish the proof.

## Lean

`HTGeometry/LoopEisenstein/AffinePolynomialCells.lean`:
`exists_lower_polynomial_translation_cell`,
`exists_upper_polynomial_reflection_cell`,
`exists_lower_polynomial_reflection_cell`. Direct audit pending.

The positive translation family is already audited. Uniqueness and actual
arithmetic restriction remain separate obligations on the parent card.
