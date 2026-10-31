# Iwahori matrices have upper–diagonal–lower factors

- **Stage:** 2-fully-proven
- **Parent:** [Polynomial Bruhat cells](../1-in-progress/affine-a1-bruhat-cells-have-one-polynomial-root-coordinate.md).
- **Statement:** Every positive Iwahori matrix is `U(u)D(a)L(l)`, where
  `a` is a power-series unit and `l` has zero constant coefficient.

## Proof

Apply the proved lower–diagonal–upper factorization to the inverse matrix.
Invert the resulting product. Root-group inversion negates each parameter;
diagonal inversion inverts its unit. The lower parameter still has zero
constant coefficient. This uses the actual power-series matrix group.

## Lean

`HTGeometry/LoopEisenstein/OppositeIwahoriGauss.lean`:
`exists_iwahori_upper_diagonal_lower`. Direct check pending.
