# Polynomial translation corrections cannot lower the slope index

- **ID:** HAAR-POLYNOMIAL-SLOPE-INDEX-MONOTONICITY
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Relative Haar splitting](../1-in-progress/finite-index-haar-carriers-split-modulo-polynomial-kernels.md)
- **Statement:** If `p` is positive definite with integer Haar successor, `ψ` is Hermitian on `ℚˣ`, and `Q` is Hermitian with polynomial translation fibres and zero dilation reading, then
  `κ(ψ) ≤ κ(p+ψ∘slope+Q) ≤ κ(ψ)+κ(Q)`.

## Proof

The [polynomial-fibre index equality](haar-addition-preserves-index-on-polynomial-translation-fibres.md)
gives `κ(p+ψ∘slope+Q)=κ(ψ∘slope+Q)`. Its signed finite-difference quadrature
reproduces every polynomial Gram entry while the positive Haar Gram tends to zero.
Restrict the residual kernel to dilations: `Q` vanishes there, so its restriction
is exactly `ψ`. Restriction cannot increase negative index, giving the lower bound.
Subadditivity and pullback along slope give the upper bound.

Polynomial corrections therefore cannot remove slope negative directions. No
additivity formula is asserted: slope and polynomial directions can overlap.

## Lean formalization

`AdelicKreinGeometry/Haar/PolynomialIndexPreservation.lean` proves
`negIndex_slope_le_positive_haar_polynomial` and
`negIndex_positive_haar_slope_polynomial_le`. The direct `lake --old env lean`
audit passed; both transitive axiom closures are exactly `propext`,
`Classical.choice`, and `Quot.sound`.
