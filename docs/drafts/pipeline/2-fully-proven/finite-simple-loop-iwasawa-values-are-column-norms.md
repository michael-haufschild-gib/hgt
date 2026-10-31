# Finite simple loop Iwasawa values are column norms

- **Stage:** 2-fully-proven
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** For every coefficient-field `SL₂` matrix `g`, every actual
  integral–Borel factorization of its finite simple loop embedding has
  central valuation one and finite torus valuation
  `max(v(g₀₀),v(g₁₀))`. For the lower root parameter `x`, these are
  `(1,max(1,v(x)))`.

## Proof

Apply the audited upper-triangular–integral decomposition to `g⁻¹` and
invert both factors. This gives `g=kb` with `k` integral and `b` upper
triangular. The audited bottom-row value of the original decomposition
becomes `v(b₀₀)=max(v(g₀₀),v(g₁₀))`, by the determinant-one inverse formula.

The finite simple embedding sends `k` into the full integral loop group.
The embedded triangular matrix is the positive splitting of its constant
power-series matrix, with central factor one. Its finite Borel coordinate
is its constant upper-left entry. Thus this factorization has the stated
values. The audited uniqueness of both Borel valuations in the full loop
group gives the same values for every integral–Borel factorization.
Substitution of the lower elementary matrix gives `(1,max(1,v(x)))`.

This is a classical local identification, using `exists_valued_sl2_upper_integral`
and `borelValuationHom_iwasawa_unique`; no new analytic premise is introduced.

## Lean

`HTGeometry/LoopEisenstein/FiniteSimpleIwasawaValues.lean`. Direct check pending.
