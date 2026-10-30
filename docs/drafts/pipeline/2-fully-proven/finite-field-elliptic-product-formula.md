# Product formula for the actual elliptic function field over F₃

- **ID:** finite-field-elliptic-product-formula
- **Stage:** 2-fully-proven
- **Statement:** Normalize each affine prime valuation by the cardinality of
  its actual residue field and the infinity valuation by `3`. Every nonzero
  element of the function field of `y²=x³−x` then has product of all place
  magnitudes equal to `1`; only finitely many factors differ from `1`.

## Proof

For a nonzero affine function `a`, unique ideal factorization gives
`(a)=∏v v^ord_v(a)`. Multiplicativity of actual finite quotient cardinalities
therefore gives
`∏v #k(v)^ord_v(a)=#(A/(a))`.
The established Smith decomposition identifies this cardinality with
`3^deg(norm(a))`. The established infinity valuation has exponent
`deg(norm(a))`, so its magnitude cancels the finite-place product exactly.

The support is finite because a nonzero principal ideal has finitely many
prime ideal divisors. Every nonzero function-field element is `a/b` with
nonzero affine `a,b`. Multiplicativity of all valuations gives the quotient
of their two product formulas, and the support lies in the union of their
finite supports. The affine coordinate ring is canonically the previously
constructed integral closure; these are the actual places of the curve.

## Verification

Lean formalization in progress.
