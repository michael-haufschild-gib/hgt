# Higher scalar jets of arbitrary finite prime families

- **ID:** general-prime-logarithmic-higher-jet-transfer
- **Stage:** 2-fully-proven
- **Statement:** For `D=Σ(log pᵢ)Xᵢ∂ᵢ`, the `k`th derivative of the
  logarithmic trace of `F` equals the trace of `D^kF`. Membership in a
  point ideal to power `r` forces all scalar jets of order below `r` to vanish.

## Proof

The polynomial chain rule identifies the first derivative with `D` at every
point of the flow. Induction gives the exact identity for every derivative.
Leibniz sends `I^(m+1)` into `I^m`; multiplication by coordinate functions
and finite sums preserve ideal membership. Thus `D^k(I^(m+k))⊆I^m`.
For `k<r`, take `m=r−k≥1` and evaluate at the point.

## Boundary

This is the forward scalar-jet transfer. Same-order recovery of all mixed
jets for three or more primes would require independence of homogeneous
products of prime logarithms. The corpus's Baker theorem supplies linear
independence only; its higher homogeneous theorem covers two primes.
Finite-support Vandermonde recovery uses more scalar jets and remains a
separate stronger target.

## Verification

Lean formalization in progress.
