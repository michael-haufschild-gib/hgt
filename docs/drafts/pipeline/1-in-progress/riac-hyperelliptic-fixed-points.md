# Actual hyperelliptic Frobenius fixed points

- **ID:** RIAC-hyperelliptic-fixed-points
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [Curve orientation counts](riac-curve-orientation-square-root.md)
- **Statement:** For finite fields `F⊂E`, `d>0` dividing `[E:F]`, the actual fixed points of `Frob_F^d` on `y²=f(x)` with infinity are equivalent to points over the degree-`d` extension of `F`.

## Construction

Choose an actual embedding `K→ₐ[F]E`, where `[K:F]=d`. Its image is
exactly the fixed set of `Frob_F^d`: on `E` this power is `x↦x^(#K)`,
the generator of `Gal(E/K)`. An element fixed by that generator is fixed
by the whole Galois group and therefore lies in `K`. Restrict the
coordinatewise embedding to the equation `y²=f(x)` and retain infinity.

The existing extension character-sum theorem then identifies the fixed
count with `q^d+1−Σ α_i^d` for odd-degree `f`. No Weil-circle or
cancellation estimate is an input to this comparison.

## Remaining obligation

Formalize the field and point equivalences, their cardinalities, and the
actual root-power-sum formula. The subsequent signed cycle-index identity
is separate. This comparison alone gives no integer-cutoff bound for
`Σ_p index_p(N)=1−M(N)`.
