# Full-theta aperture-weighted pair remainder

- **Stage:** 2-fully-proven
- **Type:** THEOREM; Lean pending
- **Wall:** Σ6

Let `T_nm(r,b)` be the literal ordinary-pair Fourier tail and `T(r,b)` the
complete-source tail. Put `w_a(r)=sinh(ar)+ar cosh(ar)`,
`P_nm(a,b)=∫_(r>0)w_a(r)T_nm(r,b)dr`, and
`H(a,b)=∫_(r>0)w_a(r)T(r,b)dr`.
For `0≤a<1/2`, real `b`, and integer `M≥0`,

`|H(a,b)−Σ_(1≤n,m≤M)P_nm(a,b)|`
`≤144a C(0) exp(−π(M+1))/((9−a²)²(1−exp(−π))²)`.

Here `C(0)=besselFirstAtomTailCost 0` is the established universal radial
cost. The bound is uniform in frequency and retains the linear aperture
factor at `a=0`. It is an absolute error bound, not the signed lower bound
needed for all-rank positivity.

## Proof

For `r≥0`, `exp r≥1+r` and `π>3`. Thus, for `k≥1`,
`πk exp r≥πk+3r`. Also `1−exp(−πexp r)≥1−exp(−π)>0`.
The established complete-source rectangular remainder therefore satisfies

`|T(r,b)−Σ_(1≤n,m≤M)T_nm(r,b)|`
`≤8C(0)exp(−π(M+1))exp(−3r)/(1−exp(−π))²`.

The same comparison gives
`|T_nm(r,b)|≤4C(0)exp(−πnm)exp(−3r)`.
These bounds and measurability give integrability after multiplication
by `w_a`. Finite sums commute with the aperture integral. The triangle
inequality reduces the claimed bound to

`∫_(r>0)w_a(r)exp(−3r)dr=18a/(9−a²)²`.

Expand `sinh` and `cosh` into exponentials and use
`∫_0^∞exp(−cr)dr=1/c`, `∫_0^∞r exp(−cr)dr=1/c²`, for `c=3±a>0`.
The four terms combine to the displayed rational expression.

## Pair signs survive aperture integration

For `0<a<1/2`, `P_nm(a,b)` has exactly the sign of
`cos(b(log n−log m))`. The radial tail amplitude and `w_a(r)` are
strictly positive for every `r>0`; integrability is established above.
Thus a positive (respectively negative) cosine gives a strictly positive
(respectively negative) integral, while zero cosine gives zero.
In particular every diagonal pair is positive, and every unequal pair
is negative at `b=π/(log n−log m)`. The aperture weight does not justify
termwise positivity; any full-source sign proof must retain cancellation.
