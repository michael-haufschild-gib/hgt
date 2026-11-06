# Strict aperture cancellation on a geometric phase chain

- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean formalization in progress)
- **Wall:** Σ6

Let `a>0`, `h≥0`, `0≤p<1`, `s>0`, `|z|=1`, and choose `N` with
`s≤Nh`. Put `f_k=p^k w_a((s−kh)₊)`, where
`w_a(r)=sinh(ar)+ar cosh(ar)`. Then

`Σ_(k=0)^N f_k Re(Σ_(j=0)^k z^j conjugate(z)^(k−j)) > 0`.

For atoms `q^j`, the established shifted-pair identity has exactly these
parameters: `h=log q`, `p=q^(−1/2)`, `z=exp(ib log q)`.
The sum includes every pair whose common-center weight is nonzero.

## Proof

For real `t`, let `U=w_a(t₊)`, `M=w_a((t−h)₊)` and
`V=w_a((t−2h)₊)`. Existing aperture convexity gives
`U−2M+V≥0`; monotonicity gives `U−V≥0`. Thus

`U−2pM+p²V−(1−p)²U`
`=p(U−2M+V)+p(1−p)(U−V)≥0`.

For `t≤0`, all three values vanish, so the same identity applies.
Multiplication by `p^k`, with `t=s−kh`, proves every second difference
of `f` nonnegative. At `k=0` it is strictly positive because
`(1−p)²w_a(s)>0`. Also `f_N=f_(N+1)=0` and `N>0`.
The exact geometric-phase summation-by-parts theorem now gives strict
positivity. [PROVED HERE]

This is a common-center cancellation theorem. Its identification with the
infinite literal aperture spectrum, and the interaction of distinct prime
chains, remain separate obligations.
