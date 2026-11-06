# Positive aperture spectrum of the complete geometric theta chain

- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean formalization in progress)
- **Wall:** Σ6

For every integer `q≥2`, `0<a<1/2`, and real `b`,

`Σ_(k≥0) Σ_(i=0)^k P_(q^i,q^(k−i))(a,b) > 0`,

where `P_nm` is the literal ordinary-pair aperture spectrum. The series
is absolutely convergent before cancellation within each block.

## Proof

Set `h=log q`, `p=exp(−h/2)`, `z=exp(ibh)` and
`F_b(s)=thetaPairCenterTailSpectrum 1 1 s b`. The established shifted-pair
identity gives, for every total exponent `k`,

`Σ_(i=0)^k P_(q^i,q^(k−i))`
`=∫_(s>0) p^k w_a((s−kh)₊) Re U_k(z) F_b(s) ds`.

At each `s>0`, only finitely many clipped weights survive. The strict
geometric aperture cancellation theorem therefore makes their full sum
positive. Also `F_b(s)>0`.

Since `|U_k(z)|≤k+1` and `w_a((s−kh)₊)≤w_a(s)`, the absolute
integrand is bounded by `(k+1)p^k w_a(s)F_b(s)`. The last radial factor
is integrable and `Σ(k+1)p^k<∞`, so dominated summation identifies the
block series with the integral of its pointwise positive sum. The
integral is strictly positive, for example on `0<s<1`.

The same bound holds before block cancellation: each individual pair has
absolute integral at most `p^k P_11(a,b)`, and the block has `k+1` pairs.
This proves absolute convergence of every ordered-pair contribution.
[PROVED HERE]

The statement covers infinitely many unequal atoms on one multiplicative
chain. It does not yet assert literal all-rank source jets or positivity
when distinct prime chains interact.
