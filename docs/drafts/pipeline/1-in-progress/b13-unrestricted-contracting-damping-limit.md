# Divisor recovery beyond the coarse contraction threshold

- **Obstacle:** B13, B134.
- **Stage:** 1-in-progress
- **Type:** CONJECTURE

## Target

For the pole-and-divisor filter of degree `d`, retain the quotient limit

`A_{P_h}(t)/(h(t)^d K(exp(−at),ρ₀−σ−it))`
`→ −mρ₀(ρ₀−1)Π_{ρq≠ρ₀}(ρ₀−ρq)`

for every `h(t)>0` with `h(t)→0`, whenever
`r=a(β−σ)/2−π/4>0`. In particular, allow every exponential contraction
speed `κ>0`, without the coarse sufficient restriction `dκ<r`.

The expected raw-observable boundary is then `r−dκ`: growth above zero,
decay below zero. The equality case needs the precise polynomial Gamma factor.

## Missing estimate

The existing zeroth-order error estimate loses `h^d` upon normalization.
The needed full-current bound is

`|Σj c_j(h)e^(−jh(β−s)) E_F(s,y e^(−2jh))|`
`≤ C h^d (1+t)^N (y+y^η)(1+log t)`.

The continued correction should similarly be bounded by
`C h^d (1+t)^(d+1)`.

For the complete complementary Gamma field, exponential differences supply
`h^d Π|ρ−ρj|`; Gamma decay should pay the polynomial in translated ordinate.
For the incomplete Mellin and archimedean errors, finite differences must
be bounded before taking norms. Two Mellin recursions express each zero error as

`−2y e^(−y)/(w(w+2)) − 4y²/(w(w+2)) ∫₀¹ e^(−yu²)u^(w+3)du`,

where `w=ρ−s` and `Re w>−2`. Logarithmic damping derivatives preserve the
inverse-square denominator and a factor `y`. In the archimedean integral,
`(yu²)^k e^(−yu²)` is uniformly bounded; its outside factor `y` and the
telescoping trivial-zero majorant remain. These are concrete candidates for
the derivative estimate, not a completed differentiation-under-the-sum proof.

These derivative bounds are not consequences of a uniform bound on function
values. The exact full-field decomposition in
`EulerFETransportTheory/TheFullGaussianCurrentAtEscapingHeights.lean` and
`OnlyExceptionalGaussianModesRemain.lean` supplies the starting identities.
No paper proof or Lean claim for this stronger limit yet.
