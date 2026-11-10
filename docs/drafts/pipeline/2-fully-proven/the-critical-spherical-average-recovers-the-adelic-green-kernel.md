# The critical spherical average recovers the adelic Green kernel

- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper proof; Lean verification in progress)
- **Obstacle:** B133: connect the mixed hyperbolic kernel to the actual all-prime Green inverse.

## Target

Let `A` be the established `p⁻²`-weighted adelic adjacency, `e` its tempered
edge, `S=√((e+¼)I−A)`, and `K(r)=exp(−rS)/(4π sinh r)`.
For every pair of finite adelic vertices `x,y`, prove that the critical
spherical average is integrable and equals the actual minimal Green kernel:

`∫₀∞ 4π sinh²(r) φ_{1/2}(r) K(r;x,y) dr = green(x,y)`.

Equivalently the integral is `∫₀∞ 2sinh(r/2)(exp(−rS)δ_x)(y)dr`.
The right side is the already constructed least nonnegative solution of
`(e−A)g=δ_x`, without a finite-place cutoff.

## Proof

Put `E(r)=exp(−rS)` and `w_ν(r)=sinh(νr)/ν`. The established positive
semigroup satisfies `‖E(r)‖≤exp(−r/2)`. For `0<ν<½`,
`‖w_ν(r)E(r)‖≤ν⁻¹exp(−(½−ν)r)` on `r≥0`, so its operator integral exists.
The companion `W_ν(r)=cosh(νr)E(r)+w_ν(r)SE(r)` satisfies
`W_ν(0)=I`, `W_ν(∞)=0`, and
`W_ν′(r)=−((e+¼−ν²)I−A)w_ν(r)E(r)` by `S²=(e+¼)I−A`.
The fundamental theorem of calculus gives `P_νR_ν=I`.

Set `T=A/e`, `c_ν=e+¼−ν²`, and `q_ν=e/c_ν∈(0,1)`.
Since `‖T‖≤1`, the norm-convergent Neumann series
`B_ν=(q_ν/e)Σ_{k≥0}(q_νT)^k` is a two-sided inverse of
`P_ν=c_ν(I−q_νT)`. Thus `R_ν=B_ν`.

Let `a_k(x,y)=(T^k(δ_x/e))(y)≥0`. Its partial sums satisfy exactly the
recursion defining the established occupation approximants, hence
`Σ_k a_k(x,y)=green(x,y)<∞`. Evaluation of the operator Neumann series gives
`R_ν(x,y)=Σ_k q_ν^{k+1}a_k(x,y)`. As `ν↑½`, dominated convergence,
with summable majorant `a_k(x,y)`, gives `R_ν(x,y)→green(x,y)`.

For `ν>0`, `w_ν(r)=∫₀ʳ cosh(νt)dt`; therefore `w_ν(r)` increases with
`ν` for `r≥0`. Positivity of every semigroup entry makes the spherical
integrands nonnegative and increasing along
`ν_n=(1−2^{−(n+1)})/2↑½`. Monotone convergence gives
`∫₀∞ w_{1/2}(r)E(r;x,y)dr=green(x,y)` as an extended nonnegative integral.
The finite product barrier for `green` makes this integral finite, proving
ordinary integrability, including `x=y`. Finally,
`4πsinh²(r)φ_{1/2}(r)K(r;x,y)=w_{1/2}(r)E(r;x,y)` for `r>0`.
No operator-norm integrability is asserted at the critical edge.

## Boundary

This identifies two independently constructed kernels on the weighted
adelic carrier. It does not equate their diagonal with Weil's diagonal or
assume the refuted invariant-gluing claim. A full hyperbolic Plancherel
inverse theorem is a separate statement.
