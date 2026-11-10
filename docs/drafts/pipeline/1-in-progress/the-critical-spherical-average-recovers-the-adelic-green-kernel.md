# The critical spherical average recovers the adelic Green kernel

- **Stage:** 1-in-progress
- **Type:** CONJECTURE / construction
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

## Mechanism to establish

For `0<ν<½`, the operator integral
`R_ν=∫₀∞ sinh(νr)/ν · exp(−rS)dr` converges in norm. Integrate the
Wronskian derivative to prove `((e+¼−ν²)I−A)R_ν=I`; symmetry or
injectivity gives the opposite inverse identity.

Expand this subcritical inverse in the norm-convergent positive adjacency
series. At every finite occupation depth, its coefficients increase to
the coefficients defining `green` as `ν↑½`; the critical product barrier
bounds the full sum. Thus the inverse entries tend to `green(x,y)`.
Monotone convergence of the positive spherical integrands then proves
integrability and the exact critical integral, even though the available
operator-norm decay bound alone does not make the critical integral converge.

## Boundary

This identifies two independently constructed kernels on the weighted
adelic carrier. It does not equate their diagonal with Weil's diagonal or
assume the refuted invariant-gluing claim. A full hyperbolic Plancherel
inverse theorem is a separate statement.
