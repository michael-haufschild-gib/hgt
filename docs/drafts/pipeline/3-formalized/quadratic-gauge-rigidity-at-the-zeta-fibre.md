# Quadratic gauge rigidity at the zeta fibre

- **ID:** B130-quadratic-gauge
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** F3/B142; pole residue curvature candidate.
- **Statement:** For a holomorphic regularized gauge continuation, real nonvanishing is equivalent to quadratic prime convergence. Under these conditions, conjugate-paired multiplicities and zero-free half-planes agree with ζ.

## Exact theorem

Fix `1/2≤c<1`, a gauge point `x`, and a holomorphic function `U` on
`Re s>c` agreeing with `(s-1)F_x(s)` for `Re s>1`. Let `Z` be the entire
extension of `(s-1)ζ(s)`, with `Z(1)=1`.

The following conditions are equivalent:

- `U(σ)≠0` for every real `σ>c`, including `σ=1`.
- For every `σ>c`, `Σ_p |χ_x(p)-1|² p^(-σ)<∞`.

Under these equivalent conditions:

1. `U(s) conj(U(conj s)) = Z(s)² exp(H(s))` throughout `Re s>c`,
   with an explicitly defined holomorphic `H`.
2. For `s≠1`, `ord_s U + ord_conj(s) U = 2 ord_s ζ`.
   Every zero of `U` is a zeta zero; each zeta zero belongs to at least
   one member of the conjugate pair.
3. For every `d≥c`, `U` is zero-free on `Re s>d` iff ζ is zero-free
   there away from its pole. Such a continuation cannot improve zero width.

Without real nonvanishing, divergence of the quadratic prime series at
any `σ>c` forces a real zero of `U` above `c`. If `U(1)≠0`, the forced
real zero lies away from one.

These statements classify actual holomorphic continuations. They do not
assert the existence of a nontrivial continuation or a purity family.

## Proof

Set `V(s)=conj(U(conj s))` and

`E(s)=Σ_p (1-Re χ_x(p))p^(-s)`.

Opposite gauge points are Schwarz conjugates. Since
`|χ_x(p)-1|²=2(1-Re χ_x(p))`, the coefficients of `E` are nonnegative.
On `Re s>1`, the Euler logarithm gives

`UV=Z² exp(-2E+R)`,

where `R=h_x+h_(-x)-2h_0` is holomorphic on `Re s>1/2`.
Termwise differentiation gives `D=-E'` with nonnegative coefficients
`(1-Re χ_x(p))log p`. Clearing denominators yields

`2ZUV D = Z(U'V+UV')-2Z'UV-R'ZUV`.

The numerator and denominator are holomorphic on `Re s>c`; under real
nonvanishing, the denominator never vanishes on its real ray. If `D`
failed to converge there, its finite real abscissa would lie above `c`.
Analytic uniqueness extends the cleared identity to the convergence
half-plane. Division by the denominator continues `D` across its real
abscissa, contradicting Landau. Thus `D`, and hence `E`, converges
throughout the half-plane; use `log p≥log 2>0` to remove the derivative
weight. Analytic uniqueness extends the paired exponential identity.
Its exponential factor has no zeros, giving the divisor law.

Conversely, quadratic convergence throughout the half-plane makes `E`
holomorphic there. Analytic uniqueness extends the same paired identity
without assuming real nonvanishing. At every positive real point, `Z`
and the exponential are nonzero; hence `U` is nonzero there.

## Lean and audit

Modules: `ArithmeticWeightTheory/GaugeDeformations/PositiveSeriesBoundary.lean`
and `ArithmeticWeightTheory/GaugeDeformations/QuadraticGaugeRigidity.lean`.
Both are imported by the `ArithmeticWeightTheory` umbrella.

Capstones:

- `real_nonvanishing_iff_quadratic_summable` — exact convergence criterion.
- `gauge_quadratic_rigidity` — convergence and the paired exponential identity.
- `gauge_conjugate_multiplicities` — exact multiplicity conservation.
- `gauge_zeroFree_halfPlane_iff` — identical zero-free half-planes.
- `real_zero_away_from_pole_of_quadratic_divergence` — the real-zero obstruction.

Both final direct Lean checks passed. All transitive audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.

## Novelty and boundary

`EulerDeformationsOfZetaAreIsozeric.exists_isozeric` assumes absolute prime
perturbation summability. Here quadratic convergence is deduced from
continuation and real nonvanishing, with an exact converse and a paired
divisor law. The existing jump-locus theorem classifies radial growth at
one, not half-plane continuation. Corpus searches found these inputs and
the general Landau singularity theorem, but not this criterion. No external
novelty claim.

[Compact divisor rigidity of gauge families](compact-divisor-rigidity-of-pole-preserving-gauge-families.md)
is also formalized. B130's arithmetic Stepanov bound remains open;
no purity specialization has been constructed.
