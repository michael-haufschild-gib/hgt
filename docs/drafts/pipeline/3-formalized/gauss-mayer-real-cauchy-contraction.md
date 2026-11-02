# Strict real-parameter Cauchy contraction

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [PM tasks](../1-in-progress/route-pm-mayer-scattering-and-escape.md), Mayer 3.
- **Input:** [Cauchy Mellin symbol](gauss-mayer-cauchy-mellin-symbol.md).
- **Lean:** `RenormalizedIntersectionTheory/GaussMayerRealCauchyContraction.lean`, namespace `MayerRealCauchyContraction`.

## Exact result

For every real `r>0` and every real frequency `ξ`, the actual Cauchy multiplier satisfies

```text
0 < M K_r(r/2+iξ) ≤ c(r) < 1,
c(r) = Γ((r+2)/4)^2 / (√π Γ((r+1)/2)).
```

With the strictly positive real density `p_r(t)=K_r(t)/t`,

```text
∫ p_r(t) dt = ∫ t^r p_r(t) dt = 1,
∫ (t^(r/2)−1)^2 p_r(t) dt = 2(1−c(r)) > 0.
```

Every integral is over `t>0` and converges absolutely.

## Proof

Identify the actual complex Cauchy kernel with `t` times its real positive
Gamma-normalized density. The full Mellin formula supplies the zeroth,
spectral, and midpoint moments. Expanding the square gives the exact
energy identity; all three terms are integrable. The square is strictly
positive on `(2,3)`, a set of positive measure, so `c(r)<1`. The actual
Mellin integral at frequency `ξ` differs from the midpoint integrand by a
factor of modulus one. The integral triangle inequality gives the uniform
upper bound. Gamma conjugation gives strict positivity at every frequency.

## Lean certificate

- `averagingFactor_ofReal`, `density_pos`, `cauchyKernel_ofReal`: actual positive density.
- `density_integral`, `spectral_moment_integral`, `central_moment_integral`: exact moments.
- `centralSymbol_zero`: explicit real Gamma quotient.
- `energy_integrable`, `energy_integral`, `energy_integral_pos`: finite, strictly positive squared energy.
- `centralSymbol_zero_lt_one`, `centralSymbol_le_zero`, `centralSymbol_bounds`: strict frequency-uniform multiplier bound.

Direct production check passed. All 13 declarations have only
`propext`, `Classical.choice`, and `Quot.sound` as transitive axioms.

## Boundary

This is a bound for the actual Cauchy Mellin multiplier at real positive
parameters. It does not supply the Mayer operator's Hermitian form or a
contraction estimate at nonreal parameters.
