# Positive Abel decomposition of the conductor surplus

- **ID:** CONDUCTOR-SURPLUS-ABEL-SQUARES
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [O1](../1-in-progress/weil-positivity-five-structural-mechanisms.md)
- **Target:** An exact positive Fourier-square decomposition of `E_m(c) − E_1(c/m)`.

Put `x=c/m`, `M=∫φ²`, and

`A_m(n)=(m/φ(m))Σ_{1≤a≤n,(a,m)=1}1/a − H_n`.

For every positive overlap and conductor, the identity is

`E_m(c) − E_1(c/m) = (2/M)Σ_{n≥1} A_m(n) ∫_{nx}^{(n+1)x}|φ̂(2πt)|²dt`.

Every summand is nonnegative. The profile may be any nonzero, twice continuously differentiable real function supported in `[0,1]`; the tilted unit spline supplies these conditions explicitly.

The existing `completedConductorEnergy_prime_mul_ge` already implies the rescaled order by prime-factor iteration. The identity here resolves its surplus into explicit Fourier bands.

## Proof

The harmonic sieve inequality gives `A_m(n) ≥ 0`. The centered harmonic limits for the primes dividing `m` give

`A_m(N) → Σ_{p|m} log p/(p−1)`.

Write `d_n=A_m(n+1)−A_m(n)` and `w_n=(2/M)T((n+1)x)`, where `T(y)=∫ᵧ^∞|φ̂(2πt)|²dt`. Subtracting the proved conductor and pole Fourier series gives `Σ d_n w_n=E_m(c)−E_1(x)`. Finite Abel summation gives

`Σ_{n<N}d_n w_n=A_m(N)w_N+Σ_{n<N}A_m(n+1)(w_n−w_{n+1})`.

The normalized tail satisfies `0≤w_N≤E_1((N+1)x)→0`, so the boundary term vanishes. Splitting the integrable tail at `(n+2)x` identifies each difference with its Fourier-band integral. Nonnegative partial sums therefore converge to the stated surplus.

## Lean verification

Module: [Conductor/PositiveAbelSurplus.lean](../../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/Conductor/PositiveAbelSurplus.lean).

- `coprimeHarmonicSurplus_nonneg` and `tendsto_coprimeHarmonicSurplus`: nonnegative coefficients and their finite Euler limit.
- `hasSum_conductorSurplusBand`: the exact convergent series.
- `completedConductorEnergy_sub_pole_eq_tsum`: the surplus identity.
- `tiltedUnitSpline_conductorSurplus_positive_series`: all analytic profile conditions discharged.

Direct `lake --old env lean` check passed. Capstone transitive axioms are exactly `propext`, `Classical.choice`, `Quot.sound`. Umbrella import added.

This exact scalar identity leaves the complete finite-horizon all-vector decomposition open.
