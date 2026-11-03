# Positive Euler twins and the strict square-root threshold

- **ID:** positive-finite-euler-factor-twins
- **Stage:** 1-in-progress
- **Wall:** Γ15; positive multiplicative functional-equation twins.
- **Target:** Every finite zeta coefficient prefix extends to a degree-one
  positive multiplicative Euler series with a zero at any prescribed real
  part `1/2 < σ < 1`. Its logarithmic coefficients obey `3n^σ`; no full
  Selberg carrier has the same ordinary coefficients.

## Construction and proof

Choose a prime `p>N`, put `r=p^σ`, `q=p^(1−σ)`, and `A=r+q`.
The Dirichlet series
`D_A(s)=ζ(s)(1+A p⁻ˢ+p p⁻²ˢ)` has coefficients
`a(n)=1+A·1_(p∣n)+p·1_(p²∣n)` for `n≥1`.
Thus `1≤a(n)≤1+A+p`, `a(1)=1`, and `a(n)=1` for `n≤N`.
Coprime multiplicativity follows because at most one factor is divisible by `p`.

Its completion is `Λ(s)(pˢ+A+p^(1−s))`, with degree one, conductor `p²`
and root number one. The bracket is reflection-even. An entire finite-order
regularization is
`ξ(s)π^(s/2)/Γ(s/2+1) · (1+A p⁻ˢ+p p⁻²ˢ)`;
it equals `(s−1)D_A(s)` away from the pole.
The explicit zero `(log r+iπ)/log p` has real part `σ`.

For any `A≥0`, each added zero satisfies `Re s=1/2 ↔ A≤2√p`:
writing `t=pˢ` gives `t²+At+p=0`, whose root norm is `√p` precisely
below this threshold.

Let `α+β=−A`, `αβ=p`. The prime-power Euler logarithm is
`b(p^k)=(1−α^k−β^k)/k`; at other prime powers it is `1/k`, and elsewhere zero.
For the displayed construction, `α=−p^σ`, `β=−p^(1−σ)`.
Both root norms are at most `p^σ<p`, so the logarithm converges absolutely
throughout `Re s>1`, exponentiates to `D_A`, and satisfies `|b(n)|≤3n^σ`.

For every real `A`, the strict Euler bound fails. If it held with exponent
`θ<1/2`, normalize the roots by `√p` and put
`u_k=(α^k+β^k)/p^(k/2)`. The bound implies `u_k→0`, whereas
`u_(2k)=u_k²−2` forces `0=−2`. Below `A=2√p`, the matching bound
`|b(p^k)|≤3p^(k/2)` holds. Any purported full Selberg logarithm has these same
coefficients: differentiate the equality of exponentials, then use Dirichlet
series injectivity. The obstruction therefore excludes every full presentation,
including presentations with different gamma data.

## Lean declarations

Namespace `GaloisForLFunctions.SelbergClass.PositiveFiniteEuler`:

- `PositiveFiniteEulerCoefficients`: `lSeriesHasSum`, `coeff_bounds`,
  `arithmeticCoeffs_isMultiplicative`, `ramanujan`.
- `PositiveFiniteEulerCompletion`: `extendedClass`, `extendedClass_degree`,
  `extendedClass_conductor`, `orderOneEnvelope_regularized`.
- `PositiveFiniteEulerZeros`: `localFactor_zero_critical_iff`,
  `localFactor_factorZero`, `quadratic_logCoeff_bound`.
- `PositiveFiniteEulerBound`: `fullClass_eulerLogCoeff_prime_pow`,
  `not_strictEulerBound`, `not_fullClass`.
- `PositiveFiniteEulerProduct`: `eulerLogCoeff_primePower`,
  `eulerLogCoeff_bound`, `logarithmicCoeffs_summable`, `logarithmicCoeffs_exp`.
- `PositiveFiniteEulerTwins`: `exists_positive_multiplicative_euler_twin_at`,
  `exists_positive_multiplicative_twin`.

The existential assembly is formalized. All 20 audited declarations depend
only on `propext`, `Classical.choice`, `Quot.sound`. Canonical source checks
remain pending.
The full Selberg-constrained face of Γ15 remains open.
