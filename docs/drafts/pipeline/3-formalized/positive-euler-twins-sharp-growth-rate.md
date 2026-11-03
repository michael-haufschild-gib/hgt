# Exact Euler discrepancy abscissa of the positive twins

- **ID:** positive-euler-twins-sharp-growth-rate
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean).
- **Wall:** Γ15; sharpness of the relative Euler strip.
- **Parent:** [positive finite-factor twins](../3-formalized/positive-finite-euler-factor-twins.md).
- **Target:** For a prime `p` and `1/2<σ<1`, the positive twin's logarithmic
  Euler discrepancy has absolute-convergence abscissa exactly `σ`. Its added
  zeros have real parts exactly `σ` and `1−σ`.

Put `r=p^σ`, `q=p^(1−σ)`, `A=r+q`, and
`D(s)=ζ(s)(1+A p⁻ˢ+p p⁻²ˢ)`. The parent constructs its degree-one extended
Selberg carrier with positive bounded multiplicative coefficients, its Euler
logarithm on `Re s>1`, and arbitrary agreement with a finite zeta prefix.

The logarithmic discrepancy `E` is supported on `p^k`, `k≥1`, with
`E(p^k)=−[(-r)^k+(-q)^k]/k`.
Its exact norm is `(r^k+q^k)/k`. Hence, for `Re s≤σ`, the absolute term
at `p^k` is at least `1/k`; the harmonic series excludes absolute convergence.
For `Re s>σ`, both local Taylor logarithms converge absolutely because
`q≤r` and `r p^(−Re s)<1`. Thus
`LSeriesSummable E s ↔ σ<Re s`, giving the exact abscissa.

Writing `t=p^s`, the added zero equation factors as
`(t+r)(t+q)=0`, since `rq=p`. Taking norms gives
`Re s∈{σ,1−σ}`. The explicit zero `(log r+iπ)/log p` attains the right
boundary, and reflection attains the left boundary.

This realizes equality in the relative Euler-strip bound with an actual
positive multiplicative carrier. It does not weaken or satisfy the full
Selberg requirement that the Euler exponent be strictly below `1/2`.

## Lean

`SelbergClass/PositiveFiniteEulerRate.lean`, namespace
`GaloisForLFunctions.SelbergClass.PositiveFiniteEuler`:

- `localDiscrepancy_eq_sub`: the actual Euler-logarithm discrepancy.
- `norm_localDiscrepancy_prime_pow`, `harmonic_le_norm_localDiscrepancy_term`:
  exact coefficients and the divergent boundary minorant.
- `localDiscrepancy_summable_iff`, `localDiscrepancy_abscissa`: exact convergence boundary.
- `localFactor_zero_re_rootRadius`, `added_zero_on_each_boundary`: both zero lines.
- `added_zero_attains_euler_abscissa`: equality in the relative-strip depth bound.

All eleven audited declarations depend only on `propext`, `Classical.choice`,
`Quot.sound`. Canonical source verification passed; the module is imported
by the SelbergClass umbrella.
