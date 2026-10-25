# Exact damped inverse series of the golden datum

- **ID:** biarithmetic-golden-inverse-series
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Golden digital module](../1-in-progress/biarithmetic-golden-digital-module.md)
- **Statement:** The actual ACS golden zeta series has an explicit inverse after every complex rescaling of its variable. Its positive coefficients are the difference of two geometric towers divided by `-sqrt(5)`.

## Proof

Let the two actual golden Frobenius roots be `alpha,beta`. The corpus gives
`alpha+beta=5`, `alpha*beta=5`; their explicit golden-ratio definitions give
`alpha-beta=sqrt(5)`. At complex parameter `t`, put `a=alpha*t`, `b=beta*t` and

`Z_t(X)=(1-aX)(1-bX)/[(1-tX)(1-5tX)]`.

These are formal power series, so no analytic convergence assumption occurs. Each linear
factor has the geometric inverse `G_c(X)=sum_n c^n X^n`, proved coefficientwise in ACS.
Consequently

`I_t(X)=(1-tX)(1-5tX) G_a(X) G_b(X)`

is the multiplicative inverse of `Z_t`. At `t=1`, `Z_t` is exactly
`goldenDatum.zetaSeries`, not an independently postulated rational model.

The polynomial identity
`(1-aX)(1-bX)=(1-tX)(1-5tX)+tX`
and geometric cancellation give

`G_a-G_b=sqrt(5)*(1-I_t)`.

The constant coefficient of `I_t` is one. Comparing every coefficient of positive degree
therefore gives `coeff_n(I_t)=-(a^n-b^n)/sqrt(5)`. This includes `t=0` without a separate
division by the damping parameter.

## Scope and verification

This is an exact source identity for ACS's golden datum. The arithmetic support map
`n=5^r`, the convergent divisor mean, and the cofactor-module asymptotics are separate
bridges. The partial fractions and geometric-series algebra are classical.

- [x] Dependency-closed paper identity.
- [x] Lean implementation with exact constant-map normalization.
- [x] Direct repository check of `GoldenInverseSeries.lean`.
- [x] Main-declaration transitive axiom audit and umbrella wiring.

Audits of `goldenZetaSeriesAt_one`, `goldenInverseSeriesAt_mul`, `golden_alpha_sub`,
`goldenInverseSeriesAt_tower_difference`, `goldenInverseSeriesAt_constantCoeff`, and
`goldenInverseSeriesAt_coeff` report only `propext`, `Classical.choice`, and `Quot.sound`.
The umbrella imports the checked leaf; no umbrella build was run.
