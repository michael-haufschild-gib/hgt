# Degree-one Selberg classification

- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Wall:** Γ15
- **Target:** Every full Selberg function of degree one is a primitive Dirichlet L-function, with the possible imaginary translation allowed by its continuation. In particular, positive coefficients force the zeta function.

## Analytic core

For the extended class, derive periodicity of the coefficients after removing their common imaginary power. The period must be an integer fixed by the Gamma conductor. Then use multiplicativity and the strict Euler bound to identify the primitive character and exclude finite Euler modifications.

The existing cusp expansion gives the exact radius `Δ = m₀/q` at degree one, with `m₀` the first nonzero coefficient index and `q` the presentation conductor. Its boundary singularities must be compatible with the exact period `2πi` of `Σa(n)e^(−nz)`.

## First consequence: a pole or conductor at least `2m₀`

Every extended degree-one function satisfies
`q ≥ 2m₀` or `meromorphicOrderAt F 1 < 0`.

Formalized as `degreeOne_conductor_bound_or_pole`; see [certificate](../3-formalized/selberg-degree-one-conductor-pole.md). This consequence belongs to Γ33 and does not settle the classification target. Meromorphic order avoids dependence on the arbitrary totalized value or nonminimal pole-clearing exponent at one.

## Open dependencies

1. Identify all boundary singularities beyond the already proved cusp-radius formula.
2. Integer conductor and periodicity of the normalized coefficients from translation of those singularities.
3. Primitive-character identification using the full Euler conditions.

The degree gap is already formalized. It does not establish any of these three steps. No classification claim is made until all three are proved in Lean.
