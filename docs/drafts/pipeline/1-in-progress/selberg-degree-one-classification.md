# Degree-one Selberg classification

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Γ15
- **Target:** Every full Selberg function of degree one is a primitive Dirichlet L-function, with the possible imaginary translation allowed by its continuation. In particular, positive coefficients force the zeta function.

## Analytic core

For the extended class, derive periodicity of the coefficients after removing their common imaginary power. The period must be an integer fixed by the Gamma conductor. Then use multiplicativity and the strict Euler bound to identify the primitive character and exclude finite Euler modifications.

The existing cusp expansion gives the exact radius `Δ = m₀/q` at degree one, with `m₀` the first nonzero coefficient index and `q` the presentation conductor. Its boundary singularities must be compatible with the exact period `2πi` of `Σa(n)e^(−nz)`.

## First consequence: a pole or conductor at least `2m₀`

**Claim:** Every extended degree-one function satisfies
`q ≥ 2m₀` or `meromorphicOrderAt F 1 < 0`.

Suppose the order at one is nonnegative. Its analytic punctured germ makes the polar residue in the cusp expansion zero. Scaling the cusp coordinate gives a holomorphic extension `G` of the ordinary exponential series to `|z| < 2πm₀/q`. If `q < 2m₀`, this radius exceeds `π`.

The identity theorem propagates `G(z+πi)=G(z−πi)` across the overlap disk. Choose a rectangle with imaginary coordinates `−π,π` and real coordinates `−a,a`, where `a>0` and the rectangle lies inside the extension disk. Integrating `G(z)e^{nz}` cancels the horizontal edges. The right edge extracts `2πa(n)`; boundedness on the compact left edge gives `|a(n)|≤C e^(−an)`. Hence the Dirichlet series converges absolutely at zero, which the existing unconditional abscissa theorem excludes at positive degree.

Paper proof dependency-closed; Lean formalization in progress. The meromorphic order avoids dependence on the arbitrary totalized value or nonminimal pole-clearing exponent at one.

## Open dependencies

1. Identify all boundary singularities beyond the already proved cusp-radius formula.
2. Integer conductor and periodicity of the normalized coefficients from translation of those singularities.
3. Primitive-character identification using the full Euler conditions.

The degree gap is already formalized. It does not establish any of these three steps. No classification claim is made until all three are proved in Lean.
