# W2: endpoint exterior coefficients

- **ID:** w2-endpoint-exterior-series
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [Arithmetic symmetric-group characters](w2-representation-construction.md)
- **Target:** All alternating projections of the prescribed arithmetic character are nonnegative.

## Exact candidate

Let `G=xiCentreLift`, `M=xiEndpointColorMass`, and
`E(z)=G(1/4+z/M)²/G(1/4)²`. The proposed identity is

`E^(n)(0) = Σ_(σ∈S_n) sign(σ) χ_arith(σ)`.

The square records both functional-equation copies: the endpoint resolvent is `2G'/G`.
Normalization requires `E(0)=E'(0)=1`.

## Analytic argument

The corpus theta identity gives
`G^(n)(0)=n!·thetaCuspRawEvenMoment(n)/(2n)! ≥ 0`.
For any entire function with nonnegative derivatives at zero, apply its Taylor expansion to
each derivative: every derivative remains nonnegative at every nonnegative real argument.
Translation by `1/4`, dilation by `1/M`, squaring, and division by the positive squared value
preserve nonnegative Taylor coefficients. Thus `E^(n)(0)≥0` for every `n`.

## Product and character identification

Pair the centered Hadamard products at `s` and `−s`, where `s²=−y`. Genus-one exponentials
cancel, giving `G(y)²/G(0)²=Π_q(1+y/t_q²)`. Divide this product at `y=1/4+z/M` by its value
at `1/4`; each factor becomes `1+z α_q/M`. Thus `E(z)=Π_q(1+z α_q/M)` with actual divisor
multiplicities. Summability of `|α_q|` gives an absolutely convergent expansion over finite
subsets. Grouping by cardinality and scalar-series uniqueness gives

`E^(n)(0)=n! Σ_(|S|=n) Π_(q∈S)(α_q/M)`.

The normalized complex alphabet has mass one. Absolute convergence factors its fixed-word
trace over cycles, identifying it with `χ_arith`. In the sign projection, a repeated letter
admits a sign-reversing transposition; an injective word has trivial stabilizer. Every
`n`-element subset has `n!` orderings. Therefore the signed trace is the same derivative.

Even complete column positivity leaves mixed Young shapes and full Gram positivity open.
No RH conclusion follows from this subfamily.

## Lean status

`RHTower/Representation/EndpointExteriorSeries.lean` passes its direct leaf check and is
wired into the umbrella. It proves the center derivative formula, affine Taylor positivity,
`nonnegTaylorAtZero_xiEndpointExteriorSeries`, `xiEndpointExteriorSeries_zero`, and
`hasDerivAt_xiEndpointExteriorSeries_zero`.

`EndpointExteriorProduct.lean` proves the exact product, absolute subset expansion, coefficient
identification, and coefficient nonnegativity; its scratch check passes. `ComplexColoring.lean`
passes checking and builds its exact complex cycle-factorization theorem. Final direct leaf checks
remain. `AlternatingComplexColoring.lean` and `EndpointAlternatingPositivity.lean` contain the
signed-character assembly under verification; no complete character-projection theorem is yet claimed.
