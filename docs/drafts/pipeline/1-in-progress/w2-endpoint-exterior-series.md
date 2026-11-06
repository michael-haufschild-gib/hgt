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

## Remaining identification

Prove the signed cycle-index identity with fixed points included. Equivalently, compare the
Newton recurrence for the sign projection with the derivative recurrence from `E'/E`.
Analytic coefficient positivity alone does not identify that projection.

An alternative bridge is the endpoint product
`E(z)=Π_q(1+z α_q/M)`. Pairing the centered Hadamard products at opposite arguments cancels
the genus-one exponentials. Taking the quotient at square coordinates `1/4+z/M` and `1/4`
then gives these exact factors. Absolute summability permits expansion over finite subsets.
The remaining combinatorial identification is the signed fixed-word sum: repeated colors
cancel, and injective words give `n!` times the subset mass of cardinality `n`.

Even complete column positivity leaves mixed Young shapes and full Gram positivity open.
No RH conclusion follows from this subfamily.

## Lean status

`RHTower/Representation/EndpointExteriorSeries.lean` passes its direct leaf check and is
wired into the umbrella. It proves the center derivative formula, affine Taylor positivity,
`nonnegTaylorAtZero_xiEndpointExteriorSeries`, `xiEndpointExteriorSeries_zero`, and
`hasDerivAt_xiEndpointExteriorSeries_zero`. Product and cycle-index identifications remain open.
