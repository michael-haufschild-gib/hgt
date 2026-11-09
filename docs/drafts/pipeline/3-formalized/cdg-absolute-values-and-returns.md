# Absolute values and heavy returns

- **ID:** CDG-MOD
- **Stage:** 3-formalized
- **Type:** TRANSFER MECHANISM

## Missing mechanism

The existing `ProportionalSavingIsAHeavyFirstReturn` dictionary concerns
`Σ a_i cos(tℓ_i)`. The programme also needs the complex modulus
`|P(t)|`, where `P(t)=Σ a_i exp(itℓ_i)`, `a_i≥0`, and `S=Σ a_i`.
Large modulus aligns phases around a common angle, which need not be zero.

## Target

For each integer `Q≥1` and every height `t`, prove

`min_{1≤m≤Q} D(mt) ≤ 2Q²(S−|P(t)|) + 4π²S/Q²`,

where `D(u)=Σ a_i(1−cos(uℓ_i))`. Consequently, if
`|P(t)|>(1−c)S`, some `m≤Q` has an `η`-returning subset of mass greater
than `(1−(2Q²c+4π²/Q²)/η)S`.

For `0≤A≤B`, prove the measure transfer

`vol{t∈[A,B]: |P(t)|>(1−c)S} ≤ H_Q vol(R∩[A,QB])`,

where `H_Q=Σ_{m=1}^Q 1/m` and `R` is the corresponding heavy-return set.
All constants are independent of the number of frequencies and the weights.
The result applies to both prime-weight profiles without identifying them.

## Paper proof

Put `θ=arg P(t)`. Polar decomposition gives
`Σ a_i cos(tℓ_i−θ)=|P(t)|`, including when `P(t)=0`. Thus the
rotated defect is `E=S−|P(t)|≥0` by the triangle inequality.

Apply one-dimensional Dirichlet approximation to `θ/(2π)`: some
integer `1≤m≤Q` has `1−cos(mθ)≤2π²/Q²`. Squared chord distance gives
`1−cos(x+y)≤2(1−cos x)+2(1−cos y)` and
`1−cos(mx)≤m²(1−cos x)`. Apply these with
`x=m(tℓ_i−θ)` and `y=mθ`, multiply by `a_i`, and sum:

`D(mt)≤2m²E+2S(1−cos(mθ))≤2Q²E+4π²S/Q²`.

If `|P(t)|>(1−c)S`, then `E<cS`; since `Q≥1`, the last inequality
is strict with upper bound `(2Q²c+4π²/Q²)S`. Weighted Markov, already
proved for the actual subset with cosine defect at most `η`, gives the
stated mass bound.

Let `R` be that heavy-return event and restrict it to `[A,QB]`. Every
large-value height `t∈[A,B]` belongs to a dilation preimage
`{t: mt∈R∩[A,QB]}` for some `1≤m≤Q`. Positivity of `A` and the bounds
on `m` give the interval inclusion. Finite subadditivity and exact Lebesgue
scaling bound its measure by
`Σ_{m=1}^Q (1/m) vol(R∩[A,QB])`. The return event is a finite union of
closed phase-condition sets; the large-value event is measurable by
continuity. No count estimate is assumed in this transfer.

## Prescribed precision and mass

For any `η,κ>0`, choose
`Q=ceil(sqrt(8π²/(κη)))+1` and `c=κη/(4Q²)>0`.
Then `8π²≤κηQ²`, so `2Q²c+4π²/Q²≤κη`. The resulting returned subset
has more than `(1−κ)S` mass. The same dilation cover and harmonic measure
bound therefore hold at any prescribed positive precision and missing-mass
allowance. These choices are explicit and independent of the dimension,
frequencies, weights, and cutoff.

For actual primes `p≤y`, set `a_p=ℓ_p=log p`, so `S=θ(y)`.
Conjugation identifies the modulus of `P(t)` with that of
`Σ_{p≤y} log p·p^(−it)`. At every cutoff and height, either this modulus
is at most `(1−c)θ(y)`, or some `m≤Q` returns an actual prime subset
with more than `(1−κ)θ(y)` logarithmic mass. This dichotomy has no
arithmetic hypothesis.

## Scope

This closes the real-part/modulus gap in the breadth-to-large-value transfer.
It does not assume or prove the missing arithmetic return-count bound, and
it does not by itself cross the bounded-height barrier. The intended output
is a uniform quantitative transfer, not a renamed first-return criterion.
It also applies to rounded frequencies: distinguishing actual prime logarithms
must occur in the arithmetic return estimate.

## Lean status

Module: `CollectiveDiophantineGeometry/AbsoluteValuesForceHeavyReturns.lean`.

- `rotated_defect`: exact modulus-deficit identity.
- `exists_dilation_defect_le`: dimension-independent dilation bound.
- `absoluteLargeSet_subset_heavy_dilations`: prescribed precision and mass.
- `absoluteLargeSet_measure_le_heavy_returns`: harmonic measure transfer.
- `prime_modulus_or_heavy_return`: actual prime-polynomial dichotomy.

The direct repository-file Lean check passed. Eleven principal declarations
passed transitive axiom audits with only `propext`, `Classical.choice`, and
`Quot.sound`. The programme umbrella imports the module.
