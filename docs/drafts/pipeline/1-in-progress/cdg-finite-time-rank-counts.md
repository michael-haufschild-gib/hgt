# Finite-time return counts from the collective rank profile

- **ID:** CDG-COUNT
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** Convert the uniform small-form rank bound into actual
  return-measure estimates, retaining its smaller dimension exponent.

## Target

For `k` distinct primes, rank threshold `r`, and integer `N≥2`, let
`Δ=Δ_r(N−1)` be the proved collective depth floor. The proposed bound,
uniform over an interval of length `T` and every target phase vector, is

`vol{t: every prime phase is within chord distance 1/(2kN) of target}`
`  ≤ 4T/N^(k−r+1)+8/Δ`.

## Mechanism

Expand the squared modulus of the normalized sum over exponent vectors
`{0,…,N−1}^k`. All differences with logarithmic frequency below `Δ`
lie in one rational subspace of dimension at most `r−1`. An injective
coordinate projection bounds each affine fibre by `N^(r−1)`, hence the
normalized weight of close pairs by `N^(−(k−r+1))`. Far pairs contribute
at most `2/(TΔ)`. On a return, every smooth monomial has chord error at
most `1/2`, so the squared normalized sum is at least `1/4`.

## Quantitative boundary

For `T≥2N^(k−r+1)/Δ`, the proposed return fraction is at most
`8N^(−(k−r+1))`. Its required horizon is polynomial in resolution `N`;
at half rank, the exponent coefficient has degree linear in dimension.
Elementary separation instead gives an exponential-in-`N` horizon, and
the scalar Baker bound has a quadratic dimension degree. These formulas
must be compared before claiming an improved parameter regime.

The result concerns shrinking precision. Fixed Fourier height is already
served by stronger elementary separation; this argument does not supply
constant-precision breadth or exclude the first return.

## Existing mechanisms

`HTGeometry.ReplicaCrowdingSpectralDimensionLaw` already converts abstract
near-frequency rank into spectral-moment bounds. `PrimeTorusTheory.TheBoxesOfTheTorus`
already controls finite-time Fourier errors with coefficient mass one.
The missing arithmetic application is an actual return set, with the
collective threshold discharged and the dimension dependence retained.
No generic conditional rank receiver alone qualifies as the result.
