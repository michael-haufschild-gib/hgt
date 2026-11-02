# The positive divisor mean controls the signed primitive

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Wall:** Γ12.
- **Statement:** For every prime pattern, put `S_N=Σ_(n≤N)ω_P(n)/n`, `g=1*ω_P`, `G_N=Σ_(n≤N)g(n)/n`, `M_N=Σ_(n≤N)(ω_P(n)/n)log(N/n)`, and `E_N=Σ_(p∈P,p≤N)(log p/p)S_⌊N/p⌋`. Then
  `|G_N−M_N|≤3+log N`, `E_N≥−A_P(N)`, and
  `|S_N log N−2M_N+2E_N|≤K(1+log N)` for some `K≥0` and every `N≥1`.

## Proof

Divisor swapping writes `G_N=Σ_(d≤N)(ω_P(d)/d)H_⌊N/d⌋`.
The bounded harmonic remainder and the integer-logarithm remainder give
the first estimate. The universal bound `S_N≥−1` gives the second.

Split the logarithmic derivative identity into primes and higher prime
powers. Swapping the full-prime convolution gives the cumulative Mertens
sum against `ω_P(m)/m`; its bounded remainder costs `O(log N)`.
Non-prime prime powers have bounded total `Λ(n)/n` mass and also cost
`O(log N)`. Flipped primes contribute exactly `−2E_N`.

## Lean

`RenormalizedIntersectionTheory/ThePositiveDivisorMeanControlsTheSignedPrimitive.lean`:

- `gaugeHarmonicSum_signDivisorCount_eq`
- `abs_positiveDivisorMean_sub_signedPolarMoment_le`
- `exists_abs_signed_flip_renewal_equation_le`
- `neg_primeSetLogMass_le_flippedPrimeRenewalTerm`

Plain kernel check passed. The three inequality capstones depend only on
`propext`, `Classical.choice`, and `Quot.sound`. No density hypothesis is used.
