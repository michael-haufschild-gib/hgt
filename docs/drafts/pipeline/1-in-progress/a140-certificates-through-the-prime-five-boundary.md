# Weil certificates through the prime-five boundary

- **ID:** A140-larger-apertures
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Target:** Positive Weil floors above `log(3)/2`, above `log(2)`, and
  through `log(5)/2`, uniformly in block size.

## Analytic reduction

The regional logarithmic form is diagonal in Legendre moments. Retaining
finitely many low moments reduces each parity to a weighted capacity problem;
the tail has the next harmonic gap. At these apertures the prime reflections
for `2`, `3`, and `4` must be retained together.

The Gamma comparison previously retained its polynomial moments only for
lag radius `r≤1`. The larger windows require `r≤log(5)<2`. The extension
uses, for `0<z≤1`,

`z/sinh(z) ≥ 1−z²/6+z⁴/64`,
`1/cosh(z) ≥ 1−z²/2+z⁴/7`.

Consequently the same exact Gamma remainder satisfies
`R(t)≥t³/1024+t⁴/224` for `0<t≤2`. These inequalities follow from the
existing degree-six exponential bounds and polynomial inequalities on `[0,1]`.

`retainedGammaRemainderWeight_ge_higher_lags_to_two` and
`local_gamma_terms_integrable_to_two` passed direct Lean checks and
transitive audits, with only `propext`, `Classical.choice`, `Quot.sound`.
They are in `TheGammaRemainderRetainsHigherLagsThroughRadiusTwo.lean`.

## Open obligations

- Check the drafted exact mean/correlation decomposition through lag radius two.
- Prove positive finite-moment capacities for the simultaneous prime reflections,
  including both parities. No such certificate is claimed here.
- Transfer the resulting floors to all block sizes.
