# Factorial order one in the uniform Vaughan logarithmic bounds

- **ID:** vaughan-factorial-order-one-is-a-fixed-strip
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** ../2-fully-proven/uniform-vaughan-convolution-stretched-exponential-rate.md
- **Statement:** A common-threshold logarithmic envelope with constants `C A^q q!` for the actual uniform undamped Vaughan convolution is equivalent to a fixed zero-free strip.

## Question

The stretched-exponential paper produces one threshold for every logarithmic
order, but its constants grow as `A^(3q)(3q)!`. Determine whether replacing
this by `A^q q!`, still at one common threshold and uniformly in both cutoffs,
is exactly the missing fixed-power estimate.

## Proposed mechanism

For a scalar error ratio `F(n)`, bounds
`|F(n)|(log n)^q≤C A^q q!` at one common threshold imply a power bound
by choosing `q=floor(log n/(2A))` and using `q!≤q^q`. Conversely a
power bound implies such a factorial envelope by the exponential-series
inequality already used in the stretched-exponential source.

For the actual Vaughan convolution, the extreme cutoffs `U=1,V=n`
give summatory value one. Thus a uniform power remainder forces a power
bound for `H_n` and hence a fixed strip by finite Abel inversion. The
reverse implication should follow from the checked finite convolution
bound with a small positive power cutoff and actual Mertens/harmonic
power rates supplied by a strip.

## Required audits

- Check the exact extreme-cutoff identity and the two directions of the
  actual harmonic power-rate bridge in the corpus.
- Search for an existing factorial-order criterion before claiming a new
  result; use existing generic statements when available.
- Close the finite-tail constants, common threshold, and zero-order cases
  on paper before formalization.
- Keep the distinction between an equivalent criterion and a producer:
  no order-one factorial envelope is currently proved here.

## Status

Conjecture and proof plan only. No claim of a fixed strip or Q-I completion.
