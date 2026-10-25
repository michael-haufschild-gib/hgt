# Factorial order one in the uniform Vaughan logarithmic bounds

- **ID:** vaughan-factorial-order-one-is-a-fixed-strip
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** ../3-formalized/uniform-vaughan-convolution-stretched-exponential-rate.md
- **Statement:** A common-threshold logarithmic envelope with constants `C A^q q!` for the actual uniform undamped Vaughan convolution is equivalent to a fixed zero-free strip.

## Question

The stretched-exponential paper produces one threshold for every logarithmic
order, but its constants grow as `A^(3q)(3q)!`. Determine whether replacing
this by `A^q q!`, still at one common threshold and uniformly in both cutoffs,
is exactly the missing fixed-power estimate.

## Proposed mechanism

For a scalar error ratio `F(n)`, divide
`|F(n)|(log n)^q≤C A^q q!` by `A^q q!`, multiply by `r^q`, and sum over
`q`, where `0≤r<1`. The exponential and geometric series give

`|F(n)| exp(r log(n)/A)≤C/(1-r)`.

Thus every exponent `r/A<1/A` is a power saving, with the same starting
threshold; `r=1/2` gives `2C n^(-1/(2A))`. Conversely the exponential-series
inequality turns a power bound with exponent `η>0` into a common-threshold
factorial envelope with `A=1/η`. No endpoint assertion at `1/A` is needed.

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

UNPROVED pending Lean verification. `/tmp/QIFactorialLogPowerTools.lean`
contains five complete generic proof drafts, including the uniform-family
equivalence with a common threshold. Its source argument is the corpus's
factorial-moment exponential-window proof; the exact exponential-series,
geometric-series, and norm-comparison declarations have been read in mathlib
after the corpus search. `/tmp/QIVaughanFactorialEnvelopeTools.lean` now drafts
both the actual factorial/power equivalence and its fixed-strip equivalence.

The latter depends on `/tmp/QIUniformVaughanPowerTools.lean`: the exact
unit/full-cutoff value, every transferred gain `κ<η/(2+η)`, the extreme-cutoff
converse, and the uniform power/fixed-strip equivalence. The optimized cutoff
is `D=floor(n^(1/(2+η)))`; the strict gap absorbs the harmonic logarithms.
`/tmp/QIMertensHarmonicPowerTools.lean` supplies the missing forward harmonic
bound with constant `C(1+1/η)` using the exact strict Mertens tail.
The harmonic-power converse is in the existing unchecked extreme-cutoff draft.
All these drafts require compilation and axiom audits. No fixed strip or Q-I
completion is claimed.
