# Factorial order one in the uniform Vaughan logarithmic bounds

- **ID:** vaughan-factorial-order-one-is-a-fixed-strip
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Verification:** All seven generic and actual targets passed final direct Lean checks and standard-axiom audits. Both modules are wired; owned scratch files are removed.
- **Source:** uniform-vaughan-convolution-stretched-exponential-rate.md
- **Statement:** A common-threshold logarithmic envelope with constants `C A^q q!` for the actual uniform undamped Vaughan convolution is equivalent to a fixed zero-free strip.

## Criterion

The checked stretched-exponential bound supplies one threshold for every
logarithmic order, with constants growing as `A^(3q)(3q)!`. Replacing this by
`A^q q!`, still at one common threshold and uniformly in both cutoffs,
is exactly equivalent to the missing fixed-power estimate.

## Proof mechanism

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
reverse implication follows from the checked finite convolution
bound with a small positive power cutoff and actual Mertens/harmonic
power rates supplied by a strip.

## Scope

The exact extreme-cutoff identity, both harmonic power-rate transfers, finite
heads, common threshold, and zero-order cases are covered by the checked
dependencies and declarations below. Corpus search preceded the Mathlib source
checks; no external novelty claim is made. This is an equivalent criterion:
no unconditional order-one factorial envelope is asserted.

## Status

All five generic targets in `HTGeometry/FactorialLogarithmicBoundsArePowerBounds.lean`
passed corrected producing and final direct checks, with standard axioms only
and no warnings. The module is wired and its scratch removed:

- `abs_mul_exp_le_of_factorial_bounds`
- `abs_le_exp_neg_of_factorial_bounds`
- `abs_le_rpow_of_log_factorial_bounds`
- `log_factorial_bound_of_abs_le_rpow`
- `uniform_log_factorial_bounds_iff_power_bound`

These include the uniform-family equivalence with a common threshold.
The source argument is the corpus's
factorial-moment exponential-window proof; the exact exponential-series,
geometric-series, and norm-comparison declarations have been read in mathlib
after the corpus search. Both actual targets in
`FactorialOrderOneInTheVaughanConvolutionIsAPowerSaving.lean` passed the final
direct check, with standard axioms only and no warnings. The module is wired
and its scratch removed:

- `uniform_pmUndampedVaughan_factorial_bounds_iff_power_bound`
- `zetaZeroAbscissa_lt_one_iff_uniform_pmUndampedVaughan_factorial_bounds`

Its undamped-power dependency is now checked in
`UniformVaughanPowerBoundsAreFixedStrips.lean`: all four targets passed final
direct checks and standard-axiom audits, covering the exact unit/full-cutoff
value, every gain `κ<η/(2+η)`, the extreme-cutoff converse, and the uniform
power/fixed-strip equivalence. The optimized cutoff
is `D=floor(n^(1/(2+η)))`; the strict gap absorbs the harmonic logarithms.
The forward harmonic bound with constant `C(1+1/η)` and its exact strict-tail
identity are now Lean-verified in
`RHTower/MertensPowerBoundsControlMobiusHarmonicSums.lean`. Both targets passed
their final direct checks and standard-axiom audits. The harmonic-power
converse is verified in `TheExtremeVaughanCutoffReadsItsHarmonicSum.lean`.
No fixed strip or Q-I completion is claimed.
