# Quarter-scaled stabilizer is not raw-centered

- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Route:** Argon §4.1; raw arithmetic normalization only.

## Killing theorem

The literal scalar 1/4 in `stabilizerModelOddCoalSum` gives complete-period
raw mean 1/8. More strongly, at conductor cutoff Q and odd-coordinate length Q²,
actual distinct odd-prime logarithmic weight minus this model has normalized
limit 7/8 (`squareScaleStabilizerDiscrepancy_quarter`). Thus it is not a raw
mean-one replacement for the prime weight.

## Positive survivor

Scalar two uniquely centers the actual raw prime rectangle. Every incomplete
period has nonnegative full-rectangle excess at most `2Q³`; row, diagonal, and
distinct-pair boundary errors are explicit. These results are
[proved and formalized](../3-formalized/stabilizer-incomplete-periods-and-prime-comparison.md),
with nineteen standard-axiom audits across three checked leaves.

## New insight and scope

Odd-coordinate restriction already supplies the density factor in the counting
measure. The packet has conditional mean two, so scalar two is needed to obtain
full-rectangle mean one. The source's density-matching comment is corrected;
its definitions and exact subtraction identity retain their literal meanings.
The signed narrow-aperture route remains open: its Fourier kernel can cancel
constant raw errors, and correct raw centering does not control phase resonance.
