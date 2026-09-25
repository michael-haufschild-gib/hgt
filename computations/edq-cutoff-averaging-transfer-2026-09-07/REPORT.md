# EDQ logarithmic cutoff averaging: finite experiment

Frozen classification: **mixed**. All fourteen measured post-support ratios
are below one, but they do not meet the predeclared strong-suppression criterion.
None of the seven width-four ratios meets the persistent-error threshold.
These are finite numerical observations, not asymptotic theorems or RH evidence
usable in Lean. This directory's pipeline location does not give the numerical
conclusion formal-proof status.

The primary ratio is the averaged target-error energy on `(M,256X]` divided by
the raw endpoint's target-error energy on the same coordinates, with
`X=2^k` and `M=width*X`.

| k | width 2 ratio | width 4 ratio |
|---|---:|---:|
| 10 | 0.475519 | 0.152376 |
| 11 | 0.300004 | 0.298957 |
| 12 | 0.532084 | 0.218283 |
| 13 | 0.480624 | 0.275491 |
| 14 | 0.501138 | 0.241070 |
| 15 | 0.470730 | 0.392510 |
| 16 | 0.700958 | 0.390138 |

The observed suppression extends beyond the averaging support. Its scale
dependence is not monotone. A proof candidate can retain logarithmic averaging,
but still needs control of the full compensated tail and a bound sufficient
for the actual chronological current. Jensen's inequality compares with an
average of input energies, so it does not supply this endpoint comparison.

The omitted-tail bounds are far too loose to turn these measurements into
full-energy comparisons. For example, at `X=65536`, width four, the measured
post-support energy is `0.01400635`, while the recorded omitted target-tail
upper bound is `443.08484`. No inference about convergence, boundedness, or
subpower growth follows from this experiment.

Execution: authorized RunPod, seven independent worker processes, BLAS threads
one, 240-second external deadline. Completed in 9.867 seconds. Python 3.8.10,
NumPy 1.24.4, long-double mantissa 63 bits. `nproc` reported 16 available CPUs;
Python reported 32 logical CPUs. No local numerical run occurred.

Validation passed: integer Möbius sieve against fixed direct factorizations;
logarithmic coefficients against suffix sums of cutoff weights; raw and
averaged initial floor identities; independently summed fixed coordinates.
The script, frozen protocol, complete block data, console log, and verified
SHA-256 hashes are retained alongside this report. There was one numerical
run, with no parameter revision or failed validation.

Exact finite-sum identities and the surviving initial-source separation are
tracked separately in the [formal source card](../../../3-formalized/edq-cutoff-averaging-transfer.md).
