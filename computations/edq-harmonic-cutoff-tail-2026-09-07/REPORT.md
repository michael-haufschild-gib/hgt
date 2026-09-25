# Harmonic cutoff selection leaves a substantial measured tail

Numerical evidence only. The frozen diagnostic classified the result as
**persistent complementary tail**. No numerical result enters Lean.

For each dyadic range, the selected cutoff minimizes abs(sqrt(N)*H_N) using
only harmonic data. Tail errors below mean the finite weighted target error
on N<n<=128N, not the entire infinite tail.

| Range exponent k | Selected N | N*H_N² | Selected tail error | Tail / midpoint tail | First block / selected tail |
|---:|---:|---:|---:|---:|---:|
| 10 | 1558 | 9.760e-5 | 0.035190 | 1.023 | 0.5983 |
| 11 | 2161 | 4.463e-8 | 0.040004 | 1.151 | 0.6926 |
| 12 | 5297 | 9.947e-7 | 0.038419 | 1.069 | 0.5485 |
| 13 | 15045 | 9.789e-7 | 0.037902 | 0.8628 | 0.5576 |
| 14 | 30254 | 1.722e-6 | 0.037625 | 0.6617 | 0.6285 |
| 15 | 56359 | 1.154e-12 | 0.036394 | 0.5785 | 0.5660 |
| 16 | 81017 | 2.044e-9 | 0.040567 | 0.9104 | 0.4909 |

All seven tail ratios exceed the preregistered 0.5 threshold. Suppressing the
initial scalar error by many orders does not produce comparable suppression of
the measured complementary tail in these ranges. Roughly half to two-thirds of
that tail lies in the first block N<n<=2N. Maximum-defect controls, midpoint
controls, harmonic sign crossings, every block, and omitted-tail bounds are
retained in results.json; no energy-dependent cutoff selection was used.

The result directs the next arithmetic comparison toward the actual Mertens
increment field M(n)-M(N). On the first block the corpus identities give exactly
1-F_N(n)=n*H_N+M(n)-M(N). The finite diagnostic therefore exposes a concrete
remaining source component, rather than only observing that a tail exists.
Its [formal first-tail decomposition](../../../3-formalized/edq-harmonic-cutoff-tail.md)
is proved independently from the identities, not from these numbers.

## Limits

These are finite nonnegative partial energies. Terms beyond 128N are unevaluated;
the explicit crude upper bounds retained in results.json are generally too large
to estimate the full norm. Floating-point output is not an interval certificate.
The experiment neither proves a positive asymptotic tail floor nor rules out an
absolute cofinal logarithmic ceiling. In particular, an error around 0.04 is
fully compatible with such a ceiling. It does not prove/falsify RH or retire
the possibility of useful selected cutoffs.

## Validation, failure, and execution

The first run failed exact divisor-sum validation before emitting energy rows.
The sieve zeroed multiples of p after p² instead of multiples of p². The failed
script and log are preserved as experiment-invalid.py and run-invalid.log.
After correcting this implementation error, the same frozen design passed:

- Exact initial floor identity at every coordinate through N, for all 21 slots.
- Exact first-block Mertens identity at every coordinate through 2N.
- Six deterministic direct integer floor-sum checks per distinct cutoff.
- Harmonic sums versus compensated summation: maximum difference 8.674e-18.
- Initial energy versus its exact scalar formula: maximum difference 2.020e-28.

The corrected run used eight independent processes on the prescribed RunPod
host (32 available CPUs), with internal NumPy threads capped at one. Runtime:
2.2267 seconds, below the 240-second timeout. Python 3.8.10, NumPy 1.24.4,
long-double harmonic sums and energies; exact int64 divisor sums. The successful
script hash is recorded in results.json. Scripts, design, results, logs and
SHA-256 manifest are downloaded here. No numerical experiment ran locally.
