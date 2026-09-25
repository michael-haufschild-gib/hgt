# EDQ divisor-ratio and reduced-denominator diagnostics

Both frozen localization predictions were numerically reversed. The first
diagnostic's predeclared classification is **MIXED**, not CROSS-RATIO
CANCELLATION. No asymptotic claim or RH bound follows from these finite data.

## Complete divisor-ratio decomposition

The [protocol](PROTOCOL.md) fixes nine cutoffs and measures
`S_L=-sum_(e<=N,N<d<=L*e)mu(d)mu(e)K(d,e)`. Its full remainder is
`T_L=R_N-S_L`, using the saved complete-flux enclosures. Every kernel retains
its infinite time series. Divisor ratio d/e is distinct from the temporal
separation tested in the earlier experiment.

The working prediction required every ratio-four relative error to be at
most 1/4. It failed at N=48,64,96. No ratio-four lower error exceeds one.

| N | Lower bound for abs(T_4)/R_N | Upper bound |
|---:|---:|---:|
| 32 | 0.15139 | 0.15180 |
| 48 | 0.34391 | 0.34451 |
| 64 | 0.32315 | 0.32385 |
| 96 | 0.30644 | 0.30781 |
| 128 | 0.23233 | 0.23349 |
| 192 | 0.16757 | 0.16952 |
| 256 | 0.17765 | 0.18012 |
| 384 | 0.20679 | 0.21018 |
| 512 | 0.24184 | 0.24741 |

Displayed endpoints are rounded outward. Every tested (16,32] band is
negative and every (32,64] band positive. Increasing L from 16 to 32 makes
the approximation worse in all nine cases. The ratio-64 upper relative errors
are below 0.00444 here, but that cutoff was not the primary criterion and is
not promoted into a new uniform claim. Complete signed bands and remainders
are preserved in [results.json](results.json).

## Attribution by reduced denominator

The separately frozen [follow-up protocol](ray_PROTOCOL.md) tests a proposed
explanation of the distant bands. For d=r*a,e=r*b with coprime a,b,

```
K(r*a,r*b)=K(a,b)/r,
mu(r*a)*mu(r*b)=mu(a)*mu(b)*mu(r)^2*[gcd(r,a*b)=1].
```

Each fixed reduced pair has a fixed sign, while the actual allowed r interval
depends on N. The tested prediction was that b<=4 explains each distant band
within 25% at every cutoff. Only b=2,3 contribute to that selection.

This prediction also failed. Its selected (16,32] contribution is positive
at every tested cutoff, although the complete band is negative. At N=32,
the selected interval is [0.0006486418,0.0006486666], the complete band is
[-0.0009340690,-0.0009340391], and the omitted b>4 contribution is
[-0.0015827356,-0.0015826809]. The relative discrepancy exceeds one in
all nine (16,32] cases. The (32,64] selection also fails the 25% criterion
at several cutoffs. All other predeclared b cutoffs remain diagnostics;
none replaces the failed b=4 prediction. See [ray_results.json](ray_results.json).

## Validation and resources

Both experiments ran only on the authorized RunPod, with eight Python workers,
native numerical threads one, and separate 120-second external limits.
Successful runtimes were 0.381 and 0.787 seconds. The first execution reached
output serialization after its controls and computation but failed on a NumPy
integer. The only correction converted that count to a Python integer; no
mathematics, input, cutoff or classification changed, and no numerical outcome
had been printed. The original [script](experiment.v1.py), input hashes and
[failure log](run.failed-serialization.log) are retained.

Controls passed: direct-factorization Möbius checks, all divisor identities
through 32768, 262144 saved periodic kernel comparisons, four independent
new-pair time-series bounds, three complete-column identities with their
omitted tails, and the exact N=2 formulas. The follow-up passed 10144 kernel
and coefficient homothety checks and full-band reconstruction at N=32,96.

Inputs were hash-verified remotely; both downloaded output sets were checked
against their remote hashes. Both experiment processes were confirmed ended.
Owned remote files, the imported-module bytecode and both owned directories
were removed. No Lean process or build was involved in either experiment.

The calculations reuse floating evaluations of analytic enclosures with a
separate 1e-8 margin. They are **not certified interval arithmetic** and have
no proved floating-point error bound. No value is admitted into Lean.

## Effect on the proof attempt

The data reject concentrating the proof on ratio<=4 or on the b=2,3 rays.
They do not reject balanced-range methods or all fixed-denominator estimates.
The complete signed reduced-denominator remainder must stay in the argument.

An independent paper estimate bounds the entire b<=B head by B/2, uniformly
in N, including unbounded numerator and time tails. It uses only the modular
primitive bound and two reciprocal-square tail estimates; it does not rely on
these data. Its [formalized proof card](../../../3-formalized/edq-reduced-denominator-head.md) separates
that bounded part from the missing b>B estimate. RH remains unresolved.
