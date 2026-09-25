# Complete EDQ reciprocal flux: frozen sign diagnostic

The prediction survives this finite test: N=1 is exactly zero and all 511
cutoffs N=2,...,512 were classified positive. There were no negative or
unresolved cases. This is numerical evidence about a sign, not a proof of
uniform positivity, a growth bound, or RH.

## Execution and validation

The unchanged [protocol](PROTOCOL.md) and [script](experiment.py) ran on the
authorized RunPod with eight worker processes and one native numerical
thread per worker. Runtime was 0.669 seconds, under the frozen 120-second
timeout. Python 3.8.10, NumPy 1.24.4, and a 63-bit longdouble mantissa were
recorded. No mathematical computation ran locally.

The complete infinite kernel was enclosed using the protocol's analytic
series-tail bounds. These are floating-point evaluations of analytic
bounds, **not certified interval arithmetic**. The separate classification
margin was the predeclared 1e-8; there is no proved floating-point error
bound. The largest analytic enclosure width was approximately 0.000150332.

| Cutoff | Computed lower endpoint | Computed upper endpoint |
|---|---:|---:|
| 2 | 0.05842501848 | 0.05842525644 |
| 13 | 0.02308689555 | 0.02309024837 |
| 512 | 0.03361219969 | 0.03376253139 |

The minimum upper endpoint among nonzero cutoffs occurred at N=13.
The N=2 closed formula lay inside its kernel enclosure. Independent literal
time-source evaluations at N=2,7,31, each with its full omitted-tail bound,
overlapped the kernel enclosures. Direct finite quadratic summation agreed
with the cutoff recurrence at N=31,127,512, with largest observed endpoint
discrepancy below 4.2e-18. All required divisibility-zero and initial divisor
identity controls passed. Every cutoff is retained in [results.json](results.json);
both complete kernel-bound matrices are in [kernel_bounds.npz](kernel_bounds.npz).

Frozen input hashes were verified on RunPod. Downloaded results, matrices
and log were verified against RunPod's [output hashes](OUTPUT_SHA256SUMS).
No experiment process remained at cleanup. Only this experiment's seven
remote files and its owned directory were removed.

## Mathematical consequence and remaining obstacle

The test did not expose a negative cutoff. It supports pursuing an actual
sign identity without selecting a favorable subsequence or changing the
frozen range. It does not establish that such an identity exists. No larger
scan or fitted bound was run after observing the result.

The ensuing paper calculation on the [active EDQ card](../../../1-in-progress/edq-full-covariance-core-attack.md)
rewrites this same complete flux as a weighted gradient square **minus a
positive-weight primitive square**, plus its exact mean and lower-boundary
terms. Thus the calculation retains an arithmetic estimate; it does not
give termwise positivity. Moreover, even a proof of nonnegativity would
not give the subpower upper bound needed for the EDQ producer.

No new uniform arithmetic bound or Lean theorem resulted from this
diagnostic. No numerical value enters Lean. The frontier map was not edited.
