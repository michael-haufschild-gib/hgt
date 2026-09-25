# Logarithmic weighting of the complete gcd Gram groups

Status: frozen before execution; NOT RUN. The prescribed RunPod SSH endpoint
refused connections on 2026-09-11. No numerical result is asserted.

The previous experiment found small total variation of complete gcd groups
at eight raw/tapered examples. The new, unknown question is whether the
logarithmic weight created by cutoff-history polarization preserves that
cancellation. This is a diagnostic for choosing between two estimates, not
a conjectured universal constant or evidence already sufficient for RH.

Use the literal raw coefficients and the original compensated Gram:

```
G(m,n) = sum_(k>=1) ((k mod m)/m)*((k mod n)/n)/(k*(k+1)),
C_r(N) = sum_(m,n<=N, gcd(m,n)=r) mu(m)*mu(n)*G(m,n),
L_r(N) = sum_(m,n<=N, gcd(m,n)=r)
           mu(m)*mu(n)*log(max(m,n))*G(m,n),
D(N) = sum_(m<=N) mu(m)^2*G(m,m),
Dlog(N) = sum_(m<=N) mu(m)^2*log(m)*G(m,m).
```

Freeze both tests at every integer cutoff 2 through 128:

1. `sum_r |C_r(N)| <= 4*D(N)` (the earlier diagnostic, now including all cutoffs).
2. `sum_r |L_r(N)| <= 4*Dlog(N)` (new logarithmic diagnostic).

The factor four is inherited from the previous test, not fitted. Report all
cutoffs and signed groups, including every failure and inconclusive result.
If test 2 fails where test 1 passes, logarithmic weighting has destroyed a
groupwise cancellation budget at this constant: prioritize the original
groups. If test 2 passes throughout, attempt its actual arithmetic estimate;
finite survival is not a proof. If both fail, retain correlations between
gcd groups instead of forcing a separate-group bound.

The motivation for test 2 is the exact finite identity, for actual compensated
source energy E(N),

```
sum_r L_r(N) = log(N)*E(N)
              - sum_(1<=k<N) log((k+1)/k)*E(k).
```

No raw/compensated source substitution is used in the experiment. An
eventual analogue of test 2 with a proved cutoff-independent constant
would be useful because `Dlog(N)=O((log N)^2)`. Neither that analogue nor
an RH estimate is assumed.

Compute the Gram once at the maximum cutoff, using four independent
processes over disjoint physical-coordinate ranges. Set native BLAS thread
counts to one. Each worker uses bounded matrix chunks. No local execution
of the numerical program is permitted.

For every non-unit pair, the omitted Gram tail after K is nonnegative and
at most `1/(K+1)`. Choose K before inspecting signs so that
`log(128)*(sum_(2<=n<=128)|mu(n)|)^2/(K+1) <= 0.02`.
Propagate positive and negative coefficient counts separately to each
group's lower and upper allowance. Retain corresponding diagonal tails.
Floating-point margins and analytic truncation allowances must be labeled
separately; these are not machine-certified intervals.

Controls: compute complete truncated source energies independently by
cumulative signed rows; compare against Gram reconstruction at every
cutoff. Check the logarithmic history identity at every cutoff. Check
`G(2,2)=log(2)/4` against its analytic tail allowance. Validate the first
small Gram by direct rational summation. Controls support implementation
checks only; no result enters Lean.

Run on `root@157.157.221.29:27094` with the specified SSH key, a 150-second
external wall limit, and a 120-second cooperative worker deadline. Do not
increase cutoffs, change thresholds, or launch a long retry after seeing
results. Download results and execution logs into this directory. Clean
up only this experiment's remote directory and processes after download.
