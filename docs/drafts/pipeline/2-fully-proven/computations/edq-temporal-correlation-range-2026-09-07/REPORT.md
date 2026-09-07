# EDQ temporal correlation range

Status: completed numerical experiment; **not a proof of an asymptotic bound or RH**.
The directory records computations, not a claim that the research question is fully proven.

The frozen protocol tested whether short temporal correlations approximate
the actual compensated covariance. The result is **NONLOCAL** under its
predeclared rule: all seven averaged-source discrepancies at radius X exceed
the complete finite energy. No parameters or thresholds changed after data.

## Actual source and observable

For X=2^k, k=10,...,16, T=256X, compute both the raw Möbius cutoff X and the
logarithmic cutoff average over [X,4X). For each, let a(d) be its literal
arithmetic coefficient, H=sum a(d)/d, g(n)=sum_(d|n)a(d),
c(n)=[n=1]-g(n)+H and S(n)=sum_(k<=n)c(k).

Compare `E=sum_(n<=T)S(n)^2/[n(n+1)]` with the signed covariance retaining
only pairs at distance at most h. Its diagonal is included for every h.
The exact pair kernel is `1/max(j,k)-1/(T+1)`.

## Averaged-source results

Values below are rounded displays of the downloaded results. "Omitted/E"
means the absolute omitted covariance divided by the complete finite E.

| X | E | h=X signed covariance | h=X signed omitted contribution | sqrt(X) omitted/E | X omitted/E | 64X omitted/E |
|---:|---:|---:|---:|---:|---:|---:|
| 1024 | 0.02019891839 | -0.1548877341 | 0.1750866525 | 61.3800 | 8.6681 | 1.3481 |
| 2048 | 0.02108727179 | -0.3783857085 | 0.3994729803 | 59.5613 | 18.9438 | 0.6760 |
| 4096 | 0.02099060915 | -0.0962505915 | 0.1172412006 | 54.9019 | 5.5854 | 0.2020 |
| 8192 | 0.02150674879 | -0.1546328707 | 0.1761396195 | 55.6870 | 8.1900 | 0.1647 |
| 16384 | 0.02166804999 | -0.1829174595 | 0.2045855094 | 56.9211 | 9.4418 | 1.1425 |
| 32768 | 0.02116577540 | -0.1994780002 | 0.2206437756 | 57.2770 | 10.4246 | 1.1719 |
| 65536 | 0.02133359899 | -0.09743376878 | 0.1187673678 | 56.7992 | 5.5672 | 0.7178 |

All h=X averaged covariances are negative. Their positive omitted terms
restore the positive finite energy. Thus these band truncations are neither
the physical energy nor valid upper bounds. The raw-source controls have
both signs for the omitted contribution; complete values at all nine radii
are in `results.json` and `analysis.txt`.

The observation rejects using either tested short radius as an accurate
standalone approximation. It does not rule out a short-interval method
that proves a bound for omitted correlations, nor identify temporal
distance with arithmetic-modulus ratio. The evidence redirects the direct
proof attempt toward signed arithmetic correlations across the full range.

## Validation and limits

All Möbius factorization, cutoff-weight suffix, initial-prefix and direct
divisor/floor checks passed. Across both sources and all seven scales,
the largest discrepancy between independent finite-energy and full-pair
covariance evaluations was `1.111307226797642e-18`; the largest direct
cumulative-coordinate discrepancy was `5.290212712338871e-14`.
These are floating-point checks, not rigorous error intervals.

The horizon is finite. For example, the available omitted infinite-energy
upper bound reaches `443.08483815817436` for the averaged source at the
largest scale. The experiment therefore cannot certify a small full norm,
an asymptotic cancellation rate, or the cofinal subpower bound required by EDQ.

## Execution and artifacts

Execution used the authorized RunPod, seven independent workers and one
thread per BLAS runtime, under an external 180-second deadline. The unchanged
experiment completed in `8.657689437270164` seconds. Environment: Python
3.8.10, NumPy 1.24.4, long-double mantissa 63 bits; host reported 16 available
processors via `nproc` and 32 via `os.cpu_count()`.

`PROTOCOL.md` is the design frozen before execution. `experiment.py`,
`results.json`, `run.log`, `analysis.py`, `analysis.txt` and `SHA256SUMS`
preserve the executed code, full observations and checks. Analysis ran on
RunPod. No numerical result is used in a Lean proof. This turn adds no Lean
declarations, performs no Lean builds and does not repeat prior axiom audits.
Downloaded artifacts passed their RunPod SHA-256 checks. No process retained
the experiment directory at cleanup; its seven remote files and directory
were removed. The report's local bookkeeping hash is also in `SHA256SUMS`.
