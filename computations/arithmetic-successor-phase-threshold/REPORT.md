# A candidate linear cutoff for the ordinary remainder's phase

**Numerical evidence only.** The proposed cutoff remains unproved. All evaluation ran on the specified Runpod; no output is used as a Lean proof input.

## Question

For `s=sigma+it`, define the literal ordinary remainder

`R_s(n)=sum_(j=1..n)j^(-s)-zeta(s)-n^(1-s)/(1-s)-n^(-s)/2`

and `g_s(n)=n^(-s)conjugate(R_s(n))/[conjugate(s)(conjugate(s)+1)]`.

Frozen conjecture R asserts `Im(g_s(n))<0` whenever `sigma>0`, `t>0`, `n>=1`, and `t<2*pi*n`. It is a `[BRIDGE]` to controlling a finite exceptional head, not an RH criterion. The existing fixed-parameter asymptotic sign does not settle this height-dependent threshold.

The conjecture arose from the corpus's exact Bernoulli-tail representation. With `x=n+y`, the phase derivative `t/(n+y)` starts below the first periodic-cell frequency when `t<2*pi*n`. That observation motivates a test; it does not prove a sign.

## Evaluation and results

`scan.py` evaluates a fixed grid of 1,008 triples: seven real parts from `0.001` through `32`; nine cutoffs from `1` through `512`; sixteen ratios `t/(2*pi*n)` from `0.001` through `2.1`. Eight worker processes use one BLAS thread each, with Python 3.8.10 and mpmath 1.3.0. The full grid and results are retained in `results.json`.

Evaluation uses the exact Hurwitz-tail expression, in dimensionless form:

`n^(2*sigma+2) g_s(n) = n^2[-n^u zeta(u,n+1)-n/(1-u)-1/2]/[u(u+1)]`, `u=conjugate(s)`.

- All 567 grid points satisfying R's strict cutoff had negative imaginary part.
- Among 441 points at or above the cutoff, 118 had positive imaginary part.
- The scan therefore does not falsify R. It does not establish R, sharpness of `2*pi`, an all-height bound, or any claim about zero locations. These grid points were not selected as zeros.

An initial fixed 55-digit run produced five apparent violations at `sigma=32`. Those results were invalidated by precision loss in extremely small Hurwitz tails. The corrected scan uses `85+ceil(sigma)*decimal_digits(n)` digits. The discarded run is retained as `initial-fixed-precision-results.json` for numerical provenance; its signs must not be used as mathematical evidence.

`verify.py` checks all five discarded violations and four additional boundary/control points by a different evaluation path: the ordinary finite prefix minus Riemann zeta. Precision ranges from 131 to 226 digits, compared with a Hurwitz evaluation at another 40 digits. The nine method differences were below `5e-133`; this is a stability check, not an interval error certificate.

| Verified point `(sigma,n,t/(2*pi*n))` | Scaled imaginary part |
|---|---:|
| `(32,128,0.05)` | `-0.158944409766270179724347080800` |
| `(0.001,512,0.9999)` | `-0.209452925448967987355322986764` |
| `(0.5,4,1.3)` | `+0.007854312832261696513618029165` |

## Consequences and next proof obligation

R remains a candidate uniform source estimate. If proved, it would bound where the exceptional coefficients can occur, but it would not force their contribution at the unit term to cancel. In particular, it supplies no unit sign at a height above `2*pi`.

A separate symbolic audit rules out a tempting proof strategy. At the exact height `pi/log(2)`, complete cells beginning at `2^k` alternate in sign forever. Thus absence of a stationary phase and negativity of the periodic quadratic do not yield cellwise negativity. A proof of R must retain cancellation across different cells. The [research card](../../../1-in-progress/arithmetic-successor-phase-threshold.md) separates this exact obstruction from the unproved whole-tail conjecture.

The underlying representation and recurrence are classical; see [DLMF 25.11.3–6](https://dlmf.nist.gov/25.11#iii). Modern complex remainder estimates are studied in [Nemes, 2017](https://arxiv.org/html/1702.05316v2). The checked statements do not establish R, and this bounded literature check cannot establish novelty.

## Reproduction

Remote folder: `/root/rh-successor-phase-threshold-20260906`. Run `python3 scan.py`, then `python3 verify.py`; the latter uses the retained initial-run JSON to select the five precision failures. The scripts contain the full fixed grids and enforce one BLAS thread per worker. All outputs were downloaded to this folder. No exploratory mathematics ran locally.
