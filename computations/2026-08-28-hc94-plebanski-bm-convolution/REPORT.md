# HC94 BM–Plebanski convolution experiment

Date: 2026-08-28

Status: exploratory route-selection evidence only. These results are not mathematical proof and
must never be imported, cited, or encoded as premises in a Lean proof.

## Question tested

Could the corner-renormalized Birmingham–Mokhtari (BM) `++` forbidden branch be annihilated after
convolution with the corpus's abstract unequal-charge Plebanski Mellin vertex? The scan tested the
constant-curvature proxy already formalized in:

- `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingSelfDualGeneralMellinVertex.lean`
- `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSecondHarmonicCornerRenormalizedSecondDerivative.lean`

The exact beta–hypergeometric identity evaluated was

```text
I_j = B(beta, alpha+j)
      * 3F2(a, b, beta; 1/2, alpha+beta+j; 1),  j=0,1,2,
```

with BM parameters transcribed from the Lean corpus, response weight
`alpha = 4n+2+rho`, negative-branch weight `beta = 2-rho/2`, and the exact forbidden connection
Gamma quotient. The proxy convolution was

```text
A_forbidden/2 * (P2*I_2 + P1*I_1 + P0*I_0),
P2 = (h+k)^2,
P1 = -2h(h+k) - c(h-k)(h+k),
P0 = h^2 + c(h-k)h.
```

Three unresolved charge assignments were tested and explicitly treated as models, not physics:
`k=1-rho/2` (reflected), `k=h` (same), and `k=-h` (opposite), with `h=rho`.

## Run and validation

- RunPod: 128 logical CPUs exposed; 32 Python worker processes; observed average utilization about
  8.2 cores (`34m00s` user time over `4m07.7s` wall time), consistent with a scheduling quota.
- Precision: 90 decimal digits; representative recomputation at 60 digits.
- Main grid: 135 cases from three zeta-zero heights, five real parts
  `0.2,0.35,0.5,0.65,0.8`, modes `n=0,1,2`, and three charge models.
- Independent check: direct quadrature versus beta–`3F2` evaluation.
- Maximum 60/90-digit relative difference: `4.0994e-66`.
- Maximum hypergeometric/quadrature relative difference: `1.2436e-95`.

## Output

For proxy curvature `c=1`, every sampled convolution was nonzero, including every critical-line
case. Minimum absolute values over the main grid were:

| charge model | all cases | critical line |
|---|---:|---:|
| reflected | `6.4065e-11` | `7.2844e-11` |
| same | `1.9930e-10` | `2.1932e-10` |
| opposite | `2.5950e-10` | `2.8716e-10` |

At the first zero height and `n=0`, a beta scan from `0.05` to `0.95` found no zero. The proxy also
failed simple even, odd, and conjugate reflection tests under `beta -> 1-beta`.

Exact SymPy elimination for `r=k/h` factored the proxy kernel as

```text
((r+1)t - 1) * ((r+1)t + c(r-1) - 1).
```

Within this constant-curvature proxy, the unique profile-independent annihilator is
`r=-1, c=-1/2`; same charge gives `(2t-1)^2` and is independent of `c`.

## Interpretation and route consequences

The important negative result is that the constant-curvature proxy is not the physical AdS4 radial
vertex. Lipstein–Nagy give

```text
V_SDG = 1/2 X(k1,k2)
        * [X(k1,k2) - 2i/(u-v) (k1-k2)_w],
```

so the deformation is radial (`u-v=2z`), not a constant. The full light-cone action for arbitrary
radial propagators further replaces `X` by an operator containing left/right `z` derivatives and
acts on `P/z` and `Q/z`. See
[arXiv:2304.07141](https://arxiv.org/abs/2304.07141) and
[arXiv:2411.04172](https://arxiv.org/abs/2411.04172).

Consequences:

1. Do not interpret `k=-h, c=-1/2` as a physical cancellation. It is an exact classification only
   inside the abstract constant-curvature proxy.
2. Retire further numerical work on that proxy. Its sampled nonvanishing and lack of simple
   reflection covariance do not decide HC94.
3. The computation supports the already Lean-proved obstruction that regularity/corner subtraction
   alone does not erase the BM forbidden branch, but supplies no proof of it.
4. Next route-changing burden is analytic: derive the coefficient-normalized physical radial
   differential vertex, including its `1/z` term, left/right derivatives, negative-helicity leg,
   boundary/corner completion, and left-QNM projection. Only then test universal annihilation or
   nonvanishing. No further special-function scan is justified before that derivation.
5. Nothing here kills the full HB, FZZ-P, RBH, or PW-B routes. It kills only the constant-curvature
   shortcut as a faithful physical model.

## Files

- `compute.py`: parallel 90-digit evaluation and independent checks.
- `raw-results.json`: complete numerical output.
- `analyze.py`, `analysis-summary.json`, `analysis-table.csv`: compact summaries.
- `symbolic_vertex.py`, `symbolic-vertex.json`: exact proxy-kernel factorization.
- `run-time.txt`, `run-summary.json`: runtime and raw-output digest.
- `SHA256SUMS`: integrity manifest.

