# The entire regularized Fredholm determinant of a Hilbert-Schmidt operator

- **ID:** `entire-regularized-fredholm-determinant`
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) / MISSING INFRASTRUCTURE
- **Statement:** For a Hilbert-Schmidt `K`, the Hilbert-Carleman determinant `det_2(1 - zK)` is an
  entire function of `z` of order at most two, nowhere zero off the reciprocal spectrum, vanishing
  at `1/lambda` to the algebraic multiplicity of the eigenvalue `lambda`, and satisfying
  `logDeriv det_2(1 - zK) = -resolventTrace K z` wherever the resolvent exists.

## Why this card exists

Three cards of the `hedenmalm` folder are blocked on exactly this object and on nothing else:

| card | blocked clause |
|---|---|
| `hedenmalm-theta-source-compressed-inverse-determinant` | `(8)` `det_2(I + zB) = Xi_C(z)/Xi_C(0)`, and the multiplicity clause of `(6)` |
| `hedenmalm-prime-translation-rank-one-anomaly` | the Jordan-length half of `(16)`, which quotes that multiplicity clause |
| `hedenmalm-essential-inverse-flow-prime-tomography` | the Riesz projections, the punctured trace `(4)`, the cutoff-independent limit `(1)`, the divisor sum `(5)` and the prime--Gamma sampling `(6)`, all inherited |

## The corpus object is not this object

`formal/GaloisForLFunctions/HTGeometry/FredholmDeterminant.lean` defines

```text
HilbertSchmidt.fredholmDet K z = Complex.exp (- fredholmExp K z),
fredholmExp K z = sum over n >= 2 of z^n / n * tr(K^n),
```

and the exponent series converges only for `‖z‖ * ‖K‖_HS < 1`.  Consequences, all of them proved in
that file:

* `fredholmDet_ne_zero` is literally `Complex.exp_ne_zero` --- the object is **nowhere zero by
  construction**;
* `logDeriv_fredholmDet` and `fredholmDet_weld` are stated **only on `Metric.ball 0 r`** with
  `r * ‖K‖_HS < 1`.

So `fredholmDet` is the local exponential representative of `det_2` inside the first eigenvalue, not
`det_2`.  Any target whose right-hand side has zeros --- `Xi_C(z)/Xi_C(0)` in particular --- is
unreachable with it, at any level of effort.  What *is* reachable is the disc-local identity

```text
fredholmDet thetaKernelMatrix z = c * Xi_C(z)/Xi_C(0)   for |z| < 1/‖B‖_HS,
```

which still requires the trace formula `resolventTrace = -Xi_C'/Xi_C` on that disc.

## Two routes

**Route A --- Plemelj--Smithies.**  Define the coefficients by the recursion
`d_0 = 1`, `n d_n = sum over j from 1 to n of (-1)^(j+1) sigma_(j+1) d_(n-j)`, with
`sigma_k = tr(K^k)` (finite for every `k >= 2` because `K^k` is trace class), and set
`det_2(1 - zK) = sum over n of d_n z^n`.  The formal identity with `exp(-fredholmExp)` is a routine
power-series manipulation; the whole content is **Carleman's bound**
`|d_n| <= (e/n)^(n/2) ‖K‖_HS^n`, which is what makes the series entire of order two.  That bound is
proved classically from Hadamard's determinant inequality applied to the exterior-power
representation, so Route A does not really avoid exterior powers --- it only postpones them.

**Route B --- exterior powers.**  Build `Lambda^n K` on `Lambda^n H`, prove
`‖Lambda^n K‖_1 <= ‖K‖_HS^n / n!^(1/2)` (Hadamard), and define
`det_2(1 - zK) = sum over n of z^n tr(Lambda^n (K)) * (regularisation)`.  This is the honest route
and it gives the multiplicity statement directly, because the order of vanishing of the determinant
at `1/lambda` is the algebraic multiplicity by construction.  mathlib has exterior powers of modules
(`ExteriorAlgebra`, `Module.exteriorPower`) but no Hilbert-space completion of them and no trace
ideal theory on them.

## Gates
- [x] 0 -> 1  the obstruction is identified exactly and the corpus object is classified
- [ ] entire `det_2` defined, with the order-two growth bound
- [ ] `det_2(1 - zK) = 0` iff `1/z` is an eigenvalue
- [ ] order of vanishing = algebraic multiplicity
- [ ] Plemelj identity on the full resolvent set
- [ ] 1 -> 2  paper proof complete
- [ ] 2 -> 3  Lean

## Log
- 2026-08-08 — created; the corpus `fredholmDet` classified as disc-local and nowhere zero, which
  rules out the route the three parent cards had recorded.  Their Lean-status sections corrected.
