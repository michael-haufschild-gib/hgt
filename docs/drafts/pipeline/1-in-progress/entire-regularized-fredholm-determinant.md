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

## Route C --- the one being built

Neither Route A nor Route B is taken directly.  The construction that is actually being formalized
is **finite sections plus Cauchy's estimate**, which produces the Carleman bound for free and needs
neither Hadamard's inequality nor exterior powers.

1. **Schur triangulation.**  `U^H M U = T` with `U` unitary and `T` upper triangular, for every
   complex square matrix.  Absent from mathlib; built here by induction on the size (eigenvector
   from a root of the characteristic polynomial, extended to an orthonormal basis, lower-right
   block by induction).
2. **The finite regularized determinant.**  `det_2(1 + zM) = det(1 + zM) exp(-z tr M)` is entire in
   `z`, and in Schur coordinates equals `prod_i (1 + z t_i) exp(-z t_i)`.  Two elementary facts give
   the growth bound:
   * the scalar inequality `|(1 + w) e^(-w)| <= exp(|w|^2/2)`, which is exactly `log u <= u - 1`
     applied to `u = |1 + w|^2 = 1 + 2 Re w + |w|^2`;
   * Schur's inequality `sum_i |t_i|^2 <= ‖M‖_HS^2`, the diagonal part of the unitarily invariant
     Hilbert--Schmidt norm of `T`.
   Together: `|det_2(1 + zM)| <= exp(|z|^2 ‖M‖_HS^2 / 2)`.
3. **Cauchy's estimate gives Carleman's bound.**  Because the finite determinant is *entire*, the
   estimate may be taken on a circle of arbitrary radius `R`, so every Taylor coefficient obeys
   `|a_n| <= exp(R^2 ‖M‖_HS^2/2) / R^n` for every `R > 0`.  Optimising `R` is Carleman's
   `(e/n)^(n/2) ‖M‖_HS^n`, but the optimisation is not needed: at a point `z != 0` the single choice
   `R = 2|z|` already turns the bound into `exp(2|z|^2 ‖M‖_HS^2) 2^(-n)`, a geometric series.  So a
   coefficient sequence with that bound defines an **entire** function.
4. **Passage to the limit.**  The truncations `K_s` of a Hilbert--Schmidt kernel satisfy
   `‖K_s‖_HS <= ‖K‖_HS`, so the coefficient bound is uniform in `s`.  On the disc
   `|z| ‖K‖_HS < 1` the finite determinants converge to the corpus object `fredholmDet K`, so their
   coefficients converge to its Taylor coefficients, and the limit coefficients inherit the bound.

### Lean built so far

```text
formal/GaloisForLFunctions/HTGeometry/SchurTriangulation.lean
formal/GaloisForLFunctions/HTGeometry/FiniteRegularizedDeterminant.lean
formal/GaloisForLFunctions/HTGeometry/EntireOrderTwoSeries.lean
```

| step | statement | Lean declaration |
|---|---|---|
| 1 | a complex matrix of positive size has an eigenvector | `exists_eigenpair` |
| 1 | a unit vector is the first column of a unitary matrix | `exists_unitary_col_zero` |
| 1 | **Schur triangulation** | `exists_schur_triangulation` |
| 2 | the Hilbert--Schmidt norm of a matrix and its unitary invariance | `matHSNormSq`, `matHSNormSq_eq_trace`, `matHSNormSq_conj` |
| 2 | the diagonal of a power of a triangular matrix | `diag_mul_of_blockTriangular`, `diag_pow_of_blockTriangular` |
| 2 | `det(1 + zM) = prod (1 + z t_i)`, `tr M = sum t_i`, `tr(M^m) = sum t_i^m` | `det_one_add_smul_eq_prod`, `trace_eq_sum_diag`, `trace_pow_eq_sum_diag` |
| 2 | **Schur's inequality** | `sum_diag_normSq_le_matHSNormSq` |
| 2 | `|(1+w)e^(-w)| <= exp(|w|^2/2)` | `norm_one_add_mul_exp_neg_le` |
| 2 | the finite regularized determinant, entire, in Schur coordinates | `finiteDet2`, `differentiable_finiteDet2`, `finiteDet2_eq_prod` |
| 2 | **the Carleman growth bound** | `norm_finiteDet2_le` |
| 3 | Taylor coefficients of an entire function | `taylorCoeff`, `hasSum_taylorCoeff` |
| 3 | **Cauchy's estimate, coefficient form** | `norm_taylorCoeff_le` |
| 3 | an order-two coefficient bound is everywhere summable | `summable_of_orderTwo_bound` |
| 3 | and defines an entire function | `entireOfCoeffs`, `hasDerivAt_entireOfCoeffs`, `differentiable_entireOfCoeffs` |
| 3 | **the Carleman coefficient bound**, uniform in the matrix size | `norm_taylorCoeff_finiteDet2_le` |

## Gates
- [x] 0 -> 1  the obstruction is identified exactly and the corpus object is classified
- [x] Schur triangulation in Lean
- [x] finite `det_2` and its order-two growth bound in Lean
- [x] Cauchy/Carleman coefficient bound, and entirety of such a series, in Lean
- [ ] truncation of a Hilbert--Schmidt kernel: `‖K_s‖_HS <= ‖K‖_HS` and `tr(K_s^m) -> tr(K^m)`
- [ ] entire `det_2` defined for a Hilbert--Schmidt kernel, agreeing with `fredholmDet` on the disc
- [ ] `det_2(1 - zK) = 0` iff `1/z` is an eigenvalue
- [ ] order of vanishing = algebraic multiplicity
- [ ] Plemelj identity on the full resolvent set
- [ ] 1 -> 2  paper proof complete
- [ ] 2 -> 3  Lean

## A cheaper route for the parent cards

For `hedenmalm-theta-source-compressed-inverse-determinant` statement `(8)` the general existence
theorem is not strictly needed.  Define: an entire `D` **is** the regularized determinant of `K` when
`D = fredholmDet K` on the disc `|z| ‖K‖_HS < 1`.  Uniqueness is the identity theorem, and existence
for the theta kernel is witnessed by `Xi_C(z)/Xi_C(0)` itself, which is entire and nonvanishing on
that disc (a zero of `Xi_C` forces `|1/z| <= ‖B‖_op <= ‖B‖_HS`).  So `(8)` reduces to the
**disc-local identity**

```text
fredholmDet (-B) z = Xi_C(z)/Xi_C(0)   for |z| ‖B‖_HS < 1,
```

which by `fredholmDet_weld` reduces further to the single trace formula

```text
Xi_C'(z)/Xi_C(z) = - resolventTrace (-B) z = sum over n >= 1 of (-1)^n z^n tr(B^(n+1)).
```

That trace formula is the remaining hard core, and it is independent of the general `det_2`
construction; the general construction is what the *multiplicity* clause needs.

## Log
- 2026-08-08 — created; the corpus `fredholmDet` classified as disc-local and nowhere zero, which
  rules out the route the three parent cards had recorded.  Their Lean-status sections corrected.
- 2026-08-08 — Route C fixed and its first three steps formalized: Schur triangulation, the finite
  regularized determinant with its order-two growth bound, and the Cauchy/Carleman coefficient
  layer.  Schur triangulation is absent from mathlib and is new corpus infrastructure.
