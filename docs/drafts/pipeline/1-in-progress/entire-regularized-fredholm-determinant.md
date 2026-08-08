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
formal/GaloisForLFunctions/HTGeometry/RegularizedDeterminantEntire.lean
formal/GaloisForLFunctions/HTGeometry/HilbertSchmidtContinuity.lean
formal/GaloisForLFunctions/HTGeometry/HilbertSchmidtTruncation.lean
formal/GaloisForLFunctions/HTGeometry/HilbertSchmidtBlockMatrix.lean
formal/GaloisForLFunctions/HTGeometry/FiniteDeterminantLogSeries.lean
formal/GaloisForLFunctions/HTGeometry/RegularizedDeterminantExists.lean
formal/GaloisForLFunctions/HTGeometry/RegularizedDeterminantLimit.lean
formal/GaloisForLFunctions/HTGeometry/FiniteDeterminantZeros.lean
formal/GaloisForLFunctions/HTGeometry/HurwitzZeroLimit.lean
formal/GaloisForLFunctions/HTGeometry/RegularizedDeterminantEigenvalues.lean
formal/GaloisForLFunctions/HTGeometry/HilbertSchmidtBlockEigenvector.lean
formal/GaloisForLFunctions/HTGeometry/CompactOperatorSpectrumLimit.lean
formal/GaloisForLFunctions/HTGeometry/RegularizedDeterminantEigenvalueLimit.lean
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
| 4 | the Hilbert--Schmidt kernels are a normed space | `isHS_add`, `isHS_sub`, `hsNorm_add_le`, `hsNorm_neg`, `hsNorm_sub_le` |
| 4 | composition is bilinear and submultiplicative | `hsComp_sub_left`, `hsComp_sub_right`, `hsNorm_hsComp_le` |
| 4 | the inner product is additive in each slot | `hsInner_sub_left`, `hsInner_sub_right` |
| 4 | **powers are Lipschitz on a norm ball** | `hsNorm_hsPow_sub_le` |
| 4 | **the power traces are Lipschitz on a norm ball** | `hsTrace_hsPow_sub_norm_le` |
| 4 | truncation to a finite block | `truncKernel`, `isHS_truncKernel`, `hsNorm_truncKernel_le`, `hsNormSq_split` |
| 4 | square blocks are cofinal among finite sets of pairs | `tendsto_finset_product_atTop` |
| 4 | **truncations converge in Hilbert--Schmidt norm** | `tendsto_hsNorm_sub_truncKernel` |
| 4 | **hence every power trace is the limit of the truncated traces** | `tendsto_hsTrace_hsPow_truncKernel` |
| 4 | a truncated kernel is the zero extension of a block matrix | `ofBlock`, `blockMatrix`, `truncKernel_eq_ofBlock` |
| 4 | the kernel algebra of blocks is the matrix algebra | `hsComp_ofBlock`, `hsPow_ofBlock` |
| 4 | **the kernel power traces of a truncation are the matrix power traces** | `hsTrace_hsPow_truncKernel` |
| 4 | the block energy is at most the kernel energy | `matHSNormSq_blockMatrix`, `matHSNormSq_blockMatrix_le` |
| 4 | `sum_k w^(k+2)/(k+2) = -log(1-w) - w` | `tsum_pow_div_add_two`, `exp_neg_tsum_pow_div_add_two` |
| 4 | each eigenvalue is bounded by the Hilbert--Schmidt norm | `norm_diag_le_of_schur` |
| 4 | **the determinant exponent of a finite matrix is its regularized determinant** | `exp_neg_traceSeries_eq_finiteDet2_neg` |
| 4 | reindexing the determinant, energy and trace | `finiteDet2_submatrix`, `matHSNormSq_submatrix`, `trace_submatrix_equiv`, `trace_pow_submatrix` |
| 4 | **the corpus determinant of a truncation is the finite one** | `fredholmDet_truncKernel_eq` |
| 5 | the geometric bound on the exponent | `norm_fredholmExp_le` |
| 5 | **the exponent is Lipschitz in the Hilbert--Schmidt norm** (`k+2` cancels `1/(k+2)`) | `norm_fredholmExp_sub_le` |
| 5 | hence the determinants converge uniformly on a closed disc | `norm_fredholmDet_sub_le` |
| 5 | Cauchy's estimate on a disc, not only for entire functions | `norm_taylorCoeff_le'`, `diffContOnCl_of_differentiableOn_ball` |
| 5 | the canonical radius and the limit coefficients | `detRadius`, `detCoeff`, `detCoeff_truncKernel`, `norm_detCoeff_truncKernel_le`, `tendsto_detCoeff_truncKernel`, `norm_detCoeff_le` |
| 5 | **the entire regularized determinant, as a named function** | `entireDet2`, `differentiable_entireDet2`, `isRegularizedDet_entireDet2` |
| 5 | **every Hilbert--Schmidt kernel has an entire regularized determinant** | `exists_isRegularizedDet` |
| 5 | **it is the pointwise limit of the finite block determinants** | `tendsto_finiteDet2_entireDet2` |
| 6 | the zeros of a finite determinant are the reciprocal eigenvalues | `finiteDet2_eq_zero_iff_det`, `finiteDet2_eq_zero_iff_exists_eigenvector` |
| 6 | **the order of vanishing of a finite determinant is the eigenvalue multiplicity** | `finiteDet2_factor` |
| 6 | **the block determinants converge uniformly on every closed disc** | `norm_detCoeff_mul_pow_le`, `norm_detCoeff_truncKernel_mul_pow_le`, `tendsto_tsum_norm_detCoeff_sub`, `tendstoUniformlyOn_finiteDet2_entireDet2` |
| 6 | the boundary minimum of a nonvanishing function on a circle | `exists_pos_le_norm_on_sphere` |
| 6 | **Hurwitz's theorem, the zero-persistence half** | `eventually_exists_zero_of_tendstoUniformlyOn` |
| 6 | **a zero of the entire determinant is a limit of reciprocal block eigenvalues** | `eventually_exists_blockEigenvalue_near` |
| 7 | a block eigenvector, extended by zero, is an `l^2` eigenvector of the truncation | `liftBlock`, `liftBlockLp`, `liftBlockLp_ne_zero`, `toOperator_truncKernel_liftBlockLp` |
| 7 | the represented operators converge in **operator** norm | `toOperator_sub`, `norm_toOperator_sub_le`, `tendsto_norm_toOperator_truncKernel_sub` |
| 7 | cluster points survive an asymptotically vanishing perturbation | `mapClusterPt_of_tendsto_dist_zero` |
| 7 | **a limit of eigenvalues of nearby operators is an eigenvalue of the compact limit** | `exists_eigenvector_of_tendsto_of_isCompactOperator` |
| 8 | the block spectrum as a closed set, and its eigenvector characterisation | `blockSpectrum`, `isClosed_blockSpectrum`, `mem_blockSpectrum_iff` |
| 8 | the zeros of the entire determinant are isolated (its value at the origin is `1`) | `eventually_entireDet2_ne_zero`, `exists_radius_isolating` |
| 8 | the distance from `1/z_0` to the block spectrum tends to zero | `tendsto_infDist_blockSpectrum`, `eventually_blockSpectrum_nonempty` |
| 8 | **a zero of the entire determinant is a reciprocal eigenvalue of the kernel operator** | `exists_eigenvector_of_entireDet2_eq_zero` |
| — | the definition and uniqueness of the entire determinant | `IsRegularizedDet`, `.unique`, `.eq_one_at_zero`, `isRegularizedDet_of_logDeriv_eq` |

## Gates
- [x] 0 -> 1  the obstruction is identified exactly and the corpus object is classified
- [x] Schur triangulation in Lean
- [x] finite `det_2` and its order-two growth bound in Lean
- [x] Cauchy/Carleman coefficient bound, and entirety of such a series, in Lean
- [x] truncation of a Hilbert--Schmidt kernel: `‖K_s‖_HS <= ‖K‖_HS` and `tr(K_s^m) -> tr(K^m)`
- [x] the definition and uniqueness of the entire `det_2`, and the criterion that recognises it
- [x] the matrix/kernel bridge: `finiteDet2` of the block matrix is `fredholmDet` of the truncated
      kernel on the disc
- [x] entire `det_2` **exists** for every Hilbert--Schmidt kernel (`exists_isRegularizedDet`)
- [x] the *finite* case of both zero statements (`finiteDet2_eq_zero_iff_exists_eigenvector`,
      `finiteDet2_factor`), and the limit that must carry them (`tendsto_finiteDet2_entireDet2`)
- [x] uniform convergence on every closed disc (`tendstoUniformlyOn_finiteDet2_entireDet2`)
- [x] **Hurwitz's theorem**, built here because mathlib lacks it
      (`eventually_exists_zero_of_tendstoUniformlyOn`), and its first consequence:
      a zero of `entireDet2 K` is a limit of reciprocal eigenvalues of the finite blocks
      (`eventually_exists_blockEigenvalue_near`)
- [x] the two halves of that passage: the `l^2` lift of a block eigenvector
      (`toOperator_truncKernel_liftBlockLp`), the operator-norm convergence
      (`tendsto_norm_toOperator_truncKernel_sub`), and the spectral limit theorem
      (`exists_eigenvector_of_tendsto_of_isCompactOperator`), all absent from mathlib
- [x] **`det_2(1 - zK) = 0` implies `1/z` is an eigenvalue of `K`**
      (`exists_eigenvector_of_entireDet2_eq_zero`).  No diagonal argument was needed: taking, for
      each block, the point of its spectrum **nearest** to `1/z_0` gives the single convergent
      family directly, because the block spectrum is closed and `ℂ` is proper
- [ ] the converse: an eigenvalue of `K` is a zero of `det_2`
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
- 2026-08-08 — step 4 formalized on the kernel side: the Hilbert--Schmidt power traces are Lipschitz
  on a norm ball (`hsTrace_hsPow_sub_norm_le`, from the telescoping identity
  `A^{m+1} - B^{m+1} = A(A^m - B^m) + (A-B)B^m` and Cauchy--Schwarz), and finite-block truncations
  converge to the kernel in Hilbert--Schmidt norm, so `tr(K_s^m) -> tr(K^m)`.  Also added the
  definition, uniqueness and recognition criterion of the entire determinant
  (`IsRegularizedDet`).  What is left of step 4 is purely the bookkeeping bridge between the
  block matrix and the truncated kernel.
- 2026-08-08 — the bridge is closed: `hsTrace_hsPow_truncKernel` identifies the kernel power traces
  of a truncation with the matrix power traces of its block, and `fredholmDet_truncKernel_eq`
  identifies the corpus determinant of a truncation with `finiteDet2` of the block, on the disc.
  The link is the scalar identity `sum_{k>=2} w^k/k = -log(1-w) - w` applied to each Schur
  eigenvalue.  Only the limit assembly is left.
- 2026-08-08 — **the entire regularized determinant now exists in Lean**, unconditionally, for every
  Hilbert--Schmidt kernel over any index type with decidable equality: `exists_isRegularizedDet`.
  Together with `IsRegularizedDet.unique` the phrase "the regularized determinant of `K`" is a
  well-posed Lean object.  The three remaining gates are about its *zeros*.
- 2026-08-08 — the determinant is now a **named** function `entireDet2 K` with its construction
  exposed (`detRadius`, `detCoeff`, and the convergence and bound lemmas), and it is the pointwise
  limit of the finite block determinants (`tendsto_finiteDet2_entireDet2`).  The finite-dimensional
  zero theory is complete: `finiteDet2_eq_zero_iff_exists_eigenvector` and the explicit
  factorization `finiteDet2_factor` giving the order of vanishing as the number of Schur diagonal
  entries equal to `-1/z_0`.  Carrying these to the limit needs Hurwitz's theorem, which mathlib
  does not have.
- 2026-08-08 — **Hurwitz built** (`HurwitzZeroLimit.lean`), from the maximum modulus principle
  applied to `1/f_n`: no argument principle and no Rouche needed.  The convergence
  `tendsto_finiteDet2_entireDet2` was upgraded to **uniform on every closed disc**, and the two
  combine into `eventually_exists_blockEigenvalue_near`: a zero of `entireDet2 K` is a limit of
  reciprocal eigenvalues of the finite blocks.  The remaining step to the operator statement is
  upper semicontinuity of the spectrum under norm convergence of compact operators.
- 2026-08-08 — that semicontinuity is now built:
  `exists_eigenvector_of_tendsto_of_isCompactOperator`.  If `‖S_a - T‖ -> 0` with `T` compact,
  `S_a v_a = lam_a v_a` with `‖v_a‖ = 1`, and `lam_a -> l != 0`, then `l` is an eigenvalue of `T`.
  The proof uses `IsCompact.exists_mapClusterPt` plus the finer filter `p ⊓ comap u (nhds w)`,
  whose non-triviality is `Filter.push_pull` + `Filter.map_neBot_iff`.  Together with the `l^2`
  lift of block eigenvectors, only the diagonal assembly is left.
- 2026-08-08 — assembled: **`exists_eigenvector_of_entireDet2_eq_zero`**.  A zero `z_0 != 0` of the
  entire regularized determinant of a Hilbert--Schmidt kernel is a reciprocal eigenvalue of the
  kernel operator on `l^2`.  The diagonal argument turned out to be unnecessary: the *nearest point
  of the block spectrum* to `1/z_0` is a single convergent family, since the block spectrum is
  closed (zero set of the characteristic polynomial) and `ℂ` is proper.
