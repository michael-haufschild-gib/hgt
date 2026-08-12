# Route E critical antiscale dissipation saturation

- **ID:** `ROUTE-E-CRITICAL-ANTISCALE-DISSIPATION-SATURATION-001`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / EXACT ESCAPE CLASSIFICATION / FINITE-HEIGHT TRANSFER
- **Scientific status:** `[LEAN-PROVED] [BRIDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `../../2-fully-proven/new_scientific_knowledge/route-e-critical-antiscale-diffuse-codiagonal-transfer-law.md`
- **Route:** E
- **RH used:** no
- **Computation used:** no
- **Literature used:** no; internal-corpus theorem synthesis under current directive

## Result

For a finite prime aperture `Q`, real exponent `r`, and height `t`, define

\[
 \Psi_{Q,r}(t)=\prod_{p\in Q}
 {1-p^{-r}p^{-it}\over 1+p^{-r}},
 \qquad
 V_{Q,r}=\prod_{p\in Q}{1+p^{-2r}\over(1+p^{-r})^2},
 \qquad
 R_Q=\prod_{p\in Q}p.
\]

The following claims are closed unconditionally in Lean.

### A. Exact local deficit and escape locus

Put

\[
 d_{p,r}(t)=
 {p^{-r}|1+e^{it\log p}|^2\over(1+p^{-r})^2}.
\]

For every real `r`, not merely `r>0`,

\[
 \left|{1-p^{-r-it}\over1+p^{-r}}\right|^2=1-d_{p,r}(t),
 \qquad 0\le d_{p,r}(t)\le1,
\]

and

\[
 d_{p,r}(t)=0\iff e^{it\log p}=-1.
\]

Consequently `|Psi|<=1`, with equality exactly when every prime phase is antiscale. Prime-log
Kronecker recurrence then proves the cofinal sharpness statement

\[
 \forall T\in\mathbb R\ \forall\varepsilon>0\ \exists t>T,
 \qquad 1-\varepsilon<|\Psi_{Q,r}(t)|.
\]

Thus antiscale coherence is the exact escape mode. It is not a quadratic-approximation artifact.

### B. Exact all-order squarefree history expansion

Index histories by all subsets `S subset Q`. Their frequencies and coefficients are

\[
 \lambda_S=-\log\prod_{p\in S}p,
\]

\[
 c_S=\prod_{p\in S}{-p^{-r}\over1+p^{-r}}
       \prod_{p\in Q\setminus S}{1\over1+p^{-r}}.
\]

Lean proves the exact identity

\[
 \Psi_{Q,r}(t)=\sum_{S\subseteq Q}c_Se^{it\lambda_S}
\]

and the exact coefficient-energy law

\[
 \sum_{S\subseteq Q}|c_S|^2=V_{Q,r}.
\]

Unique factorization proves frequency injectivity. Since distinct subset products are positive
integers at most `R_Q`, the elementary logarithmic gap is formalized with the sharp packet scale

\[
 S\ne T\Longrightarrow {1\over R_Q}\le|\lambda_S-\lambda_T|.
\]

### C. Exact finite-height dissipation

The module proves a reusable theorem for any finite separated real-frequency polynomial. Ordering
the frequency set, extending the finite ordered sequence arithmetically, and bounding every
reciprocal-gap Gram row by its exact harmonic sum gives

\[
 \int_{-W}^{W}\left|\sum_jc_je^{it\lambda_j}\right|^2dt
 \le
 \left(2W+{4\over\delta}(1+\log N)\right)\sum_j|c_j|^2.
\]

Instantiating `N=2^{|Q|}` and `delta=R_Q^{-1}` yields the paper theorem with no constant loss:

\[
 \boxed{
 \int_{-W}^{W}|\Psi_{Q,r}(t)|^2dt
 \le
 \left(2W+4R_Q(1+|Q|\log2)\right)V_{Q,r}.}
\]

The Lean statement is valid for every real `W`; the intended finite-height form takes `W>0`.

### D. Critical accumulated mass

For `r>0`,

\[
 \boxed{V_{Q,r}\le
 \exp\!\left(-{1\over2}\sum_{p\in Q}p^{-r}\right).}
\]

More generally, for every sequence of finite prime packets `Q_N`,

\[
 \sum_{p\in Q_N}p^{-r}\longrightarrow+\infty
 \quad\Longrightarrow\quad
 V_{Q_N,r}\longrightarrow0.
\]

For canonical prime apertures and `0<r<=1`, comparison with the divergent reciprocal-prime sum
discharges the premise. This separates two logically distinct regimes exactly:

- local escape geometry is valid for every real `r`;
- accumulated critical dissipation uses `0<r<=1`.

## Lean certificate

Module:

```text
GaloisForLFunctions.RHTower.RouteECriticalAntiscaleDissipationSaturation
```

Principal declarations:

```text
routeECriticalEulerLocalDeficit_identity
routeECriticalEulerLocalDeficit_nonneg
routeECriticalEulerLocalDeficit_le_one
routeECriticalEulerLocalDeficit_eq_zero_iff
routeECriticalEulerReporter_normSq_eq_prod_deficit
routeECriticalEulerReporter_norm_eq_one_iff_all_antiscale
routeECriticalEulerReporter_norm_le_one
exists_gt_phaseCovec_near_antiscale
exists_gt_routeECriticalEulerReporter_norm_gt_one_sub

routeEFiniteFrequency_meanValue_error_le
routeEFiniteFrequency_meanValue_le
routeEFinsetFrequency_meanValue_le
routeEFintypeFrequency_meanValue_le

routeECriticalEulerSubsetFrequency_injective
routeECriticalEulerSubsetFrequency_separated
routeECriticalEulerReporter_eq_frequencyPolynomial
routeECriticalEulerSubsetCoefficient_energy_eq_mass
routeECriticalEulerReporter_meanValue_le

routeECriticalEulerMeanSquareMass_le_exp_neg_half_sum
tendsto_routeECriticalEulerMeanSquareMass_zero_of_radiusMass
tendsto_routeECriticalPrimeRadiusMass_atTop
tendsto_routeECriticalEulerApertureMeanSquareMass_zero
```

Module is imported by `GaloisForLFunctions.RHTower`. No `sorry`, `admit`, new `axiom`, `opaque`,
`unsafe`, numerical computation, or route hypothesis occurs.

## Frontier consequence

Critical dissipation saturation is no longer open. Cofinal recurrence and finite-height decay are
compatible because recurrence occupies a diffuse height set; pointwise coercivity was wrong target.
Route E's open core remains downstream: finite physical column-ANOVA strict-half production and
transport of same signed reporter through moving prime seam and exact recurrence. This theorem is
receiver plus exact escape classification; it does not manufacture missing physical ANOVA bound.

Parent card remains Stage 2 because its centered codiagonal, physical column-ANOVA, seam transport,
and endpoint claims are broader than Theorems A--B formalized here.

## Novelty status

No external priority claim is made. Relative to internal corpus, new content is exact assembly of
prime recurrence, all-order squarefree histories, harmonic finite-height transfer, and critical
prime-mass divergence into one unconditional theorem, plus stronger separation of all-real local
geometry from critical-only accumulated decay.

## Log

- 2026-08-12 — Theorems A--B and reusable finite separated-frequency mean-value infrastructure
  proved in Lean; umbrella import added; claim-complete child promoted to Stage 3.
