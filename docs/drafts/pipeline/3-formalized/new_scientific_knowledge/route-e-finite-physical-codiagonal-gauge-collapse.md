# Route E finite physical codiagonal and Fisher gauge collapse

- **ID:** `ROUTE-E-FINITE-PHYSICAL-CODIAGONAL-GAUGE-COLLAPSE-001`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / SHARPENED ONE-CORNER LAW / EXACT PHYSICAL ANOVA
- **Scientific status:** `[LEAN-PROVED] [BRIDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `../../2-fully-proven/new_scientific_knowledge/route-e-critical-antiscale-diffuse-codiagonal-transfer-law.md`
- **Route:** E
- **RH used:** no
- **Computation used:** no
- **Literature used:** no; internal-corpus theorem synthesis under current directive

## Result

This module closes finite complex codiagonal transfer, finite Fisher gauge collapse, and finite
physical column ANOVA, and strengthens the paper constant by one factor of `sqrt 2`.

### A. One oriented pointed-Fisher corner costs half

For a unit vector `psi`, arbitrary tangent `chi`, orthogonal cutoff `e`, and pointed connection

\[
 F(\psi,\chi)=2^{-1/2}
 (|\chi\rangle\langle\psi|+|\psi\rangle\langle\chi|),
 \qquad B=(1-e)F(\psi,\chi)e,
\]

Lean proves, without assuming `psi` and `chi` orthogonal,

\[
 \boxed{\|B\|_{HS}^{2}\le \frac12\|\chi\|^2.}
\]

If `D` is any contraction and `Reporter_D` is its joined one-corner reporter, the existing
half-unit reporter law combines with this bound to give

\[
 \boxed{|\langle B,\operatorname{Reporter}_D\rangle_{HS}|^2
 \le\frac14\|\chi\|^2.}
\]

The previous paper argument used only monotonicity under compression and obtained `1/2` instead
of `1/4` on the right. This is a genuine geometric strengthening.

### B. All-order finite squarefree Gibbs histories

For every finite prime palette `S`, all occupied-subset histories form
`SquarefreeBitConfig S`. Existing source and curvature infrastructure gives signed unit source
`psi_(S,sigma)`, centered tangent `h_(S,sigma)`, and variance `V_(S,sigma)`. The new module proves

\[
 \langle\psi,h\rangle=0,
 \qquad
 \|F_{S,\sigma}\|_{HS}^{2}
 =4(\sigma-1)^2V_{S,\sigma},
\]

and the strengthened finite gauge-collapse law

\[
 \boxed{
 |\langle(1-e)F_{S,\sigma}e,\operatorname{Reporter}_D\rangle_{HS}|
 \le |\sigma-1|\sqrt{V_{S,\sigma}}.}
\]

Thus shrinking Euler coordinate still cannot create physical cancellation, but exact loss is
smaller than previously known.

### C. Division-free gauge neutralization

Rather than divide by `sigma-1`, Lean constructs centered logarithmic tangent directly before
gauge multiplication. This definition is valid even at `sigma=1`. It proves

\[
 h_{S,\sigma}=(\sigma-1)\widehat h_{S,\sigma},
 \qquad
 \|\widehat h_{S,\sigma}\|^2=4V_{S,\sigma},
 \qquad
 \langle\psi,\widehat h\rangle=0,
\]

so neutral connection satisfies

\[
 \|\widehat F_{S,\sigma}\|_{HS}^2=4V_{S,\sigma},
 \qquad
 \boxed{
 |\langle(1-e)\widehat F_{S,\sigma}e,
   \operatorname{Reporter}_D\rangle_{HS}|
 \le\sqrt{V_{S,\sigma}}.}
\]

This replaces paper's coarse `sqrt (2 V)` while preserving its obstruction: at source-faithful
tilt, `sqrt V` still grows on physical scale.

### D. Unequal-mass physical column ANOVA

For arbitrary finite nonnegative pushed masses `rho_i` and positive target masses `nu_i`, let

\[
 P=\sum_i\rho_i,
 \quad N=\sum_i\nu_i,
 \quad A_i={\rho_i\over\nu_i}-{P\over N},
 \quad E_{\rm cent}=\sum_i\nu_iA_i^2.
\]

Lean proves the weighted centering identity and exact orthogonal decomposition

\[
 \sum_i\nu_iA_i=0,
 \qquad
 \boxed{
 \sum_i{(\rho_i-\nu_i)^2\over\nu_i}
 =E_{\rm cent}+{(P-N)^2\over N}.}
\]

The theorem is unconditional over every finite type. Empty index type is handled internally, so
no nonemptiness or nonzero-total premise appears. This is paper Theorem H exactly. It isolates
non-scalar centered producer energy from scalar signed mass discrepancy without assuming mass
conservation.

### E. Literal finite complex mean/codiagonal/collision trichotomy

For normalized nonnegative real weights `w_s`, arbitrary complex cofactors `G_s`, complex
reporters `d_s`, and centered blocks `A_s=G_s-sum_q w_q G_q`, Lean proves literal ordered-pair
identity

\[
 \sum_{s\ne q}w_sw_q(A_s+A_q)d_s
 =\sum_sw_sA_sd_s-2\sum_sw_s^2A_sd_s.
\]

Consequently

\[
 \sum_sw_sd_sG_s
 =\bar G\sum_sw_sd_s+O_w(A,d)+2R_w(A,d).
\]

If `0<=w_s<=wMax` and `|d_s|<=1`, weighted Cauchy--Schwarz gives exact paper collision bound

\[
 \left|2R_w(A,d)\right|
 \le 2w_{\max}\left(\sum_sw_s|A_s|^2\right)^{1/2}.
\]

This closes Theorems C--D in their stated complex finite-state form. Existing countable real
codiagonal theorem remains a compatible infinite specialization, not a substitute for this claim.

## Lean certificate

Module:

```text
GaloisForLFunctions.RHTower.RouteEFinitePhysicalCodiagonalGaugeCollapse
```

Principal declarations:

```text
hsNormSq_cutoffLowerBoundary_pointedFisherConnection_le_half
norm_sq_hsInner_cutoffLowerBoundary_joinedReporter_le_quarter

routeEFiniteOffDiagonalCodiagonal_eq_score_sub_collision
norm_routeEFiniteCodiagonalScore_sub_offDiagonal_le
routeEFiniteCenteredCofactor_mean_zero
routeEFinite_mean_offDiagonal_collision_decomposition
norm_two_mul_routeEFiniteCenteredCofactor_collision_le

routeEFiniteSquarefreeFisherConnection_energy
finiteSquarefreeCurvature_nonneg
norm_sq_hsInner_routeEFiniteSquarefreeFisherLowerBoundary_joinedReporter_le
norm_hsInner_routeEFiniteSquarefreeFisherLowerBoundary_joinedReporter_le

routeEFiniteSquarefreeGaugeNeutralTangent
finiteSquarefreeTangent_eq_gauge_smul_neutral
norm_routeEFiniteSquarefreeGaugeNeutralTangent_sq
inner_source_routeEFiniteSquarefreeGaugeNeutralTangent_eq_zero
routeEFiniteSquarefreeGaugeNeutralConnection_energy
norm_hsInner_routeEFiniteSquarefreeGaugeNeutralLowerBoundary_joinedReporter_le

RouteEFiniteColumnData.likelihoodRatio
RouteEFiniteColumnData.centeredLikelihoodRatio
RouteEFiniteColumnData.centeredEnergy
RouteEFiniteColumnData.centeredLikelihoodRatio_mean_zero
RouteEFiniteColumnData.chiSquare_eq_centeredEnergy_add_massDefect
```

Module is imported by `GaloisForLFunctions.RHTower`. No `sorry`, `admit`, new `axiom`, `opaque`,
`unsafe`, numerical computation, or Route E producer premise occurs.

## Frontier consequence

Finite Fisher gauge collapse, division-free neutralization, and exact physical ANOVA identity are
no longer open. They do not prove Route E's arithmetic producer estimate

\[
 E_{\rm cent}\le X^{o(1)},
\]

nor transport same centered reporter through moving zero/one-large-prime seam and signed
recurrence. Those remain exact open core. Improved constant changes geometry, not missing power.

## Novelty status

No external priority claim is made. Relative to internal corpus, new content is quarter-energy
composition of two one-corner laws, its exact all-order squarefree Euler instantiation,
division-free gauge neutralization valid at singular gauge, and unequal-total physical ANOVA
formalization.

## Log

- 2026-08-12 — Literal complex Theorems C--D, strengthened one-corner constant, and Theorems E, F,
  and H formalized; umbrella import added; claim-complete child promoted to Stage 3.
