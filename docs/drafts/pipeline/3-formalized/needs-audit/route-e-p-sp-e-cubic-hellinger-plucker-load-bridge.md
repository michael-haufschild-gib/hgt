# Route E/P/SP-E cubic Hellinger--Pluecker load bridge

- **ID:** `route-e-p-sp-e-cubic-hellinger-plucker-load-bridge`
- **Stage:** 3-formalized / needs audit
- **Type:** `[THEOREM] [CROSS-ROUTE BRIDGE] [POSITIVE PRODUCER]`
- **Parents:**
  - `../../1-in-progress/rh-current-frontier-map.md` (Routes E, P, SP-E);
  - `../../1-in-progress/prime-gamma-signed-permutation-eulerian-rh.md`;
  - `../new_scientific_knowledge/route-e-weighted-hall-anova-projection-duality-law.md`.
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/RouteEPCubicHellingerPluckerLoadBridge.lean`

## Result

Three previously separate finite defects are one exact information coordinate.

For positive rates (a,b), let

\[
  \chi(a,b)=\left(\frac{a-b}{a+b}\right)^2.
\]

This is exactly Route E's target-weighted physical chi-square for one unit source transported to
two columns in proportions (a:b), against the balanced target ((1/2,1/2)).

Route P's equal-ordinate cubic Cauchy columns have squared normalized coherence

\[
  C_3(a,b)^2=\frac{64a^3b^3}{(a+b)^6}=(1-\chi(a,b))^3.
\]

Therefore their normalized Pluecker defect satisfies the exact law

\[
  \Delta_3(a,b)
   =1-C_3(a,b)^2
   =\chi(a,b)\bigl(3-3\chi(a,b)+\chi(a,b)^2\bigr).
  \tag{1}
\]

Since (0\le\chi<1),

\[
  \chi(a,b)\le\Delta_3(a,b)\le3\chi(a,b).
  \tag{2}
\]

Thus Route E physical load dispersion and Route P/SP-E cubic Gram area are quantitatively
equivalent, not merely zero on the same diagonal. The unnormalized Route-P two-node Gram
determinant is

\[
  \det G_{a,b}
   =\frac{\Delta_3(a,b)}{16a^3b^3}
   =\frac{\chi(a,b)(3-3\chi(a,b)+\chi(a,b)^2)}{16a^3b^3}.
  \tag{3}
\]

## Canonical source witness

Let (D) be Route P's primitive depth-square map. Corpus already proves

\[
  \lambda(D(pe))=2\lambda(pe).
\]

For (D^2(pe)), every primitive cell therefore has a canonical source partner of frequency
(4\lambda(pe)). No Xi zero, Xi Taylor coefficient, fitted activity, or numerical approximation
enters this pair. Equations (1)--(2) give

\[
  \chi(\lambda,4\lambda)=\frac9{25},
  \qquad
  \Delta_3(\lambda,4\lambda)=\frac{11529}{15625}.
\]

After normalizing the two cubic columns to unit diagonal, the determinant polynomial
(det(I+uG)) has linear coefficient (2) and quadratic coefficient (Delta_3). Its scale-free
quadratic ratio is therefore

\[
  \frac{[u^2]}{[u]^2}
   =\frac{\Delta_3}{4}
   =\frac{11529}{62500}
   >\frac16
   >\frac{13}{98}.
  \tag{4}
\]

Equation (4) is first source-derived **unit-diagonal** SP-E metric block that clears theta moment
log-convexity floor (1/6), and it strictly exceeds exact ceiling of uniform Boolean metric. Unit
diagonal is not source-faithful: the follow-up normalization-debt audit proves transported
fourth-depth diagonal is smaller by (1/64), dropping actual ratio below both thresholds. See
`route-e-p-sp-e-cubic-source-normalization-debt.md`.

## Higher principle

Failures of three routes are shadows of one quotient error:

- Route E coalesces labelled histories into physical columns and loses load information;
- Route P compresses cubic source columns and measures surviving Schur area;
- SP-E scalarizes signed-word curvature and loses two-minors.

Before scalarization, same projective rate gap is seen as chi-square in transport coordinates and
as Pluecker/Hellinger area in Gram coordinates. Cubic Gamma geometry applies the polynomial
(chi\mapsto1-(1-\chi)^3). Hence entropy or orbit cardinality alone cannot be producer. Required
quantity is weighted pairwise projective dispersion. Conversely, a Route-E estimate on aggregate
two-column chi-square transfers to SP-E cubic minor mass with only universal factor three.

This also explains coalescence obstruction: (Delta_3) is quadratic in relative rate gap near
(a=b). Local pair-switch abundance without projective rate spread can still carry negligible
capacity.

## Conjecture loop audit

1. **Conjecture:** labelled-to-physical quotient formalism was missing.
   **Failed:** corpus already has exact physical coarea, idempotent fibre shuffle, stationary
   kernels, and product-history dissipation.
2. **Conjecture:** Route-P cubic Cauchy Gram might provide missing SP-E metric.
   **Survived after strengthening:** its coherence defect is exactly cubic transform (1) of
   Route-E load chi-square.
3. **Attack:** qualitative positivity may be too weak and canonical source rates may be too close.
   **Survived:** fourth-depth partner gives universal exact ratio (4), clearing first SP-E
   quadratic floor.
4. **Attack:** a single two-column block might be mistaken for theta coefficient equality.
   **Fails as completion:** every two-column normalized Gram ratio is at most (1/4), while exact
   theta ratio is larger. Positive survivor is local metric producer and pairwise dispersion law;
   cofinal many-column assembly remains necessary.
5. **Attack:** unit-diagonal block might remain valid under coefficient-faithful depth transport.
   **Fails:** two depth-square steps contract cubic diagonal by exactly (1/64), giving actual ratio
   (737856/66015625<13/98<1/6). Positive survivor is unique amplitude-eight correction and exact
   trace debt (63w/64), formalized in the normalization-debt child card.

## Open core exposed

1. Build cofinal primitive-depth pairing/mixture whose diagonal normalization is source-faithful.
2. Prove weighted aggregate of (Delta_3) has exact theta degree-two ratio, not only floor (4).
3. For Route E, prove grade-recurrent cube has enough projective rate dispersion in every interval,
   alongside unit row/column capacity.
4. For Route P, show completed four-leg/Stokes correction preserves this cubic information area
   while remaining inside primitive trace budget.
5. Extend pairwise law to all principal minors and identify cofinal determinant with square-coordinate
   Xi function.

## Novelty audit

Internal research search found Route-P normalized Cauchy coherence and strict two-node Schur gap,
Route-E chi-square/ANOVA, and SP-E Pluecker lift separately. It found no exact identity (1),
factor-three comparison (2), or canonical fourth-depth gate (4).

External ingredients are classical: Hellinger affinity matrices and chi-square information
matrices are studied by Derumigny--Schmidt-Hieber,
[`Codivergences and information matrices`](https://doi.org/10.1007/s41884-024-00135-2), and
Cauchy-kernel total positivity by Simon,
[`Total positivity of a Cauchy kernel`](https://arxiv.org/abs/1305.1173). Neither source states
the arithmetic depth-square identity, Route-E load/Route-P cubic transform, or SP-E gate (4).
No external priority claim is made.

## Formal status

Lean proves, unconditionally and without added axioms:

- `routeETwoColumnBalanced_chiSquare_eq`;
- `routePBaseCauchyCubic_coherence_defect_eq_loadChiSquare`;
- `routeETwoColumnLoadChiSquare_le_coherence_defect`;
- `routePBaseCauchyCubic_coherence_defect_le_three_loadChiSquare`;
- `routePBaseCauchyCubicTwoNodeGramDet_eq_loadChiSquare`;
- `routePPrimitivePair_cubicPluckerDefect_pos`;
- `xiGammaEulerPrimitiveLogFrequency_routePPrimitiveFourthDepth`;
- `routeETwoColumnLoadChiSquare_primitiveFourthDepth`;
- `routeEPCubicNormalizedPairGramRatio_primitiveFourthDepth`;
- `one_div_six_lt_routeEPCubicNormalizedPairGramRatio_primitiveFourthDepth`;
- `thirteen_div_ninetyEight_lt_routeEPCubicNormalizedPairGramRatio_primitiveFourthDepth`.
