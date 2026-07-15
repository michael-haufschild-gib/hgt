# Prime--archimedean scaled Hausdorff divisor value law

- **ID:** `prime-arch-scaled-hausdorff-divisor-value-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** normalized prime--Gamma moment germ, reciprocal-square Xi divisor, endpoint-calibrated Hausdorff criterion
- **Statement:** Every endpoint-calibrated source difference is the real part of an explicit reciprocal-square Xi polynomial sum; the full 616-condition rectangle `k <= 13`, `r <= 43` is nonnegative unconditionally.
- **Novelty status:** not asserted; retained for direct RH proof leverage.

## Main value law

For
```text
lambda_q = (i(rho_q-1/2))^(-2)
R        = C/(1-C)
C        = xiEndpointCompletedCurvature,
```
the normalized prime--Gamma source functional satisfies, for every real polynomial `p`,
```text
L_source(p) = Re sum_q lambda_q p(lambda_q).
```
Consequently every endpoint-calibrated Hausdorff difference has the exact expression
```text
D_R(k,r)
  = Re sum_q lambda_q^(k+1) (R-lambda_q)^r.
```
The sum is absolutely convergent for every `k,r`.

## Unconditional finite rectangle

The completed endpoint and reflection estimates give
```text
0 < Re(lambda_q) <= R,
Im(lambda_q)^2 <= Re(lambda_q)^2/84.
```
For an off-critical copy, the four-copy endpoint charge sharpens the radial estimate to
```text
|lambda_q| <= C/(4-C),
Re(lambda_q) < R/4.
```
For every off-critical copy they imply
```text
(913/100) |Im(lambda_q)| <= Re(lambda_q),
(2739/100) |Im(R-lambda_q)| <= Re(R-lambda_q).
```
Thus `lambda_q` lies in an angle sector of half-width at most `100/913`, while its endpoint
complement lies in the three-times-narrower sector of half-width at most `100/2739`. Their
imaginary parts have opposite signs. The powered arguments therefore partially cancel, and the
absolute argument of their product is bounded by the larger, rather than the sum, of
```text
(k+1) * 100/913,
r * 100/2739.
```
Both are below `pi/2` whenever `k <= 13` and `r <= 43`. Lean proves unconditionally
```text
0 <= D_R(k,r)  whenever k <= 13 and r <= 43.
```
This is a rectangle of `14 * 44 = 616` indexed conditions. It strictly contains the earlier
301-condition wedge `3*k+r <= 40` and the complete total-degree triangle `k+r <= 13`.

## RH proof impact

The existing endpoint-calibrated theorem proves
```text
(for all k r, 0 <= D_R(k,r))
  iff RH
  iff sigma_abs(sum_n S^-_{L,N}(n) n^(-s)) <= 1.
```
The present result discharges the entire 616-condition rectangle of that exact criterion and exposes every remaining inequality as an explicit summand-level value relation. The two separate rational-angle budgets are `1400/913 < pi/2` and `4300/2739 < pi/2`. Lean also proves the reduced capstone
```text
sigma_abs(sum_n S^-_{L,N}(n) n^(-s)) <= 1
  iff
forall k r, (13 < k or 43 < r) -> 0 <= D_R(k,r).
```
Thus none of these 616 low-index inequalities remains as a premise of the prime--polar endpoint theorem. The unresolved obligation is a global positivity argument on the complement of the rectangle; the abscissa bound itself is not yet proved.

## Lean certificate

Formalization:
`formal/GaloisForLFunctions/RHTower/PrimeArchScaledHausdorffDivisorValueRelation.lean`.

Principal declarations:

- `xiCentralPolynomialMomentTerm`
- `xiCentralPolynomialMoment`
- `summable_xiCentralPolynomialMomentTerm`
- `xiCentralPolynomialMoment_eq_moment_sum`
- `normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment`
- `xiCentralPolynomialMoment_eq_sourceMomentFunctional`
- `scaledHausdorffMomentDifference_eq_momentFunctional`
- `xiCentralPolynomialMoment_scaledBasis`
- `summable_xiCentralScaledHausdorffTerm`
- `scaledHausdorffMomentDifference_eq_re_xiCentralSum`
- `xiZeroCopyReciprocalSquare_norm_le_offLineEndpointRadius`
- `xiThermalNode_le_one_third_endpointRadius_of_offLine`
- `xiThermalNode_lt_one_fourth_endpointRadius_of_offLine`
- `scaledPrimeArchEndpointHausdorffDifference_totalDegree_le_three_nonnegative`
- `re_xiCentral_scaledBasis_rectangle_nonneg`
- `scaledPrimeArchEndpointHausdorffDifference_rectangle_nonnegative`
- `scaledPrimeArchHausdorffMomentDifferencesNonnegative_iff_rectangleTailNonnegative`
- `rectangularPrimePolarSource_negativeAbscissa_le_one_iff_rectangleHausdorffTailNonnegative`
- `re_xiCentral_scaledBasis_weightedDegree_le_forty_nonneg`
- `scaledPrimeArchEndpointHausdorffDifference_weightedDegree_le_forty_nonnegative`
- `scaledPrimeArchHausdorffMomentDifferencesNonnegative_iff_weightedTailNonnegative`
- `rectangularPrimePolarSource_negativeAbscissa_le_one_iff_weightedHausdorffTailNonnegative`
- `re_xiCentral_scaledBasis_weightedDegree_le_twentySix_nonneg`
- `scaledPrimeArchEndpointHausdorffDifference_weightedDegree_le_twentySix_nonnegative`
- `re_xiCentral_scaledBasis_totalDegree_le_thirteen_nonneg`
- `scaledPrimeArchEndpointHausdorffDifference_totalDegree_le_thirteen_nonnegative`

The named module builds successfully. `#print axioms` for the principal value identity, scaled-sum identity, off-line one-quarter bound, 616-condition rectangle, residual-tail reduction, degree-thirteen corollary, and prime--polar equivalence reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] 0 -> 1 in-progress: exact source/divisor identity and endpoint sector attack are well posed
- [x] 1 -> 2 fully-proven: complete proof of the value identity and 616-condition rectangle
- [x] 2 -> 3 formalized: named Lean build and axiom audit pass
- [ ] 3 -> 4 publication-ready: not required for the active RH proof
- [ ] RH: prove the remaining global positivity outside the finite rectangle

## 2026-07-15 disk-Schur consumer

The paper theorem
`../../2-fully-proven/not_new_scientific_knowledge/xi-radial-jensen-schur-capacity-rigidity.md`
uses `xiCentralPolynomialMoment_eq_sourceMomentFunctional` as its zero-data elimination step.  It
takes the supremum of these exact values over real polynomials contractive on the fixed unit disk.
The source radius and one-eighty-fourth orientation sector then give the stronger exact law

```text
diskSchurCapacity = primeArchCentralCurvature.
```

The proof is a direct Schwarz--Pick estimate and works for complex coefficients.  Its deficit from
the centered radial Jensen mass is exactly half the global reflection energy.  Thus the polynomial
value relation feeds a closed analytic norm; the remaining orientation is carried by the
adjoint/absolute-value/polar channel rather than by a stronger holomorphic extremizer.
