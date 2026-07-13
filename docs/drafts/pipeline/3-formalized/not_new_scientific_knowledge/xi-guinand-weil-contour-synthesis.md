# Contour synthesis for the Xi Guinand--Weil resolvent algebra

- **ID:** `xi-guinand-weil-contour-synthesis`
- **Stage:** 3-formalized
- **Type:** VALUE RELATION / ANALYTIC INFRASTRUCTURE
- **Scientific status:** `[FORMALIZATION] [POSITIVE STATEMENT] [STANDARD COMPLEX ANALYSIS] [NOT AN RH PROOF]`

## Statement

For an entire function `g`, a nonzero point `p` strictly inside a rectangle `R`, and the
regularized Cauchy kernel already used by the formal Xi Guinand--Weil theorem,

```text
K_z(p) = p^(-1) - (p-z)^(-1),
```

Lean proves the exact synthesis law

```text
integral_(boundary R) g(z) K_z(p) dz = 2*pi*i*g(p).
```

It also proves the finite-superposition version with every boundary-integrability condition
discharged from the assumption that the packet lies strictly inside `R`.

The square of the rectangular two-edge Xi transform is entire.  Consequently every finite packet
of its values on the multiplicity-exact Xi divisor satisfies

```text
integral_(boundary R)
  sum_(q in T) h_(L,a)(z)^2 K_z(a_q) dz
  = 2*pi*i*sum_(q in T) h_(L,a)(a_q)^2.
```

These are exactly the resolvent kernels for which the source-side continued Guinand--Weil identity
is already formalized.

## Weighted argument principle

Lean additionally proves the factorization-facing weighted residue law

```text
integral_(boundary R) g(z) f'(z)/f(z) dz
  = 2*pi*i*sum_(rho in R) ord_rho(f)*g(rho).
```

It assumes an explicit finite zero product times an analytic nonvanishing cofactor on a
neighbourhood of the closed rectangle.  This form composes with the existing multi-peeling theorem
and avoids exchanging a contour integral with an infinite divisor sum.

## Lean implementation

The implementation is split across

```text
GaloisForLFunctions.RHTower.RectangleCauchyFormula
GaloisForLFunctions.RHTower.RectangleWeightedCauchyResidue
GaloisForLFunctions.RHTower.XiGuinandWeilContourSynthesis
GaloisForLFunctions.RHTower.FinitePeeling
GaloisForLFunctions.RHTower.XiGuinandWeilRectanglePeeling
GaloisForLFunctions.RHTower.XiGuinandWeilRectangleExhaustion
GaloisForLFunctions.RHTower.XiGuinandWeilSpectralRectangle
```

with principal declarations

```text
rectIntegral_cauchyFormula_entire
rectIntegral_mul_logDeriv_multi_zero
rectIntegral_mul_logDeriv_boxCount
rectIntegral_regularizedCauchySynthesis_entire
rectIntegral_finset_regularizedCauchySynthesis_entire
rectangularTwoEdgeTransform_differentiable
xiRectangularTwoEdgeTransform_sq_analyticOnNhd
rectIntegral_finset_xiRectangularTwoEdgeKernel_eq
rectIntegral_xiRelativeResolventTrace_of_factorization
rectIntegral_continuedPrimeArchSourceRelativeTrace_of_factorization
exists_finite_peel
xiC_zeros_closedRectangle_finite
exists_xiC_closedRectangle_factorization
rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_closedRectangleZeroSum
xiSpectralMultiplicity_eq_analyticOrderAt_toNat
exists_admissible_rectangle_containing_xiZeroCopy_finset
sum_xiZeroCopyClosedRectangle_eq_multiplicity_sum
rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_xiZeroCopyClosedRectangleSum
exists_admissible_rectIntegral_source_eq_xiZeroCopy_sum_containing
exists_admissible_rectIntegral_rectangularSource_eq_xiZeroCopy_sum_containing
exists_admissible_rectangularSource_normalizedContour_approximates_weil
```

All seven exact modules compile.

## RH leverage

The relation supplies the analytic conversion from the Xi logarithmic derivative to finite
rectangular spectral values.  It also identifies the same contour directly with the full continued
prime--archimedean source trace.  Every prescribed finite packet of multiplicity copies lies in an
automatically selected admissible rectangle, analytic zero order is proved equal to the copied
spectral multiplicity, and the contour value is therefore an exact finite sum in the same
`XiZeroCopy` carrier used by the formal RH criteria.

For the squared rectangular two-edge Xi test, all boundary selection, factorization,
multiplicity, and analytic-regularity obligations are discharged internally.  To obtain the target
dyadic prime-window inequality, the remaining obligation is source-side: evaluate or bound the
resulting continued prime--archimedean contour with the sharp main coefficient, then apply the
already formalized prime-only/theta reduction.

Absolute summability also promotes the cofinal finite-stage law to an approximation theorem: for
every positive tolerance, some automatically admissible normalized source contour lies within that
tolerance of the full rectangular Xi-Weil polarization.  No separate infinite divisor
sum/contour-interchange hypothesis remains.

## Gates

- [x] rectangle Cauchy formula for entire weights
- [x] regularized Cauchy synthesis
- [x] finite superposition with automatic boundary integrability
- [x] entireness of the squared rectangular Xi test
- [x] finite rectangular Xi-value contour identity
- [x] weighted rectangle argument principle
- [x] Xi relative-resolvent extraction under finite local factorization
- [x] full continued prime--archimedean source extraction on an admissible boundary
- [x] finite XiC zero set in every closed rectangle
- [x] exact finite-packet peeling with analytic multiplicities
- [x] automatic XiC factorization and source extraction on every admissible rectangle
- [x] exact module builds
- [x] cofinal pointwise-admissible rectangle-boundary selection
- [x] analytic zero order equals copied spectral multiplicity
- [x] exact finite copied-spectral-carrier contour law
- [x] squared rectangular two-edge specialization with regularity discharged
- [x] arbitrary-precision source-contour approximation of the full rectangular Weil value
- [ ] continued source contour evaluation at rectangular autocorrelation regularity
