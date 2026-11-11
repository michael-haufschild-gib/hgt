# Shifted Selberg factorization, profile limits, and derivative control

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** A111, `levinson-gate-from-below-square-root-twists.md`.

## Exact factorization

Let `A_s=(μ(n)n^s)*(1/n)` under Dirichlet convolution, and restrict
`A_s` to integers supported on primes dividing `r`, writing `A_{s,r}`.
Push `W_s(r,u,v)=μ(r)A_{s,r}(u)A_{s,r}(v)/r²` forward under
`(r,u,v)↦(ru,rv)`. Its bivariate convolution with the diagonal coefficient
`d^(s−1)` and two reciprocal Möbius rows is exactly
`μ(m)μ(n) gcd(m,n)^(1+s)/(mn)` for positive `m,n`.

At prime powers, `A_s(p^k)=(1−p^(1+s))/p^k` for `k≥1`.
Dirichlet inversion and pair-coprime multiplicativity give the identity;
finite divisor rearrangement collapses every weighted principal factor
to a harmonic sum of two Möbius transforms.

For retained fibres `ru,rv≤N`, `N>1`,
`|W_{C/log N}(r,u,v)|≤exp(4|C|)|W_0(r,u,v)|`.
The absolute triple mass is summable and its unshifted signed mass is one.
The corresponding summable pair majorant is
`A(m,n)=Σ_{r|gcd(m,n)}|W_0(r,m/r,n/r)|`, with zero values on the axes.

## Polynomial limits and derivatives

For fixed polynomials `P,Q` vanishing at zero and any `v_N→v`, the full
corrected harmonic row with logarithmic weight `t^k` tends to
`∫₀¹ t^k (P′−vP)(Q′−vQ) dt`; profiles are evaluated at `1−t`.
The literal finite Möbius–gcd form equals this model at independent shifts
`(c,v)` and has this limit on `c=−2v`.

Complex continuation and Cauchy's estimate bound correction jets of order
`j` by `j! exp(4(|C|+1)) A(m,n)`. Every positive-order correction jet
vanishes, including bounded moving centres and the summed finite form.

Write `RP(x)=(1−x)P(x)`. A directional derivative `(κ,ν)` inserts `κt`,
replaces either profile by `νRP`, or differentiates the correction.
The last contribution vanishes. Applying this recurrence twice proves
both literal directional derivative limits.

Compact uniform profile bounds give one bound for all retained dilation
pairs and logarithmic powers. The derivative recurrence and real mean
value inequality give a Lipschitz constant in `v`, uniform in sufficiently
large `N`, for every corrected jet on each compact interval. Comparing a
moving shift with its limit proves all three literal form-jet limits for
arbitrary cutoffs tending to infinity along any filter.

## Actual twisted-moment coordinates

For coefficients `μ(n)n^(v/log N)P(1−log n/log N)`, the reflected gcd sum
has shifts `(c,v)=(2d log N,v)`; the direct sum has shifts
`(−2d log N,v+2d log N)`. Both identities include the normalization `log N`.
The actual linear mollifier is `P(x)=x`, `v=−d log N`.

## Lean

Namespace `GaloisForLFunctions.MultiscaleMollifiedZetaField`; all modules
below passed direct Lean checks and have umbrella imports.

- Exact Euler identities: `TheShiftedSelbergAmplitudeHasTheSameMajorant`,
  `TheShiftedSelbergCorrectionIsMultiplicative`, `TheShiftedSelbergEulerFactorsCancel`,
  `TheShiftedSelbergFormIsAHarmonicModel`.
- Summable real/complex correction bounds: `TheShiftedSelbergCorrectionKeepsItsSummableEnvelope`,
  `TheShiftedAmplitudeIsHolomorphic`, `TheCorrectionJetsKeepTheSummableEnvelope`,
  `TheShiftedCorrectionHasASummablePairMajorant`, `TheCorrectionCoefficientJetsHaveASummableMajorant`.
- Full polynomial limits: `TheCoupledEulerCorrectionPreservesThePolynomialLimit`,
  `TheCoupledShiftedSelbergFormHasThePolynomialLimit`.
- Literal derivatives: `ThePrincipalRowDerivativesShiftTheProfiles`,
  `TheCorrectedRowDerivativesHaveVanishingCorrectionTerms`, `TheCorrectedPolynomialJetsConverge`,
  `TheShiftedSelbergFormKeepsItsFirstTwoDerivatives`.
- Uniform parameter control and arbitrary reindexing: `TheCorrectedJetsAreUniformlyLipschitz`,
  `TheCorrectedJetLimitsAllowArbitraryHeights`.
- Original gcd identities and frozen jets: `TheActualGcdSumsAreShiftedProfileForms`,
  `TheFrozenGcdJetsHaveTheirProfileLimits`.

The exact jet statements appear in `shifted-selberg-euler-correction.md`.

Pole/chi main-term assembly and the Levinson gate remain obligations on
the parent card.
