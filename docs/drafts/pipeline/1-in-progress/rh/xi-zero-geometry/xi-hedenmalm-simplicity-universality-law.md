# Xi Hedenmalm simplicity universality law

- **ID:** xi-hedenmalm-simplicity-universality-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper proved, hostile-audited, Lean-direct-checked; no priority claim)
- **Source:** Bottom-up join of terminal `XiZerosSimple` and pointwise multiplicity-one classifiers
  found in the post-Law-18 endpoint scan
- **Statement:** Xi simplicity is one datum simultaneously realized by quotient values,
  theta-evaluation density, continued-Cauchy closure, local Jordan normality, de Branges
  Bezoutians, complex theta first moments, all-order theta source jets specialized at the first
  surviving order, and every cut-dependent boundary-reflection jet. With RH, the same phase is
  exactly prime--Gamma sign, reciprocal self-adjointness, local Hermiticity, conservative metric
  existence, and positive-half theta sine-moment nonvanishing.

## Gates

- [x] 0 → 1 in-progress: theorem-first closure and exact hypotheses
- [x] Complete paper proof with no open dependency
- [x] Lean source passes `lake env lean <file>`
- [x] Direct tree-file Lean check
- [x] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Lean inputs

1. `xiThetaFirstQuotientValueConstraint_iff_simple`,
   `xiThetaEigenAlgebraicSubspace_dense_iff_simple`, and
   `xiContinuedCauchyToHedenmalmClosure_iff_simple` classify three global value, Hilbert, and
   continuation interfaces by `XiZerosSimple`.
2. `all_xiLocalJordanNormal_iff_simple` and
   `xiLocalJordanNormal_iff_multiplicity_one` classify global and local Jordan normality.
3. `xiHedenmalmBezoutian_self_ne_zero_iff_simple` classifies the pointwise de Branges diagonal by
   multiplicity one.
4. `xiThetaFirstQuotientValueConstraint_iff_thetaCuspFourierLaplaceFirstMoment_ne_zero`,
   `xiSupportMultiplicity_eq_iff_thetaCuspFourierLaplaceJet`, and
   `xiSupportMultiplicity_eq_iff_thetaCuspBoundaryReflectionDefectJet` supply explicit complex
   source-moment and cut-covariant boundary-jet classifiers.
5. `continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_riemannHypothesis` and
   `xiReciprocalOperator_isSelfAdjoint_iff_rh` classify the RH coordinate.
6. `all_xiLocalJordanMatrix_isHermitian_iff_rh_and_simple`,
   `exists_conservative_xiThetaMetric_iff_rh_and_simple`, and
   `riemannHypothesis_and_xiZerosSimple_iff_thetaCuspFirstSineMoment` classify the joint phase.

## Paper proof

Assume `XiZerosSimple`. Inputs 1 and 2 give the first four global certificate components. At each
support point, local normality gives multiplicity one; Inputs 3 and 4 then give the Bezoutian,
Fourier--Laplace jet, and every-cut boundary-reflection classifiers. The quotient/source theorem
gives complex first-moment nonvanishing at every Xi zero. Conversely, the certificate's quotient
value component recovers `XiZerosSimple` through Input 1.

For the RH extension, assume `RiemannHypothesis ∧ XiZerosSimple`. The simplicity certificate is
already available. Inputs 5 and 6 give prime--Gamma sign, reciprocal self-adjointness, all local
Hermitian blocks, a conservative divisor metric, and the real positive-half sine-moment law.
Conversely, prime--Gamma sign recovers RH and the nested simplicity certificate recovers
`XiZerosSimple`. `[PROVED HERE]`

## Formalization target

- Module: `formal/GaloisForLFunctions/RHTower/XiHedenmalmSimplicityUniversalityLaw.lean`
- Simplicity certificate: `XiHedenmalmSimplicityUniversalCertificate`
- Simplicity capstone: `xiZerosSimple_iff_hendenmalmSimplicityUniversalCertificate`
- RH certificate: `XiHedenmalmRHSimplicityUniversalCertificate`
- RH capstone: `riemannHypothesis_and_xiZerosSimple_iff_hendenmalmUniversalCertificate`

## Internal noncollision audit

`scripts/formal_tools.py research "Xi simplicity Jordan normal Hedenmalm Bezoutian theta source
moment eigenfunction dense Cauchy closure"` returned the individual endpoints and adjacent
orientation results but no common certificate. Direct usage search found no module importing and
consuming all five terminal `_iff_simple` families; existing capstones pair one RH classifier with
one simplicity chart at a time.

## Hostile literature audit

Exact searches for the internal names and combinations of Hedenmalm, Xi simplicity, Jordan
normality, Bezoutians, conservative metrics, theta-source moments, and eigenfunction completeness
found no collision. Hedenmalm's primary
[Spectral interpretation of Riemann zeta zeros](https://arxiv.org/abs/2606.17494) gives the
theta-based differential-operator eigenproblem and a conditional pair-self-adjointness framework,
but not these multiplicity classifiers or their simultaneous equivalence. Burnol's
[Two complete and minimal systems associated with the zeros of the Riemann zeta function](https://arxiv.org/abs/math/0203120)
connects zeta zeros, co-Poisson formulas, and de Branges Sonine spaces, but does not identify
simplicity with this quotient/Jordan/Bezoutian/source-jet/metric package. Baranov's
[Cauchy-de Branges spaces, geometry of their reproducing kernels and multiplication operators](https://arxiv.org/abs/2206.02175)
studies completeness and reproducing-kernel geometry abstractly, not the Xi-specific universal
certificate. Evidence supports noncollision only; no priority claim is made.

## Log

- 2026-07-22 — Found by enumerating terminal `_iff_simple` and multiplicity-one endpoints after
  Law 18, then reading exact signatures and downstream consumers.
- 2026-07-22 — Both capstones formalized and exact direct check
  `lake env lean GaloisForLFunctions/RHTower/XiHedenmalmSimplicityUniversalityLaw.lean` passed.
- 2026-07-22 — Hostile exact and neighboring-concept literature audit passed; nearest Hedenmalm,
  Burnol, and Cauchy-de Branges sources are materially different.
