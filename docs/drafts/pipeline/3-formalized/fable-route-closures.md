# Closure tasks in the consolidated review

- **ID:** fable-route-closures
- **Stage:** 3-formalized
- **Type:** FORMALIZED SCOPE REPORT
- **Source:** `docs/reports/review-1011/fable.md`, §12.3.
- **Goal:** Resolve all ten tasks in the explicitly named §12.3 with unconditional Lean proofs. §12.1 instead lists nine assemblies; the positivity ceiling belongs to both.

## Obligations

| Item | Required scope | Status |
|---|---|---|
| Calibrations of B13, Landing, DH | Exact scope of the three model theorems and joint rigidity | Euler-product Landing countermodel and Hamburger coefficient rigidity already formalized |
| Arithmetic constituents | Wiener obstruction and the bounded class | Closed for every half-plane boundary by `bounded_dirichlet_constituent_ne_zero`; positive survivor: finite-prime zero-set representative |
| First rung by sizes | Exact barrier and positive boundary theorem | Existing barrier; no new producer established |
| Section rings of the square | Tower product formula and planar ideal equality | Both already formalized; exact tower scope below |
| Covers and averaged families | Fixed-part and character-index laws, with rightmost-zero exception | Existing exact law counts the union of right-hand zero sets, not their sum; base survives every finite cover |
| S3 transfer | Exact implication and status of the transfer itself | Exact equivalence with RH under `Θ<1` already formalized; transfer remains unproved |
| Window and theta stages | Verification law and obstruction to unconditional induction | Verification, bounded aperture tower, exact theta rounding, and escaping first-atom failure rank already formalized; no universal obstruction for every theta construction |
| Scheduled sums and source completions | Exact criteria for all named routes | Existing criteria and scoped obstructions listed below; advancing-history bounds and arithmetic realization remain missing |
| Positivity census | Decide 70% at every bandwidth | Closed for the full integrable Fourier positivity class: test cost is at least `1+3/π²>13/10`; regularized countermodels exist at every bandwidth |
| Short mean values as detectors | Relocation invariance and positive density/census scope | Growing quadratic tests formalized: `N(T)E(T)=o(T)` on moving lines near the critical line; normalized `N(T)=o(T²)` on fixed lines right of it |

## Existing scope statements

- `ArithmeticPositiveDuality/AnApproachingIntegerNormEulerProduct.lean`,
  `exists_integer_norm_euler_product_not_landingLaw`: natural norms and coefficients,
  linear counting, continuation across the critical line, and failure of Landing.
- `HTGeometry/HamburgerFunctionalEquation.lean`,
  `coeff_eq_of_completed_functional_equation`: absolute Dirichlet convergence,
  the two completed boundary identities and strip decay force constant coefficients.
  The decay and polar-part conditions belong to its scope; the functional equation alone
  is not its full hypothesis.
- `AbsoluteGeometryOfSpecZ/BezoutIsAnEqualityOnThePlanarSquare.lean`,
  `planarValues_eq_prod`: values of sections vanishing on finitely many graphs equal
  the product of their contact ideals.
- `ArithmeticPositiveDuality/FiniteZeroRelocationPreservesTheMeanSpectrum.lean`,
  `relocatedZeta_meanSquare`, `relocatedZeta_fourierMean_log`,
  `relocatedZeta_fourierMean_off_spectrum`: finite rational relocation preserves the
  Carlson square mean and every fixed Fourier mean in `1/2 < σ < 1`.

The bounded constituent gap is closed in `ABoundedConstituentHasNoZeros.lean`.
`bounded_dirichlet_constituent_ne_zero` excludes every zero, with no restriction
on the half-plane boundary. Its positive survivor,
`exists_smooth_zero_set_representative_of_bounded_pure`, preserves the zero set
and bound under a suitable finite-prime projection.
[Paper proof and Lean status](../3-formalized/bounded-pure-dirichlet-series-have-finite-prime-zero-sets.md).
The stronger finite exponential polynomial divisor conjecture remains open;
it is no longer an input to constituent closure.

## Section and cover boundaries

- `HodgeTheoryOfAFixedPart/RiemannRochOnTheTowerHasTheGluingIndex.lean`:
  `exists_orbitLatticeMap_vanishing` constructs sections from the exact gluing count;
  `exists_orbitLatticeMap_first_graph` gives
  `n ≤ |x_n| ≤ σ(M)bAq^(bn)` on their first nonzero graph. This is the product-formula
  boundary of this tower construction; it is not a universal theorem about all geometries.
- `HodgeTheoryOfAFixedPart/WhatTheSectionsOfTheSquareCertify.lean`:
  restriction pays all contacts below a graph and one contact per prime above it.
  `primePointSection_spec` and `log_abs_primePointSection_lt` show why prime powers
  above the diagonal cannot be charged repeatedly. These are the positive and negative
  scopes of section restriction.
- `AbsoluteGeometryOfSpecZ/TheHodgeIndexOfANumberRingCountsTheZerosOfItsZetaFunction.lean`:
  `exists_le_negIndex_ringDefect_iff` identifies the index with the number of **distinct**
  right-hand zeros in the union of the factors' zero sets. Shared zeros count once;
  §12.3's unqualified character additivity is too strong.
  `exists_le_negIndex_ringDefect_of_zeta` proves the finite-cover obstruction.
- `AbsoluteGeometryOfSpecZ/InATowerTheSquareOfTheIntegersHasWeightOneOverTheDegree.lean`:
  `tendsto_ringZeroSum_div_degree_sub` gives the exact fixed-part dilution law.
  `eventually_ringPairing_div_degree_le` additionally assumes nonnegative twisted sums;
  it does not produce that sign. The rightmost-zero family method is outside this closure.

## Transfer and window boundaries

- `FamilyContinuationTheory/TheReturnTransferIsTheRiemannHypothesisUnderAStrip.lean`:
  `homogeneousReturnWindowTransfer_of_riemannHypothesis` proves the reverse implication;
  `homogeneousReturnWindowTransfer_iff_riemannHypothesis` gives the exact equivalence
  under `Θ<1`. Removing that premise or proving the transfer is not supplied by the equivalence.
- `VerifiedHeightRungs/WindowEntries.lean`,
  `windowPositiveAt_of_rhVerifiedThrough`: verification through `windowHeight a`
  supplies positivity at aperture `a`.
- `WindowTowerOfSpecZ/TheFirstFoldPaysANegativeFrozenDirection.lean`,
  `exists_first_stage_negative_frozen_positive_complete`: a smooth window test has
  negative first frozen-stage energy and positive complete Weil energy. The omitted
  signed prime fold can supply positivity; frozen-stage positivity is not automatic.
- `ArithmeticIncidencePositivity/TheWeilFloorTowerIsFrozen.lean`,
  `weilFloorApertureLimit_bounds`: the strictly increasing aperture tower converges
  below `0.3621`, within `10^(-7800000)` of its base. Its positive survivor is a
  convergent tower of certified windows; no stage reaches `log(3)/2`.
- `ConjugateDiagonalGeometry/EffectiveThetaCollisionRounding.lean`,
  `riemannHypothesis_iff_uniform_floor_finiteThetaCollisionReading_eq_zero`:
  uniform zero rounded charge for every height and every stage `n≥6` is exactly RH.
  Heightwise rounding at the explicit threshold uses the actual collision gap;
  convergence of the readings alone does not force their rounded values to vanish.
- `CompletedArithmeticForms/FirstAtomRankBoundary.lean`:
  `exists_firstAtom_signed_moment_neg` excludes an all-order positive center for
  the literal first atom. Nevertheless `firstAtomSignedHead_posDef_eventually`
  makes every fixed head positive on its own cofinal ray, and
  `firstAtomFailureRank_tendsto` sends the first failing rank to infinity.
  This separates fixed-rank positivity from all-order positivity; the obstruction
  does not extend to the complete theta source by the same argument.

## Advancing-source completion

The scheduled-sum criteria already have exact Lean statements:

- FU: `MobiusDivisorOneSidedPowerGapBootstrap.lean`,
  `riemannHypothesis_iff_mobiusDivisorSquareRootAbel_bddAbove_of_powerGaps`,
  identifies RH with an upper bound for the normalized Abel moment on any
  sampling set with backward gaps `O(N^(1−δ))`, `δ>0`.
- CFC: `CCM/CCMFirstClockTailLowerBoundCompleteness.lean`,
  `ccmFirstClockPublishedSourceEventuallyBoundedBelow_iff_rh`, identifies RH
  with a constant lower bound for the literal first clock on one aperture tail.
- RP: `SPEQuantileRieszRoutePLinearFloorCriterion.lean`,
  `riemannHypothesis_iff_routeP_history_eventual_linear_floor`, identifies RH
  with `defect(K)≥−B(K+2)` for every `K≥3`, for some nonnegative `B`.

Each equivalence retains the complete arithmetic history. None proves its floor.

`CompletedArithmeticForms/EulerCompletionAlongGrowingSources.lean` proves
`|fullErrorEnergy(X,M)−finiteSourceEnergy(errorIncrement(X,M),T)|≤1/(n+1)`
at `T=(n+1)(M+1)²`, uniformly for `1≤X<M`.
`tendsto_fullErrorEnergy_iff_finiteSourceEnergy_on_schedule` works for arbitrary
growing source cutoffs. This controls completion error, not the full source energy;
it does not discharge the arithmetic input of the other scheduled-sum routes.

The named source-completion routes have different boundaries:

| Route | Exact existing result | Remaining input |
|---|---|---|
| SEC | `TimeOneGammaJetFockRHCriterion.timeOneGammaJetFockBounded_iff_re_eq_half`: at every strip parameter and base `x₀>1`, factorial-jet boundedness is exactly `Re s=1/2` | Boundedness at actual zeros |
| CDC/BSH | `ConstitutiveDaggerConfluence.actualRepairProofErasureConsistent_iff_re_eq_half`: for `n≥2`, consistency of the canonical repair potential is exactly `Re s=1/2` | Arithmetic consistency at actual zeros |
| APF | `CCMArithmeticPrimeFredholmTrace.completedXi_horizontalOrientation_eq_zero_iff_sourceTrace`: vanishing at the real source label is exactly vanishing of every source trace coefficient there | Exhaustion of the full divisor, including arbitrary nonreal centered labels |
| EWJ | `PaperEulerWoldCompactCharacter.paperEulerWoldHistoryOperator_compact_iff`: compactness exactly when `c=0` or `−a+b+2d=0`; essential distance is `(8/3)‖c‖²|−a+b+2d|` | A source identity outside this vanishing plane; the endpoint has positive essential distance |
| RFHM | `JointAncestryAllPrimeReversibleRFHMSewingNoGo.not_JASAllPrimeReversibleRFHMSewing`: reversible literal insertion cannot retain nonempty prime support; every surviving output has empty support | A different source law retaining arithmetic orientation |
| WBF | `PaperCriticalGenealogyCompletion.paperCriticalGenealogyCompletion_iff`: positive finite relative determinant completion is exactly the Hilbert–Schmidt condition on the weight | Arithmetic certificate stream and identification with the complete Xi/Weil form |

These results do not prove a universal impossibility of source completion. They identify
the missing arithmetic input or classify a specified construction.

## Positivity question

**Closed for the full integrable Fourier positivity class.**
`positivity_test_cost_ge_totient_limit` proves

```
[h(0)+∫_[-1,1]|α|h(α)dα]/g(0) ≥ 1+3/π² > 13/10
```

for continuous integrable `g≥0`, with `g(0)>0`, integrable real Fourier
transform `h=𝓕g`, and `h≤0` outside the unit band. Thus this positivity
method has census ceiling at most `1−3/π²<7/10`.
[Paper proof and Lean declarations](totient-grid-lower-bound-for-the-full-positivity-lp.md).

The positive survivor is an exact family of totient grid laws with origin
mass tending to `1+3/π²`. Their positive Fourier coefficients give the bound
for every admissible test. Gaussian regularization also supplies continuous
even form factors with integrable perturbations of one, exact unit-band data,
and nonnegative pair densities, whose Frobenius values exceed `13/10` at
any prescribed bandwidth.
[Regularized countermodels](totient-grids-obstruct-seventy-percent-at-every-bandwidth.md).

At bandwidth `4/3`, the separate
[finite-spike theorem](positivity-seventy-percent-four-thirds.md)
also imposes `F≥1` outside the unit band. That extra constraint is outside
the full-class obstruction above.

[Parseval forces excess pair density](pair-density-excess-is-forced.md)
explains why a nonnegative deficit cannot supply the origin mass: its bound
is `A≤(3+√(11/3))/4<13/10`. An integrable square-integrable signed deficit
with `g≤1` and exact low band must have `∫(g₋²+g₋)≥11/75` when `A≥13/10`.

## Growing quadratic tests

[Growing quadratic tests ignore finite relocation](../3-formalized/growing-quadratic-tests-ignore-finite-relocation.md)
proves a uniform `O(1/t)` bound for the squared-modulus difference on
`3/8≤Re s≤5/8`. Consequently arbitrary moving-line trigonometric tests with
term count times coefficient energy `o(T)` preserve the normalized quadratic mean.
The unconditional witness uses actual critical-line donors, an off-line target at
real part `3/4`, and preserves the completed functional equation and `R(0)=R(1)=1`.
The model loses ordinary Dirichlet-series structure; arithmetic distinguishability
is outside this conclusion.

