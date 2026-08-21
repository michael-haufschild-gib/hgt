# Stage-2 → stage-3 formalization ledger — `not_new_scientific_knowledge`

Scope: every card in this folder must have its proven theorems formalized unconditionally in Lean 4
and then move to `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/`.

Folder size at sweep start (2026-08-16): **496** top-level cards, no subfolders.

## Working rules

0. **Search the Lean tree for the card's own content first.**  `universal-quadratic-root-ridge-density`
   was already fully formalized in `RHTower/UniversalQuadraticRootRidgeDensity.lean` while its Lean
   gate was still unchecked.  Run `scripts/formal_tools.py research "<the card's theorem>"` before
   writing anything.

- No added hypotheses standing for analytic inputs; no axioms; no `sorry`.
- Search the corpus first (`scripts/formal_tools.py research`, `rg`) before writing any new module —
  ~29 700 Lean files already exist.
- Check with `lake env lean <file>`; build only the oleans needed; wire new modules into the area
  umbrella but never build the umbrella.
- Audit axioms in a scratch file (`#print axioms`), expect only
  `propext`, `Classical.choice`, `Quot.sound`.
- One Lean process at a time; clean up stale processes.

## Promoted

| Date | Card | Lean module(s) |
|---|---|---|
| 2026-08-16 | `co6-involution-host-caveat` | `HTGeometry/InvolutionIdempotentHost.lean` |
| 2026-08-16 | `unbounded-one-coordinate-monodromy-obstruction` | `HTGeometry/ScalarMonodromyAlgebraicIndependence.lean` |
| 2026-08-16 | `suzuki-one-prime-fractional-carrier` | `RHTower/SuzukiOnePrimeFractionalCarrier.lean` (pre-existing) |
| 2026-08-16 | `endpoint-sheared-gram-ridge-parity` | `RHTower/EndpointShearedGramRidgeParity.lean` (+ `Z/2Z` sharpness witness) |
| 2026-08-16 | `finite-wick-contracted-interaction-matroid` | `HTGeometry/WickInteractionMatroidLabels.lean` (+ contraction rank law) |
| 2026-08-16 | `one-sided-compression-bound-not-bounded-operator` | `RHTower/OneSidedCompressionUnbounded.lean` |
| 2026-08-16 | `shifted-towers-do-not-fix-t0-tail-class` | `RHTower/ShiftedTowerTailClasses.lean` |
| 2026-08-16 | `shifted-euler-prime-orbit-pf2-failure` | `RHTower/ShiftedEulerPrimeOrbitPF2.lean` |
| 2026-08-16 | `theta-analytic-to-real-defect-kernel-is-offreal-divisor` | `RHTower/ThetaAnalyticRealDefectKernel.lean` |
| 2026-08-16 | `discriminant-cross-positive-interval` | `RHTower/DiscriminantCrossPositiveInterval.lean` |
| 2026-08-16 | `finite-degree-reciprocal-tests-height-limited` | `RHTower/FiniteDegreeReciprocalPerturbation.lean` |
| 2026-08-16 | `reciprocal-seam-t0-infinite-mass-obstruction` | `RHTower/ReciprocalSeamZerothMoment.lean` |
| 2026-08-16 | `real-source-microlocal-quartet-no-go` | `RHTower/RealSourceMicrolocalQuartet.lean` |
| 2026-08-16 | `single-even-frequency-not-stieltjes` | `HTGeometry/EvenFrequencySeamMoments.lean` |
| 2026-08-16 | `half-turn-repaired-frequency-not-markov` | `HTGeometry/EvenFrequencySeamMoments.lean` |
| 2026-08-16 | `positive-even-frequency-cone-not-markov` | `HTGeometry/EvenFrequencySeamMoments.lean` |
| 2026-08-16 | `finite-signed-even-frequency-atoms-not-markov` | `HTGeometry/EvenFrequencySeamMoments.lean` |
| 2026-08-16 | `bounded-half-turn-frequency-packets-fail-hankel` | `HTGeometry/EvenFrequencySeamMoments.lean` |
| 2026-08-16 | `finite-order-local-frequency-operators-not-markov` | `HTGeometry/EvenFrequencySeamMoments.lean` |
| 2026-08-16 | `relative-contraction-compression-exhaustion` | `HTGeometry/ContractionCompressionExhaustion.lean` |
| 2026-08-16 | `monomial-tail-gate-height-linear-no-go` | `RHTower/MonomialTailGateBound.lean` |
| 2026-08-16 | `loewner-contraction-congruence-normalization` | `RHTower/LoewnerCongruenceNormalization.lean` |
| 2026-08-16 | `bbm-pullback-metric-no-point-spectrum` | `RHTower/BBMMetricObstruction.lean` (pre-existing; wired + audited) |
| 2026-08-16 | `positive-jet-horizon-rh-level-blindness` | `RHTower/PositiveJetHorizonLevelBlindness.lean` |
| 2026-08-16 | `route-r-physical-bockstein-homological-nonerasure` | `RHTower/RouteRPhysicalBocksteinHomologicalNonErasure.lean` (pre-existing; verified + audited) |
| 2026-08-16 | `zeta-summation-constraint-graph-dense-collapse` | `RHTower/SummationGraphDenseCollapse.lean` |
| 2026-08-16 | `fixed-rank-hankel-tests-do-not-imply-stieltjes` | `RHTower/FixedRankHankelNonStieltjes.lean` |
| 2026-08-16 | `boundary-weyl-thresholds-have-no-formal-monotonicity` | `RHTower/BoundaryWeylThresholdNonMonotone.lean` |
| 2026-08-16 | `pole-budget-does-not-imply-uvarov-repair` | `RHTower/PoleBudgetUvarovNoGo.lean` |
| 2026-08-16 | `uvarov-repair-requires-boundary-kernel-positivity` | `HTGeometry/BoundaryKernelSchurSplit.lean` |
| 2026-08-16 | `rank-one-scalar-shadow-needs-kernel-exhaustion` | `HTGeometry/BoundaryKernelSchurSplit.lean` |
| 2026-08-16 | `stieltjes-bulk-exterior-christoffel-monotonicity` | `HTGeometry/StieltjesExteriorChristoffelMonotone.lean` |
| 2026-08-16 | `test-space-closure-q0-visible-rh` | `RHTower/ReciprocalAtomTestSpaceClosure.lean` |
| 2026-08-16 | `finite-rank-counterterm-kernel-visibility` | `RHTower/ReciprocalAtomCounterterm.lean` |
| 2026-08-16 | `continuous-counterterm-atom-locality` | `RHTower/ReciprocalAtomCounterterm.lean` |
| 2026-08-16 | `continuous-counterterm-local-domination-threshold` | `RHTower/ReciprocalAtomCounterterm.lean` |
| 2026-08-16 | `non-atomic-finite-rank-counterterms-rh-strength` | `RHTower/ReciprocalAtomCounterterm.lean` |
| 2026-08-16 | `source-aware-q0-alone-reciprocal-positivity` | `RHTower/ReciprocalAtomPolynomialApproximation.lean` |
| 2026-08-16 | `finite-hard-edge-counterterm-q0-rh-strength` | `RHTower/ReciprocalAtomPolynomialApproximation.lean` |
| 2026-08-16 | `support-vanishing-q0-filter-visible-rh` | `RHTower/ReciprocalAtomPolynomialApproximation.lean` |
| 2026-08-16 | `finite-boundary-ideal-q0-rh-equivalence` | `RHTower/ReciprocalAtomPolynomialApproximation.lean` |
| 2026-08-16 | `continuous-preconditioner-q0-visible-rh` | `RHTower/ReciprocalAtomPolynomialApproximation.lean` |
| 2026-08-16 | `uvarov-kernel-pregate-rh-equivalence` | `RHTower/ReciprocalAtomPolynomialApproximation.lean` |
| 2026-08-16 | `finite-prolate-channel-boundary-rh-strength` | `RHTower/ReciprocalAtomPolynomialApproximation.lean` |
| 2026-08-16 | `summable-exterior-boundary-measure-rh-strength` | `RHTower/ReciprocalAtomPolynomialApproximation.lean` |
| 2026-08-16 | `finite-linear-probe-rh-nonselection` | `RHTower/FiniteProbeRHNonselection.lean` |
| 2026-08-16 | `finite-codimension-landscape-rh-nonselection` | `RHTower/FiniteProbeRHNonselection.lean` |
| 2026-08-16 | `finite-seam-jet-rh-nonselection` | `RHTower/FiniteProbeRHNonselection.lean` |
| 2026-08-16 | `finite-type-source-functor-rh-nonselection` | `RHTower/FiniteProbeRHNonselection.lean` |
| 2026-08-16 | `shifted-stieltjes-hankel-strictness-infinite-support` | `HTGeometry/ShiftedHankelStrictPositivity.lean` |
| 2026-08-16 | `all-order-seam-jet-function-complete` | `RHTower/SeamJetFunctionComplete.lean` |
| 2026-08-16 | `seam-log-derivative-weld-identity` | `RHTower/SeamWeldIdentity.lean` |
| 2026-08-16 | `triangular-seam-coordinates-function-complete` | `RHTower/SeamJetFunctionComplete.lean` |
| 2026-08-16 | `xf1-square-tests-outside-weil-class` | `RHTower/SeamSquareTestNotAdmissible.lean` |
| 2026-08-16 | `d2-countable-window-basis` | `RHTower/CountableWindowBasis.lean` |
| 2026-08-16 | `determinant-line-trivialization-zero-divisor-blindness` | `RHTower/DeterminantLineDivisorBlindness.lean` |
| 2026-08-16 | `acyclic-finite-fibers-derived-limit-zero` | `RHTower/AcyclicFiniteFibersDerivedLimit.lean` |
| 2026-08-16 | `translation-invariant-defect-form-orbit-classification` | `RHTower/TranslationInvariantDefectForm.lean` |
| 2026-08-16 | `xi-hurwitz-scalar-comparison-codimension-no-go` | `RHTower/HurwitzScalarComparisonNoGo.lean` |
| 2026-08-16 | `involutive-reflection-quadratic-rigidity` | `HTGeometry/InvolutiveReflectionQuadraticRigidity.lean` (+ `HTGeometry/FiniteOrderHadamard.lean`) |
| 2026-08-16 | `polynomial-drift-rational-outer-factor-rigidity` | `HTGeometry/PolynomialDriftRationalOuterFactorRigidity.lean` (+ `RHTower/FiniteZeroHadamardProduct.lean`, `HTGeometry/PolynomialDriftExpansion.lean`, `HTGeometry/FiniteOrderPolynomialDescent.lean`, `HTGeometry/AlgebraicOverStateFieldOrder.lean`) |
| 2026-08-16 | `ht-infinite-additive-torsor-staircase` | `HTGeometry/DerivativeShadowStaircase.lean` (+ `HTGeometry/OneSidedJetIndependence.lean`) |
| 2026-08-16 | `prime-translation-koszul-off-unitary-contractibility` | `RHTower/PrimeTranslationKoszulOffLine.lean` (+ `HTGeometry/KoszulCartanContraction.lean`, `RHTower/UnitaryResolventOffCircle.lean`) |
| 2026-08-16 | `prime-loop-connectivity-mixed-word-obstruction` | `RHTower/PrimeLoopMixedWordObstruction.lean` |
| 2026-08-16 | `reciprocal-seam-admissible-domain-q1` | `RHTower/ReciprocalSeamAdmissibleDomain.lean` |
| 2026-08-16 | `finite-t0-schur-threshold-divergence` | `RHTower/FiniteT0SchurThresholdDivergence.lean` |
| 2026-08-16 | `hurwitz-quadratic-n2-density-shadow` | `FullyProvenNewTargets.hurwitz_quadratic_n2_density_shadow` (pre-existing; verified + audited) |
| 2026-08-16 | `semilocal-prolate-control-deformation` | `RHTower/SemilocalProlateControlDeformation.lean` |
| 2026-08-16 | `semilocal-prolate-unitary-transport-trilemma` | `RHTower/SemilocalProlateUnitaryTransport.lean` |
| 2026-08-16 | `euler-support-transverse-divisor-rigidity` | `RHTower/RelativeStripDivisorReflection.lean` |
| 2026-08-16 | `euler-divisor-ultrametric-stability` | `RHTower/EulerDivisorUltrametricStability.lean` |
| 2026-08-16 | `universal-prime-side-orthogonality` | `Core.lean` (`cpow_inversion_scale`), `HTGeometry/OrbitBalance.lean` (pre-existing) + new `HTGeometry/PrimeSideOrthogonality.lean` |
| 2026-08-16 | `seam-firewall` | `HTGeometry/OrbitBalance.lean` (pre-existing) + new `HTGeometry/SeamFirewall.lean` |
| 2026-08-16 | `archimedean-prime-cross-term` | `RHTower/ZetaCarrier.lean`, `RHTower/ExteriorParity.lean` (pre-existing) + new `RHTower/ArchimedeanPrimeCrossTerm.lean` |
| 2026-08-16 | `shifted-reciprocal-moments-determine-divisor` | new `HTGeometry/AtomicMomentDeterminacy.lean` |
| 2026-08-16 | `tail-e-zero-support-nonselector` | `HTGeometry/AtomicMomentDeterminacy.lean` |
| 2026-08-16 | `reciprocal-seam-canonical-gauge-extraction` | new `HTGeometry/ReciprocalSeamGaugeExtraction.lean` |
| 2026-08-16 | `even-seam-finite-part-canonicality` | new `HTGeometry/EvenSeamFinitePart.lean` |
| 2026-08-16 | `friable-dirichlet-auxiliary` | `RHTower/FriableAuxiliary.lean`, `HTGeometry/SmoothNumbers.lean`, `HTGeometry/ZeroEstimate.lean`, `RHTower/ZeroEstimateUniformity.lean` + new `HTGeometry/SimplexTestSet.lean`, `RHTower/FriableCoefficientSurjectivity.lean`, `RHTower/FriableEdgeCoefficients.lean` |
| 2026-08-16 | `source-odd-quintic-successor-modulus` | `HTGeometry/SourceOddQuinticSuccessorModulus.lean` (pre-existing) + new `HTGeometry/SourceOddLowAritySuccessorOrbits.lean` |
| 2026-08-16 | `dss-lower-bound-orbit-nogo` | `HTGeometry/PrimeTorusKroneckerDensity.lean`, `RHTower/SuzukiApertureLiouvilleDense.lean`, `HTGeometry/ZeroEstimate.lean` (pre-existing) + new `HTGeometry/DSSOrbitEdgeOrthogonality.lean` |
| 2026-08-16 | `f1-two-face-criterion` | `HTGeometry/OrbitBalance.lean`, `HTGeometry/ArchimedeanCorank.lean` (pre-existing) + new `HTGeometry/F1TwoFaceCriterion.lean` |
| 2026-08-16 | `zero-estimate-uniformity` | `HTGeometry/ZeroEstimate.lean`, `RHTower/ZeroEstimateOrder.lean` (pre-existing) + new `RHTower/ZeroEstimateUniformity.lean` |
| 2026-08-16 | `stieltjes-log-weld` | `RHTower/StieltjesWeld.lean`, `RHTower/StieltjesLogWeldTierOne.lean` (pre-existing) + new `RHTower/DirichletMonomialIndependence.lean` |
| 2026-08-16 | `projective-horizon-pure-tail-fermionic-fiber` | pre-existing chain (`ProjectiveHorizonPureTailFiber`, `OccupationFactorInjective`, `PureFibreOccupationBijection`, `PureFibreCardinality`, `ShiftInvariantSubspace`, `QuotientIdealDivisor`, `QuotientIdealDimension`, `InvariantSubspaceRootSubset`, `RootSubsetInvariantSubspace`, `InvariantSubspaceIff`) + new `HTGeometry/PureFibreExteriorOccupation.lean` |
| 2026-08-16 | `projective-horizon-irreducible-simple-ramification` | pre-existing chain, verified + audited: `HTGeometry/SquaredJetCoefficientIndependence.lean`, `HTGeometry/DualRectangularSection.lean`, `HTGeometry/SchurCofactorLocus.lean`, `HTGeometry/CriticalSchurPrimeDivisor.lean`, `HTGeometry/CriticalSchurGenericCorank.lean`, `HTGeometry/CriticalSchurUniformizer.lean` |
| 2026-08-16 | `leading-laurent-coefficient-differential-algebraicity` | `HTGeometry/CoefficientwisePowerSeriesDerivation.lean`, `HTGeometry/FormalParameterRelationNormalization.lean`, `HTGeometry/LaurentCoefficientwiseDerivation.lean`, `HTGeometry/LeadingLaurentCoefficientDescent.lean` |
| 2026-08-16 | `koszul-acyclicity` | `RHTower/EHKoszulDuality.lean` (pre-existing, finite) + new `RHTower/EHKoszulLimit.lean` (the limit statement, arbitrary infinite index type) |
| 2026-08-16 | `euler-source-finite-jet-local-openness` | `RHTower/EulerSourceJetJacobian.lean` (pre-existing, algebraic) + new `RHTower/EulerSourceJetOpenness.lean` (holomorphic IFT + Dirichlet expansion + identity theorem) |
| 2026-08-16 | `c5-jensen-perturbation-lemma` | new `HTGeometry/HyperbolicCriticalAlternation.lean`, `HTGeometry/LocalizedPerturbationHyperbolicity.lean`, `RHTower/CriticalScaledHermite.lean` (uses pre-existing `HTGeometry/SignAlternationHyperbolicity.lean`, `RHTower/SpurHermite.lean`) |
| 2026-08-16 | `fid-shifted-hankel-strict-total-positivity` | new `HTGeometry/SparsePolynomialPositiveRoots.lean`, `HTGeometry/GeneralizedVandermondePositive.lean`, `HTGeometry/CauchyBinet.lean`, `RHTower/FIDHankelTotalPositivity.lean` |
| 2026-08-16 | `pa9-turan-newton-floor` | new `HTGeometry/NewtonInequalities.lean`, `RHTower/TuranNewtonFloor.lean` |
| 2026-08-16 | `li-reciprocal-chebyshev-kernel` | new `RHTower/LiReciprocalChebyshevKernel.lean` |
| 2026-08-16 | `hd3-li-gauge-shift` | new `RHTower/HD3LiGaugeShift.lean` |
| 2026-08-17 | `additive-heat-diagonal-generates-full-operator-algebra` | new `HTGeometry/DiagonalCommutantGeneration.lean`, `HTGeometry/GaussianToeplitzGeneration.lean` |
| 2026-08-17 | `finite-jet-secant-detection-rank` | new `HTGeometry/MonomialJetSecantRank.lean` (uses pre-existing `HTGeometry/AlgebraicIndependenceFromDifferentials.lean`) |
| 2026-08-17 | `two-prime-real-euler-transition-selector` | new `RHTower/EulerTransitionSelector.lean` (uses pre-existing `RHTower/TwoDilationDivisorMetric.lean`) |
| 2026-08-17 | `rational-rank-two-multiple-elliptic-gamma-da` | `HTGeometry/MultipleEllipticGammaPeriodRankDichotomy.lean`, `HTGeometry/MultipleEllipticGammaCommonStepNilpotence.lean` (pre-existing) + new `HTGeometry/MultipleEllipticGammaRankTwoDA.lean` |
| 2026-08-17 | `equivariant-causal-hessian-kernel-fidelity-rigidity` | new `HTGeometry/UnitaryConjugationMatrixUnits.lean`, `HTGeometry/TwoBlockUnitaryAlgebra.lean`, `HTGeometry/ConjugationEquivariantClassification.lean`, `HTGeometry/EquivariantCausalizerClassification.lean`, `HTGeometry/EquivariantCausalizerPositivity.lean` |
| 2026-08-17 | `completed-prime-gamma-second-moment-four-crossing-law` | `RHTower/CompletedPrimeGammaSecondMomentCenterPositive.lean`, `RHTower/CompletedPrimeGammaMomentFarRightAsymptotic.lean` (pre-existing) + new `RHTower/CompletedPrimeGammaSecondMomentFourCrossing.lean` |
| 2026-08-17 | `universal-quadratic-root-ridge-density` | `RHTower/UniversalQuadraticRootRidgeDensity.lean` (pre-existing; verified + audited) |
| 2026-08-17 | `corank-trdeg-realization-locus` | new `HTGeometry/CorankTrdegRealizationLocus.lean` (uses pre-existing `HTGeometry/SymmetricBlockAlgebraicIndependence.lean`, `HTGeometry/PrimeRadialRelativeJetRank.lean`, `HTGeometry/StateFieldTrdeg.lean`) |
| 2026-08-17 | `prime-source-cancellation-budget` | new `RHTower/PrimeSourceCancellationBudget.lean`, `HTGeometry/ComplexExponentialPolynomial.lean`, `HTGeometry/PrimeValuationLeadingEchelonInfinite.lean` (+ complex layer appended to `HTGeometry/ExponentialPolynomialZeroBound.lean`; uses pre-existing `HTGeometry/ExponentialTypeZeroDensity.lean`, `RHTower/PrimeLogExponentialTypeUniqueness.lean`, `RHTower/XiShiftPrimeHypertranscendence.lean`) |
| 2026-08-17 | `completed-logderiv-full-translation-orbit-freeness` | new `RHTower/XiTranslationOrbitFreeness.lean` (uses the three modules added for `prime-source-cancellation-budget`, plus pre-existing `RHTower/XiUpperEndHypertranscendence.lean`, `HTGeometry/UpperEndRationalCoordinateDifferentialAdjoin.lean`, `HTGeometry/FiniteAbscissaDirichletUpperEnd.lean`) |
| 2026-08-17 | `entire-multiplier-translation-defect-universality` | new `HTGeometry/EntireMultiplierDefectUniversality.lean` (uses pre-existing `HTGeometry/EntireBezout.lean`) |
| 2026-08-17 | `gamma-reflection-clock-observable-split` | new `HTGeometry/GammaReflectionClockObservables.lean` (uses pre-existing `HTGeometry/MeromorphicGammaReflection.lean`, `HTGeometry/MeromorphicGammaOrbit.lean`, `HTGeometry/MeromorphicReflection.lean`) |
| 2026-08-17 | `prime-zero-susceptibility-transverse` | new `RHTower/PrimeZeroSusceptibility.lean` |
| 2026-08-17 | `u0-phi-independence` | already formalized: `U0/U0AllNonexceptionalConnected.lean` |
| 2026-08-17 | `u0-phi-independence-disconnected` | already formalized: `U0/U0AllNonexceptionalDisconnected.lean` |
| 2026-08-17 | `fixed-taylor-modulus-ht-real-rootedness-nonselection` | new `HTGeometry/FixedModulusRealRootednessNonselection.lean` |
| 2026-08-17 | `archimedean-generator-axis-mode` | new `RHTower/BohrGeneratorAxisMode.lean` (uses pre-existing `HTGeometry/BohrGenerators.lean`, `RHTower/ArchimedeanAxisMode.lean`, `HTGeometry/GammaLogDeriv.lean`) |
| 2026-08-17 | `two-sources-of-hypertranscendence` | new `HTGeometry/OrbitBalanceRationalComplete.lean` (uses pre-existing `HTGeometry/RationalOrder.lean`, `HTGeometry/RationalOrderComposition.lean`) |
| 2026-08-17 | `multiplier-dichotomy-theorem` | new `HTGeometry/MultiplierDichotomyDegreeObstruction.lean` (uses new `HTGeometry/OrbitBalanceRationalComplete.lean` + pre-existing `HTGeometry/MultiplierDichotomy.lean`, `HTGeometry/ExpPolynomialDA.lean`) |
| 2026-08-17 | `finite-rg-jet-blindness-to-hypertranscendence` | new `HTGeometry/FormalGermFiniteJetShadow.lean` (new reusable formal-germ composition/inversion layer) |
| 2026-08-17 | `nyman-finite-mellin-ht-gauge-collapse` | new `RHTower/NymanMellinGaugeCollapse.lean` (uses pre-existing `RHTower/FractionalPartZeta.lean`, `HTGeometry/ZetaHypertranscendence.lean`, `HTGeometry/ExponentialSumDA.lean`, `HTGeometry/ComplexExponentialPolynomial.lean`) |
| 2026-08-17 | `lean-claim-review-row-010-pk-li-secular-change-of-basis` | new `RHTower/VorosPowerSumClosedForm.lean` (§A closed form) + pre-existing `RHTower/SecularMoments.lean` (§B) |
| 2026-08-17 | `seam-division-source-split-cancellation` | new `RHTower/SeamDivisionSourceSplit.lean` (uses new `RHTower/VorosPowerSumClosedForm.lean` + pre-existing `HTGeometry/GammaLogDeriv.lean`, `RHTower/ZetaRealStrip.lean`) |
| 2026-08-17 | `seam-two-lattices-archimedean-residue` | new `RHTower/SeamTwoLatticesArchimedeanResidue.lean` (assembles the four modules built earlier the same day) |
| 2026-08-17 | `leaf-reflection-bohr-projection-catastrophe` | new `RHTower/LeafReflectionBohrProjection.lean` (all four items of the card's Lean target, incl. the full nonnormality statement via the in-tree Vitali theorem, and the coefficient criterion proved rather than cited) |
| 2026-08-17 | `semilocal-sonin-two-place-positive-association` | new `RHTower/SoninSemilocalTwoPlaceCovariance.lean` (Poisson expansion + Tonelli + covariance assembly on top of the corpus Gamma-measure characteristic function) |
| 2026-08-17 | `entire-heat-holonomic-finite-spectrum` | new `HTGeometry/EntireHeatHolonomicFiniteSpectrum.lean` (includes an unconditional proof of D-finite ⟹ P-recursive for formal power series, previously absent from mathlib and the corpus) |
| 2026-08-17 | `arbitrary-finite-quartet-passport-realization` | five new `RHTower` modules: `CoshPolynomialQuasiPeriod`, `EnvelopeJetAgreement`, `QuartetSymmetryJets`, `QuartetPassportRealizer`, `QuartetPassportCapstone`; also records that `exists_scalar_add_simultaneousFlatPolynomial_pos_real_on_imaginaryAxis` is vacuous as stated |
| 2026-08-17 | `prime-arch-exact-finite-positive-atomic-block-rh` | new `HTGeometry/FiniteAtomicCubature.lean` (Carathéodory cubature: a limit of convex combinations of a compact `K ⊆ ℝ^N` is a combination of `≤ N+1` points; mathlib lacks compactness of convex hulls of compact sets) and `RHTower/PrimeArchExactAtomicBlock.lean` |
| 2026-08-18 | `xi-logderivative-real-boundary-divisor-measure` | new `HTGeometry/BoundaryCauchyKernel.lean`, `HTGeometry/WeightedAtomHilbert.lean`, `RHTower/RealBoundaryDivisorLimit.lean`, `RHTower/XiRealBoundaryDivisorMeasure.lean` (general Schwarz-real boundary divisor limit; Xi specialisation; weighted-atom Hilbert space with unitary translation; the limitation isolated as `↔ RiemannHypothesis` plus an explicit blind conjugate pair) |
| 2026-08-18 | `horizontal-entry-charge-transfer` | new `HTGeometry/HorizontalChargeTransfer.lean` (abstract multiset charge algebra: both charges even and nonnegative, `O = 0 ↔ on-line` under self-duality, the split `C − N = O + M`, and the collision transfer `(4r+2, r²−r) → (0, r²+3r+2)`; supersedes the card's own "no Lean declaration" note, and is not a wrapper — the pre-existing Xi module lacks `M`, the split, and the collision arithmetic) |
| 2026-08-18 | `projective-horizon-rectangular-schur-caustic` | new `HTGeometry/ProjectiveHorizonSchurCausticDivisor.lean` on top of the pre-existing `ProjectiveHorizonSchurCaustic.lean`: the `y₀^{2m}` row scaling (4), the Jacobi–Trudi transpose identification, the identity-block form of the full differential (5), and properness of the divisor via a unipotent jet point plus a Hensel-built truncated square root (replaces the card's appeal to a Pascal determinant) |
| 2026-08-18 | `semilocal-prolate-defect-triangular-determinant-blindness` | three new modules: `HTGeometry/StrictlyLoweringFiltration.lean` (filtration nilpotence + adapted-basis strict triangularity + `det(1+zB)=1`), `HTGeometry/TriangularKernelDeterminant.lean` (strictly triangular HS kernel ⟹ `det₂ = det₁ ≡ 1` for **every** `z`, termwise), `HTGeometry/QuasinilpotentLowering.lean` (spectrum `{0}` for a compact lowering operator, proved by a geometric power bound + total boundedness instead of Riesz perturbation theory) |
| 2026-08-18 | `bigraded-corank-dss-cross` | new `HTGeometry/BigradedCorankLattice.lean` (§A object + Prop A1 in both parametrisations + relation-lattice quotient reading; §B `U=0` column and `F_q` collapse; the `corank^{(1,0)} = ∞` floor from `linearIndependent_log_primes`) on top of the pre-existing §G anchor.  Records a correction: A1's `⟹` needs "full rank" read as linear independence of the monomials, not merely infinite span dimension |
| 2026-08-18 | `corank-seam-invariant` | new `HTGeometry/CorankSeamInvariant.lean` — both Lean targets: `corank(Λ_ff)=1` from a surjective degree map, and `corank=∞` over `ℚ` from the trivial prime-log relation lattice; plus the graded ladder and the level-separation witness `√2` (ℚ-linearly independent, algebraically dependent) |
| 2026-08-18 | `prime-density-local-unitary-zero-blindness` | new `RHTower/PrimeDensityLocalUnitary.lean` — the twist is a phase unitary (reuses `lpPhaseUnitary`), is *local* by complete multiplicativity + unique factorization, and the amplitude factors across an arbitrary prime bipartition (Schmidt rank one).  No infinite tensor model needed, contrary to the card's gate note; reuses the corpus `rankOneProj` |
| 2026-08-18 | `paired-euler-algebraic-closure-gap` | new `RHTower/PairedEulerPoleSeparation.lean` — the private boundary pole `2πi/log p`, its residue `1/log p` via the slope form of the derivative, regularity of every other and every reflected tangent there, and the conclusion that no finite combination of paired Euler tangents equals `2s−1` on the strip.  Uses an explicit interior approach sequence instead of an identity-theorem step |
| 2026-08-18 | `fe-orbit-quotient-half-trace-moments` | new `RHTower/FEOrbitQuotientMoments.lean` — the quotient divisor carries `m` not `2m` (via `analyticOrderAt_comp` at a simple square), the orbit total is `2m`, the log-coefficient series `ℓ_k` (branch-free: the logarithm is defined as the sum of branch logs and proved to exponentiate to the product), and the dictionary `T_k = −2k(−1)^k ℓ_k`.  Reuses the corpus `xiSquaredSeamEntireQuotient` |
| 2026-08-18 | `erosion-cocycle-reducibility` | new `RHTower/EulerCocycleReducibility.lean` — the observable dichotomy (`σ > ½`), the transfer dichotomy (`σ ≥ ½`, the named Tier-A target) and the **full** Parseval-form Theorem 19a including the `k`-sum.  Reuses the corpus `burnolSummable_prime_one_div_mul_log_sq` and `burnolNotSummable_prime_one_div` |
| 2026-08-18 | `archimedean-sampling-total-variation-defect` | new `HTGeometry/SamplingDefectTotalVariation.lean` (general order-zero defect = total mass, by inner regularity + Urysohn; sample-supported measures pair to zero) and `RHTower/ArchimedeanSamplingDefect.lean` (the theta measure, closedness of the prime-power logarithms, defect = `M_θ = Λ₀(1/2)`, the explicit `2e^{−2π}log 2` bound, and the completion doubling) |
| 2026-08-18 | `hd1-p1-hadamard-finite-part` | new `RHTower/XiHadamardFinitePart.lean` — the uncentered genus-one log derivative `ξ'/ξ(s)=∑_ρ[(ρ−½)⁻¹−(ρ−s)⁻¹]`, its Hadamard normalization at the origin, the absolutely summable double family and its two fiberings, the atlas expansion `−ξ'/ξ=∑_k P_k s^{k−1}`, `P_k=∑_ρ ρ^{−k}` for `k≥2`, divergence of `∑_ρ‖ρ‖⁻¹`, and the exact finite part `P₁ = Λ₀(0) = (γ−log 4π)/2+1`.  Reuses `XiC_eq_constant_mul_canonicalProduct` and `logDeriv_XiC_eq_relativeResolventTrace`; needs no Riemann–von Mangoldt count |
| 2026-08-18 | `critical-point-interpolation-ht-field-blindness-speiser` | new `RHTower/OrderOneFixedDivisorRigidity.lean` (general order-≤1 fixed-divisor rigidity through the first main theorem — no minimum modulus) and `RHTower/SpeiserCriticalPacketGauge.lean` (positive real-even multiplier `1+Q²` built directly on the packet, so the card's squared-orbit detour and its `a ≠ 0` restriction both drop; polynomial gauges keep the order-one envelope; the exponential gauge keeps the divisor and shifts `F'/F` by `Q'` but is forced back to exp-affine inside the cage).  Items 1–2 of the HT list are the corpus `differentialAdjoin_range_mulBase_eq` / `differentialIndependent_mulBase_iff` |
| 2026-08-18 | `quadratic-subtype-canonical-divisor-equivalence` (partial) | new `HTGeometry/CountableDivisorConvergenceExponent.lean` — the entire converse direction for an **arbitrary index type**: bucket summability criterion, exponent of convergence zero, genus-zero product convergence, the three-bucket estimate, and `∑ log(1+r/‖a i‖) = o((log r)²)`.  Closes sub-task 1 of the card's resumption plan; the remaining gap is the order of the product at each divisor point |
| 2026-08-18 | `quadratic-subtype-canonical-divisor-equivalence` (partial, cont.) | new `HTGeometry/EntireQuotientNormalForm.lean` (equal divisors ⟹ entire nonvanishing quotient, the general form of the corpus's `xiHadamardQuotient` construction) and `HTGeometry/EntireZeroDivisorIndex.lean` (the zero divisor indexed with multiplicity: local finiteness, avoidance of the origin, fiber cardinality); plus the genus-zero product's analyticity, non-vanishing and **divisor** in `CountableDivisorConvergenceExponent.lean`.  One bookkeeping identity (`divisorIdxCount` = the finsum divisor mass) remains before the forward direction closes |
| 2026-08-18 | `quadratic-subtype-canonical-divisor-equivalence` | **closed.**  New `HTGeometry/QuadraticSubtypeHadamard.lean` completes the forward direction: the zero-copy count of a disc *is* its divisor mass (`divisorIdxCount_eq`), so Jensen gives `SublogDensityIdx`; the genus-zero product over the zero divisor realizes it exactly; and the quotient is constant by a value-distribution argument (first main theorem + Poisson + Borel–Carathéodory) with no minimum-modulus estimate.  Supporting bricks: `EntireQuotientNormalForm.lean` (now also the monomial split) and `QuotientProximityBound.lean` (`proximity_quotient_le`, moved out of RHTower to remove duplication) |
| 2026-08-18 | `adjacent-zeta-dilation-entire-relative-hypertranscendence` | new `RHTower/AdjacentDilationDifferentialFreeness.lean` (the coefficient source `c_m`, its Ω-grade bound and prime-ray leading layer, and Theorem 1 in jet / formal-algebra / actual-carrier forms via the corpus Ω-leading-echelon criterion) and `RHTower/AdjacentDilationZetaBase.lean` (Corollary 2 by base adjunction, Theorem 3 by `differentialIndependent_mulBase_iff`, the Dirichlet transform `C_m(s)=ζ(ms)−ζ((m+1)s)`, and the manifestly entire pole-cancelled representative).  Equation (6) is cited from a parent card, not proved here |
| 2026-08-18 | `exponential-rational-shadow-bidegree-law` | **closed, all four items.**  `HTGeometry/RationalExponentialShadow.lean` (Lemma 1 by a degree argument replacing the pole-order case split), `HTGeometry/DerivEigenIndependence.lean` (Lemma 2), `HTGeometry/LinearDifferentialOperatorSeparation.lean` (the separation `Af=0 ⟹ Aq=0` and the operator/symbol dictionary), `HTGeometry/ExponentialRationalMinimalOrder.lean` (item 2, exact minimal order `r+1`), `HTGeometry/RadicalDerivativeDivisibility.lean` + `HTGeometry/RationalLogarithmicDerivativeRadical.lean` (item 3 on the shadow: `rad(N·M)` is exactly the reduced denominator of `h'/h`, by an exact multiplicity computation plus mathlib's `divRadical_dvd_wronskian_*`; and `deg rad(h)` = number of distinct finite zeros and poles), `HTGeometry/ExponentialRationalLeadingDegree.lean` (item 3 at operator level: Lemma 4's symbol factorization, polynomiality of the tail via the `mapRingHom` subring, `rad(h) ∣ c_{r+1}` and attainment), `HTGeometry/ExponentialModeAlgebraicIndependence.lean` (Lemma 5 with **no** transcendence input — algebraic independence is linear independence of the monomials, and every monomial in the modes is again a derivation eigenvector; Vandermonde transfer to the jets via the corpus `matrixSubst_injective` plus a new `transSubst_injective`).  Two corrections to the paper proof: the rigidity hypothesis in `linOp_eq_zero_separation` / `coeff_eq_zero_of_annihilates` had to be restricted to *constant* multipliers (the unrestricted form is false over `C(s)`: `c=s`, `μ=1/s`), and the order-`r+1` annihilator needs no reduced fraction for existence |

## Already carrying a stage-3 certificate (verify, then move the paper card)

- `square-aperture-von-mangoldt-correlation-energy` — forward implication and exact identity are
  formalized (`RHTower/CCMSharpPrimeWindowSquareCorrelationEnergy.lean`, axiom-clean). **Open gate:**
  the reverse implication `RH ⇒ C_M = O_δ(M^{1+δ})` needs a formal von Koch–Schoenfeld bound
  `|ψ(x) − x| ≪ √x log²x` under RH. Nothing weaker than `ψ(x) − x = O_ε(x^{1/2+ε})` is required.
- `universal-typed-event-network-fixed-carrier-no-go` — `HTGeometry/EventNetworkFixedCarrier.lean`
  covers the algebraic no-go; `HTGeometry/TraceClassQuantumCorner.lean` covers certified corners.
  **Open gate:** the literal Hilbert direct-sum corner must be proved completely positive, normal
  and trace-nonincreasing (i.e. construct a `TraceClassQuantumCorner` instance for
  `⊕^{ℓ²} H_i` with its inclusion isometries). The last card gate (monoidal-locality obstruction)
  is an open research target, not debt.

## In-flight card analyses (2026-08-17)

## In-flight card analyses (2026-08-16)

Cards whose remaining 2→3 obligation has been read and scoped, so the next session can start
directly.  None of these is blocked by open mathematics.

- **The in-tree PNT layer is usable**: `GaloisForLFunctions/PNTPlus/` carries `nth_prime_asymp`,
  `log_nth_prime_asymp`, `pi_nth_prime_asymp`, all axiom-clean.  Reach for it whenever a card needs
  `p_N ~ N log N` or `π(x) ~ x/log x`.
- `critical-line-abscissa-of-convergence` — the threshold `Σ_p p^{-2σ} < ∞ ⟺ σ > 1/2` is immediate
  from mathlib's `Nat.Primes.summable_rpow`.  The card's a.s.-convergence dichotomy additionally needs
  **Kolmogorov's three-series theorem**, which mathlib does *not* have (only the Kolmogorov continuity
  condition for processes).  That is the missing library for this card.
- ~~`c5-jensen-perturbation-lemma`~~ — **closed 2026-08-16**, stage 3.  Both 2→3 targets are Lean
  theorems (`hyperbolic_of_localized_perturbation`, `abs_second_derivative_criticalScaledHermite`).
  All four earlier Leaner return notes are answered structurally: the curvature bound is a window
  hypothesis, `m_i > 0` is derived by continuity (no `ρ_i`), the statement is uniform in `N`, and
  the perturbed critical point is located by a closed condition.  §2's `O(1)` barrier constant still
  rests on classical Hermite gap asymptotics, which the card credits as classical, and §3 remains
  the open C5 crux.
- `arbitrary-finite-quartet-passport-realization` — all named parents are formalized
  (`SimultaneousFiniteJetFlatness`, `FiniteHermiteCRT`, `FiniteFluxPassport`,
  `ImaginaryAxisPositiveRepair`, `CoshQuartetEnvelope`, `CoshPolynomialPeriodClassification`,
  `CoshPolynomialExactOrderOne`).  Remaining: the capstone assembly, which needs two new pieces —
  (i) a jet-agreement calculus for analytic functions (target jets prescribed as the Taylor
  polynomial of `ε_w (z-w)/A(z)`; reuse `deningerLocalJetPolynomial_iterateDerivative_eval`), and
  (ii) a **quasi-period** classification `F(z+h) = C F(z) ⇒ h = 0` generalizing the existing
  `coshQuartetEnvelope_mul_polynomial_periodic_iff` (which only covers `C = 1`).
- ~~`euler-source-finite-jet-local-openness`~~ — **closed 2026-08-16**, stage 3
  (`RHTower/EulerSourceJetOpenness.lean`).  Both remaining halves are done: the holomorphic
  inverse-function corollary via `HasStrictFDerivAt.map_nhds_eq_of_equiv` /
  `HasStrictFDerivAt.to_localInverse`, and the jets-to-half-plane-L-series step via a new
  jets-determine-the-germ lemma plus `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.
- `lean-claim-review-row-010-pk-li-secular-change-of-basis` — §B is formalized
  (`li_secular_pointwise`, `secular_li_pointwise_inv`).  Remaining: §A, the Voros closed form
  `P_k = 1 − (−1)^k ζ(k)/2^k − a_{k−1}`, which needs the `ξ'/ξ` decomposition (the corpus owns
  `RHTower/XiHadamardFactorization.lean`, `XiCanonicalProduct.lean`) and the digamma Taylor
  expansion with zeta values (`Hurwitz/PolygammaHurwitzValue.lean` has
  `polygamma_one_eq_riemannZeta`).
- `centered-ksgns-covariance-pythagoras` — blocked on a **Hilbert C\*-module / Paschke–KSGNS
  layer**, which mathlib does not have at all.  This is the largest single missing library named so
  far in this folder.

## Blocking-infrastructure analysis (2026-08-18 pass)

Each entry names the *exact* missing theorem and the route, so the next pass builds rather than
re-diagnoses.

0. **Hadamard factorization at order ≤ 1 — NOT a blocker; the corpus already owns it.**
   *Corrected 2026-08-18.*  `RHTower/XiHadamardGrowth.lean` closes the construction unconditionally:
   `xiHadamardQuotient_constant` (via `entire_log_affine_of_proximity_isLittleO_sq` fed by
   `xiHadamardQuotient_proximity_isLittleO_sq`, with evenness killing the linear term through
   `xiHadamardQuotient_deriv_zero`) and hence
   `XiC_eq_constant_mul_canonicalProduct : XiC = (fun _ => XiC 0) * xiCanonicalProduct`,
   axiom-clean.  The route taken there is the *proximity* one — a little-o bound on the Nevanlinna
   proximity function — so no Cartan/Boutroux minimum modulus and no Poisson–Jensen differentiation
   was ever needed.  Downstream consumers should import `RHTower.XiHadamardGrowth` (or
   `RHTower.XiRelativeResolventTrace`, which already exposes
   `logDeriv_XiC_eq_relativeResolventTrace`) rather than re-deriving anything.
   Related unconditional assets found in the same pass: `RHTower.xi_zeroCount_growth`
   (`N(r) = O(r log r)` for the ξ divisor in `B(2,r)`, i.e. the Riemann–von Mangoldt *bound* — the
   sharp asymptotic is still absent, but the bound alone settles every dyadic-tail estimate),
   `RHTower.xiSpectralPoint_inv_sq_summable`, `RHTower.not_summable_inv_norm_xiSpectralPoint`,
   `RHTower.four_lt_norm_xiSpectralPoint`.
   The superseded diagnosis follows, kept only because it records what mathlib carries.

0'. **(superseded)** Hadamard factorization at order ≤ 1 — the largest single lever.  The corpus already has the
   whole construction for `ξ` in `RHTower/XiHadamardFactorization.lean`: the multiplicity-exact
   canonical product (`xiCanonicalProduct`), its divisor match with `XiC`, the entire zero-free
   quotient (`xiHadamardQuotient`), its evenness, and an entire logarithm
   (`xiHadamardQuotient_has_log`).  The single missing step is
   `xiHadamardQuotient_constant_of_log_reBound`'s hypothesis: a real-part bound
   `Re L(z) ≤ C(1+|z|)^a`, `a < 2`, for the entire logarithm.  Given it,
   `HTGeometry.exists_linear_of_ne_zero_of_growth` finishes, and evenness kills the linear term.
   The bound needs a **lower** bound on `|xiCanonicalProduct|`, i.e. a minimum-modulus estimate —
   classically **Cartan/Boutroux**: for `a_1,…,a_n` and `H > 0`, outside discs of total radius `2H`
   one has `|∏(z−a_k)| > (H/e)^n`.  That is the brick to build.  The alternative route that avoids
   it entirely is **Poisson–Jensen**: differentiate `p+1` times to get
   `(f′/f)^{(p)} = −p!·Σ_k (z−a_k)^{−p−1}` using only an *upper* bound on `log|f|` on circles plus
   the Jensen boundary estimate, then integrate back.  **Mathlib already carries the ingredients for
   this second route** — checked 2026-08-18:
   `Mathlib/Analysis/Complex/JensenFormula.lean` has the Herglotz–Riesz (Poisson–Jensen) kernel
   average `circleAverage_re_herglotzRieszKernel_mul_log`, the Jensen formula
   `MeromorphicOn.circleAverage_log_norm` / `AnalyticOnNhd.circleAverage_log_norm`, and the divisor
   bound `AnalyticOnNhd.sum_divisor_le`; `Mathlib/Analysis/Complex/BorelCaratheodory.lean` converts
   a real-part bound to a modulus bound; `Mathlib/Analysis/Complex/Harmonic/Poisson.lean` has the
   Poisson formula.  (`Mathlib/Analysis/Complex/Hadamard.lean` is the *three-lines* theorem, not
   factorization.)  So the build is: Poisson–Jensen ⇒ `(ξ′/ξ)′(z) = −Σ_ρ (z−ρ)^{−2}` by letting the
   boundary term vanish on a radius sequence, then Liouville on the entire difference.  No
   Cartan/Boutroux minimum modulus is needed.  Either route unblocks:
   `hd1-p1-hadamard-finite-part`, `critical-point-interpolation-ht-field-blindness-speiser`
   (order-one fixed-divisor rigidity), `quadratic-subtype-canonical-divisor-equivalence`, and the
   order-one rigidity family generally.
1. **Riemann–von Mangoldt `N(T+1) − N(T) = O(log T)`.**  Every corpus statement currently carries the
   zero count as a hypothesis (`…_of_zeroCountBound`).  Route: Jensen (corpus
   `AnalyticOnNhd.sum_divisor_le`) on the disc `|s − (2+iT)| ≤ 4`, with the `exp(−πT/4)` Gamma factor
   cancelling between `max|ξ|` on the disc and `|ξ(2+iT)|`; needs two-sided Stirling for `Γ` on
   vertical strips, plus `|ζ(2+it)| ≥ ζ(4)/ζ(2)` from the Euler product.  Unblocks
   `gamma-tail-law-shifted-square-tests`, `bounded-support-weil-critical-tail-uniqueness`, the
   `…_of_zeroCountBound` family, and the divergence half of `hd1-p1-hadamard-finite-part`.
2. **Kolmogorov three-series.**  Absent from mathlib (only Doob/martingale machinery is present).
   Route: partial sums of independent mean-zero `L²` terms form an `L²`-bounded martingale, so
   `MeasureTheory.Submartingale.ae_tendsto_limitProcess` gives the sufficient half; the converse
   needs Kolmogorov's maximal inequality.  Unblocks `critical-line-abscissa-of-convergence` (whose
   elementary core is already `RHTower.EulerCocycle.summable_observableCoeffSq_iff`).
3. **Lerch's formula** `ζ_H′(0,a) = log Γ(a) − ½log 2π`.  In neither mathlib nor the corpus.
   Unblocks the `Γ = ζ-reg det` half of `gamma-module-construction`.
4. **Lipshitz diagonal D-finiteness** + torus-closure dimension — `G3-corank-dichotomy`.
5. **Differentiation under the Gamma integral with log powers** + Bell-polynomial `Γ^{(t)}` —
   `friable-moment-ladder-finite-dim` Theorem A (its Theorem B is a one-liner).
6. **Several-complex-variables currents** (Poincaré–Lelong, wedge of `dd^c log|F|`) —
   `euler-shift-pair-incidence-resultant` Theorem E only; A–D are elementary and already reachable.
7. **Reproducing-kernel Pontryagin spaces** — `euler-pick-node-window-nonlocality`.  The `≤`
   direction is trivial; the `≥` direction genuinely needs density of kernel sections in an RKPS,
   and the determinant/polarization shortcut fails (the sign of the leading minors is not controlled
   by nonvanishing alone).

## Known blocking infrastructure (shared across several cards)

1. **von Koch–Schoenfeld**: `RH → |ψ(x) − x| ≤ √x log(x)²/(8π)` for `x > 73.2`, or any
   `O_ε(x^{1/2+ε})` form. Blocks the reverse half of several RH-equivalence cards.
2. ~~Riemann–von Mangoldt zero counting~~ — **not needed**: the corpus already owns the
   unconditional genus-one convergence `RHTower.xiSpectralPoint_inv_sq_summable` and
   `RHTower.xiDivisorSupport_infinite` (`RHTower/XiCanonicalProduct.lean`,
   `RHTower/XiZerosInfinite.lean`), together with a complete Xi Hadamard factorization in
   `RHTower/XiHadamardFactorization.lean`. Use those wherever a card cites `N(T) = O(T log T)`
   only to get convergence of `Σ_ρ |ρ|^{-k}`, `k ≥ 2`.
3. ~~Hadamard factorization for finite-order entire functions~~ — **built, both halves**:
   `HTGeometry/FiniteOrderHadamard.lean` proves the zero-free half
   `exists_polynomial_exp_of_ne_zero_of_growth` (zero-free entire with
   `‖f z‖ ≤ exp(C(1+‖z‖)^d)` ⇒ `f = exp(polynomial)`) from `exists_entire_log_of_ne_zero`,
   `borel_caratheodory` and `exists_polynomial_of_polyGrowth`, together with the reusable
   `FiniteOrderEnvelope` predicate and its closure API;
   `RHTower/FiniteZeroHadamardProduct.lean` proves the divisor-carrying half
   `exists_polynomial_mul_expPolynomial_of_envelope` (finite order + finitely many zeros ⇒
   `p · exp q`) at every finite order, generalizing the corpus's subquadratic
   `RHTower.exists_finiteDivisorFactor_mul_exp_of_finite_zeroSet`.
4. ~~von Neumann algebra generation~~ — **built**: `HTGeometry/DiagonalCommutantGeneration.lean`
   defines `vonNeumannGen S = Set.centralizer (Set.centralizer S)` and proves
   `vonNeumannGen_eq_univ'` (a basis-diagonal algebra plus one operator with no zero matrix entry
   generates `B(E)`), and `HTGeometry/GaussianToeplitzGeneration.lean` supplies the `ℓ²(ℕ)`
   instance: the backward shift, diagonal `ℓ^∞` multipliers, the Gaussian Toeplitz operator with
   entries `exp(-π x (m-n)²)` as a norm-convergent shift series, and
   `vonNeumannGen_multiplierAlgebra_gaussToeplitz`.  Note the definition sidesteps the double
   commutant theorem, which mathlib still lacks; a card that genuinely needs SOT-closure = double
   commutant is *not* covered by this layer.
4b. **Automatic continuity of C\*-seminorms (Sebestyén)**: every C\*-seminorm on a C\*-algebra is
   dominated by the norm.  Needed by `cofinal-gamma-cstar-shilov-blindness` claim 4 (a locally
   C\*-closed ideal containing `c_00` contains every `Δ_t`).  The other four claims of that card
   are now within reach: claim 1 follows from the new `isCompactOperator_lpDiag`, claim 2 from
   `MemSchattenClass.one_summable_inner_diag_basis` together with the corpus's
   `summable_primeGammaCofinalBocksteinMagnitude_iff`, claim 3 from the norm-limit truncation, and
   claim 5 is already formalized (`regulator_eq_zero_of_contracts_cocycle`).  Note the elementary
   power trick gives the domination only on the finitely supported subalgebra; passing to all of
   `c_0` is exactly the automatic-continuity theorem.
4c. **Adamczewski--Dreyfus--Hardouin (ADH) rational-or-hypertranscendental theorem**: a
   Laurent-series solution of a homogeneous linear shift or Mahler equation with rational
   coefficients is rational or hypertranscendental over `C(s)`.  This is the single largest
   blocking import in the folder — **18 cards cite it** (grep `Adamczewski`), including
   `finite-commuting-shift-peeling-hypertranscendence-law`,
   `ultrametric-thermal-mahler-hypertranscendence`, `multiplier-dichotomy-theorem`,
   `q-geometric-generalized-free-field-hypertranscendence`, `schwarzian-projective-erosion-tower`.
   Formalizing it means building parameterized difference Galois theory (Hardouin--Singer) on top
   of a Picard--Vessiot layer for difference equations; nothing of that exists in mathlib or in the
   corpus.  Cards whose only gap is this citation should be grouped and closed together once the
   layer exists.
5. **Derived inverse limits** (`R lim` of a diagram of zero objects): needed by
   `acyclic-finite-fibers-derived-limit-zero`.
6. **Complex-dynamics layer** (Böttcher coordinate, equilibrium measure of a Cantor Julia set,
   winding-number integration): needed by the three `bottcher-*` monodromy cards.
7. **Fredholm determinants and Riesz spectral theory for compact operators** (eigenvalue stability
   under norm perturbation; `det_F(I + zB)` as the canonical limit of finite truncations): needed by
   `semilocal-prolate-defect-triangular-determinant-blindness`.  The strict-lowering, local
   nilpotence and finite-truncation-determinant parts are elementary; only the compact/trace-class
   extension clauses need this layer.
8. **Clunie composition growth** (`T(r, f ∘ g)/T(r,g) → ∞` for transcendental entire `f,g`, outside
   an exceptional set): needed by `autonomous-cap-derivative-shadow-law` and
   `asymptotically-exponential-algebraic-cascade-unit-cost`.
9. **Lipshitz diagonal `D`-finiteness** (the diagonal of a `D`-finite series is `D`-finite): needed
   by `G3-corank-dichotomy`.
10. ~~Selberg-class relative-strip rigidity~~ — **built**:
   `RHTower/RelativeStripDivisorReflection.lean` carries the abstract normal-convergence and
   divisor-reflection theorem named by `euler-support-transverse-divisor-rigidity`'s 2→3 gate
   (`differentiableAt_dirichletSeries`, `exp_dirichletSeries_ne_zero`, `mem_band_of_reflection`,
   `max_re_le_of_reflection`, `re_eq_half_of_reflection`, `eq_empty_of_reflection_lt_half`,
   `summable_of_sparse_support`, `summable_of_partialSum_bound`).  **Still open:** the concrete
   Selberg-class instantiation (an actual completed Euler product with its functional equation);
   the consumer `euler-divisor-ultrametric-stability` is now fully formalized and promoted, with
   `(NE)` discharged by `divisorExponent_le_of_reflection`.
11. **Torus shrinking targets** (Haar measure on `𝕋^V`, forest coordinates, Borel–Cantelli):
   needed by `coherence-graph-volume-recurrence-exponent-law`.
12. **Kummer/radical provider for `U0`** (`PhibKummerInputs` / `PhibRadicalData` /
   `PhibSquareRootDeckData` discharged unconditionally): the `u0-phi-independence*` wrappers in
   `FullyProvenNewTargets.lean` are otherwise complete.

## New reusable infrastructure added by this sweep

- `HTGeometry/ExponentialPolynomialZeroBound.lean` — **the extended-Chebyshev zero bound**
  (mathlib gap): a real exponential polynomial `∑ⱼ Pⱼ(x) e^{cⱼ x}` with distinct exponents and
  nonzero polynomial coefficients has strictly fewer distinct real zeros than its number of scalar
  coefficients (`card_lt_of_expPoly_eq_zero`).  Built from a reusable Rolle chain for arbitrary
  differentiable real functions (`exists_deriv_zeros`, `exists_iteratedDeriv_zeros`) and the
  polynomial calculus `P ↦ cP + P'` for derivatives of `P(x)e^{cx}` (`shiftD`, `deriv_polyExp`,
  `iteratedDeriv_expPoly`, `natDegree_shiftD_iterate`).  This is the real-shift half of
  `prime-source-cancellation-budget` and is cited by four further cards
  (`completed-logderiv-full-translation-orbit-freeness`, `nyman-finite-mellin-ht-gauge-collapse`,
  `prime-power-dirichlet-complex-jet-independence`, `quadratic-subtype-canonical-divisor-equivalence`).
- `HTGeometry/UnitaryConjugationMatrixUnits.lean` and `HTGeometry/TwoBlockUnitaryAlgebra.lean` —
  the coordinate toolkit for **conjugation-equivariant linear maps on matrices**: conjugation of a
  matrix unit by a diagonal unitary (`diagonal_conj_single`) or a permutation matrix
  (`permMatrix_conj_single`, `perm_transport`), the phase equation and the resulting support law
  `exists_offDiag_coeff` (an equivariant map sends `E i j` to a multiple of itself), diagonality of
  the image of `E i i` (`diag_image_offDiag_eq_zero`), `exists_perm_map_pair`, and the two-index
  block algebra `blockP/blockQ/blockZ/blockR` with the non-monomial unitary
  `blockUnitary = 1 + ((1+I)/2 - 1) P + ((1-I)/2) Q`, proved unitary
  (`blockUnitary_mem_unitaryGroup`) and satisfying `Vᴴ Z V = -I R`
  (`blockUnitary_conj_blockZ`).  This is the machinery that forces a two-parameter classification;
  it is the in-flight support for `equivariant-causal-hessian-kernel-fidelity-rigidity`.
- `HTGeometry/BoundedDiagonalOperatorLp.lean` — **diagonal operators on `ℓ²(I)` for an arbitrary
  index type** (the corpus's earlier diagonal modules are all `ℕ`-indexed or Hilbert–Schmidt-only):
  `lpDiag` with `norm_lpDiag_le` and `lpDiag_single`, the coordinate injection `lpSingleCLM`,
  compactness of finite truncations `isCompactOperator_lpDiagFinset`, and the capstone
  `isCompactOperator_lpDiag` — a bounded diagonal whose family vanishes along the *cofinite* filter
  is compact.  Needed whenever the index set is the primes or prime powers and the diagonal is not
  Hilbert–Schmidt.
- `HTGeometry/CorankTrdegRealizationLocus.lean` — the corank/transcendence-degree layer:
  `AlgebraicIndependent.add_const` (algebraic independence survives a rational translation, via the
  translation automorphism `shiftAlgEquiv` of `MvPolynomial`), `trdeg_adjoin_le_finrank_span`
  (transcendence degree of a generated field is at most the `ℚ`-dimension of the span of the
  generators), and the explicit free-plus-powers family `locusFamily` realizing every admissible
  pair.  The linear-independence engine — distinct monomials in an algebraically independent family
  are linearly independent — is `linearIndependent_locusFamily`.
- `HTGeometry/MonomialJetSecantRank.lean` — the confluent Vandermonde / secant layer:
  `span_jet_eq_top` (jets and jet derivatives at `k` distinct nodes span order-`m` jet space once
  `m+1 ≤ 2k`, proved through the dual polynomial `dualPoly` and a double-root count),
  `hasStrictFDerivAt_jetMap` with the explicit differential `jetMapDeriv`, the general submersion
  transfer `mvPolynomial_eq_zero_of_hasStrictFDerivAt_surj` (a polynomial vanishing on the image of
  a map with surjective strict differential is zero — the non-square companion of the corpus's
  `mvPolynomial_eq_zero_of_hasStrictFDerivAt_injective`), and the catalecticant obstruction
  `hankelPoly` with `hankelPoly_ne_zero` and `eval_hankelPoly_jetMap`.
- `HTGeometry/DiagonalCommutantGeneration.lean` — **generated von Neumann algebras** (mathlib gap):
  `vonNeumannGen S = Set.centralizer (Set.centralizer S)`, the rank-one basis projections
  `basisProj`, the diagonal algebra `diagonalOps b` of a Hilbert basis, the commutant computation
  `exists_diag_of_mem_centralizer` (commuting with all `basisProj` ⇒ diagonal), and the generation
  theorem `vonNeumannGen_eq_univ'`: a set containing every `basisProj b i` and one operator `A`
  with `⟪b m, A (b n)⟫ ≠ 0` for all `m, n` generates all of `B(E)`.  No double commutant theorem,
  no SOT density, no adjoints — only commutation against the projections.
- `HTGeometry/GaussianToeplitzGeneration.lean` — the `ℓ²(ℕ)` operator layer: `backShift` with
  `backShift_pow_coe` and `‖backShift‖ ≤ 1`, its adjoint `fwdShift` with
  `fwdShift_pow_eq : fwdShift ^ j = adjoint (backShift ^ j)`, the diagonal `ℓ^∞` multipliers
  `diagMul` with the operator-norm bound `‖diagMul c v‖ ≤ M ‖v‖`, the Gaussian Toeplitz operator
  `gaussToeplitz x` built as a norm-convergent two-sided shift series, its entry formula
  `inner_stdBasis_gaussToeplitz : ⟪e m, H x (e n)⟫ = exp(-π x (m-n)²)`, and the generation
  capstone `vonNeumannGen_multiplierAlgebra_gaussToeplitz`.  The evaluation helper
  `tsum_inner_apply` (entries of an operator tsum are the tsum of the entries) is reusable for any
  norm-convergent operator series.

- `RHTower/LiReciprocalChebyshevKernel.lean` — the FE-folded Li kernel `2 - 2T_n((4-y)/(4+y))` in the
  reciprocal seam coordinate, with `two_mul_chebyshevT_eval_half_add_inv`
  (`2T_n((z+z⁻¹)/2) = z^n + z^{-n}`, via mathlib's Dickson bridge), the explicit `L_1 = 4y/(4+y)`
  expansion on `‖y‖ < 4`, analyticity away from `y = -4`, and the absolutely convergent
  reciprocal-moment transform `tsum_liChebyshevKernel_one`.

- `HTGeometry/NewtonInequalities.lean` — **Newton's inequalities** (mathlib gap): for a real-rooted
  real polynomial of degree `d`, the normalised coefficients `A_k = c_{d-k}/C(d,k)` are log-concave.
  Built from the two operations that preserve real-rootedness — `hyperbolic_derivative` (from
  mathlib's `Polynomial.card_roots_le_derivative`) and `hyperbolic_reverse` (the reverse of a split
  polynomial with nonzero constant term splits, with reciprocal roots) — together with the
  coefficient transports `newtonCoeff_derivative` (`A_k ↦ d·A_k`) and `newtonCoeff_reverse`
  (`A_k ↦ A_{d-k}`).
- `RHTower/TuranNewtonFloor.lean` — the elementary-symmetric specialisation `newton_esymm`, the
  hypothesis-free floor `newton_floor_finite` (`(n+1)e_{n-1}e_{n+1} ≤ n e_n²` for *any* real
  family), the ratio form `turan_ratio_newton_floor` (`g_n ≥ (n+1)/n`), and the infinite-atom limit
  `newton_floor_limit`.

- `HTGeometry/CauchyBinet.lean` — **Cauchy–Binet for a rectangular product** (mathlib gap), in the
  permutation-symmetrised form `m!·det(A·B) = Σ_{f : Fin m → Fin N} det(A∘f)·det(f∘B)` over an
  arbitrary commutative ring: no increasing-enumeration bookkeeping, and the non-injective index
  functions drop out on their own.  Also `det_mul_eq_sum_fun` and `det_eq_sum_perm_row`.
- `HTGeometry/GeneralizedVandermondePositive.lean` — **generalized Vandermonde positivity**
  (mathlib gap): `det[x_l^{r_a}] > 0` for `0 < x_0 < … < x_{m-1}` and strictly increasing natural
  exponents.  Proved by the Descartes induction on the varying-node polynomial
  (`genVandermondePoly`), whose sparsity is read off the Laplace expansion.
- `HTGeometry/SparsePolynomialPositiveRoots.lean` — **the Descartes-type sparse root bound**
  (mathlib gap): a nonzero real polynomial with `k` nonzero coefficients has at most `k−1` strictly
  positive roots (`card_posRoots_succ_le`), by the Rolle interleaving induction.
- `RHTower/FIDHankelTotalPositivity.lean` — the `ζ(2(i+j)+3)` moment matrix, its identification with
  the odd zeta values (`fidHankel_eq_riemannZeta`) and its strict Hankel total positivity.

- `HTGeometry/HyperbolicCriticalAlternation.lean` — **interlacing for hyperbolic real polynomials**:
  strict monotonicity off the critical set, the gap-index counter `critBelow` and its injectivity,
  exactly one root in each of the `N` critical gaps, hence the sign alternation of the critical
  values plus the two outer sign changes; and `hyperbolic_of_sign_changes`, the consecutive
  sign-change form of the hyperbolicity certificate (either starting sign).
- `HTGeometry/LocalizedPerturbationHyperbolicity.lean` — **the localized `C¹` perturbation lemma**
  `hyperbolic_of_localized_perturbation`, with its three reusable steps: the second-order Taylor
  bound at a critical point (`abs_eval_sub_le_of_abs_second_derivative_bound`, proved by
  monotonicity of the comparison function), the curvature window (`exists_curvature_window`,
  `exists_perturbation_windows` — the positivity of the window-minimum curvature is *derived* by
  continuity, with no inflection-distance bookkeeping and no degree special cases), and the shifted
  critical point (`exists_perturbed_critical_point`, covering the zero-slope degenerate branch).
  Also `eventually_pos_atBot_of_leadingCoeff_pos_of_even`, the even-degree sign at `−∞`.
- `RHTower/CriticalScaledHermite.lean` — the Theorem-M critical rescaling `p ↦ a·p(·/√m)` and its
  ODE `C_d'' = (w/m)C_d' − C_d`, giving `κ = |C_d''(c)| = |C_d(c)|` at every critical point.

- `RHTower/EulerSourceJetOpenness.lean` — **closed-form `s`-jets of a nonlinear degree-one Euler
  flux, the holomorphic inverse-function corollary, and full-jet faithfulness.** `eulerJetPoly` is
  the Eulerian-type polynomial family for `(w ∂_w)^j (w/(1-w))`; `hasDerivAt_localFluxJet` /
  `iteratedDeriv_localFluxJet` / `iteratedDeriv_eulerFlux` give every `s`-derivative of the flux in
  closed form off the polar set; `hasStrictFDerivAt_eulerJetMap` identifies the differential at the
  trivial product with the weighted Vandermonde; `eulerJetMap_map_nhds_zero` and
  `hasStrictFDerivAt_eulerJetLocalInverse` are the openness / local-biholomorphism statements.
  Two independently reusable pieces: **`eventuallyEq_of_iteratedDeriv_eq`** (equal full jets
  determine an analytic germ in one complex variable — mathlib has the identity theorem from
  eventual equality but not from jets) and **`lSeries_degreeOneEulerPrimeFluxCoeff_eq`** (an
  all-prime Euler logarithmic flux is the Dirichlet series of its prime-power coefficient stream,
  with the von-Mangoldt domination `norm_degreeOneEulerPrimeFluxCoeff_le_vonMangoldt`).

- `RHTower/EHKoszulLimit.lean` — **infinite-variable symmetric functions and `e–h` reciprocity in the
  limit ring** (mathlib has neither). `esymLimit`/`hsymLimit` realize `e_k`, `h_k` inside
  `MvPowerSeries ι R` for an *arbitrary* index type; `eh_koszul_duality_limit` proves
  `Σ_{i+j=k} (−1)^i e_i h_j = 0` there for all `k ≥ 1`, and `esymGen_mul_hsymGen` gives `E(t)H(t) = 1`.
  Also: the squarefree-exponent calculus `sqfreeExp`, `support_sqfreeExp`, `degree_sqfreeExp`,
  `sqfreeExp_support_eq_self`, `card_support_eq_degree_iff` (squarefree ⟺ `card supp = degree`), and
  `sum_antidiagonal_sqfree_sign` (the alternating subset sum over an antidiagonal).

- `HTGeometry/FiniteOrderHadamard.lean` — the `FiniteOrderEnvelope` growth predicate with full
  closure API (`const`, `add`, `sub`, `neg`, `mul`, `compAffine`, `of_sq`, polynomials,
  exponentials of polynomials) and **Hadamard's zero-free factorization at every finite order**:
  a nowhere-vanishing entire function with envelope `exp(C(1+‖z‖)^d)` equals `exp(p)` for a
  polynomial `p`.  Generalizes the corpus's order-one `exists_linear_of_ne_zero_of_growth`.
- `HTGeometry/InvolutiveReflectionQuadraticRigidity.lean` — the reflection difference-of-squares
  split, its hyperexponential normal form, the resulting order-one ADE, and the
  `sin z - z cos z` witness.
- `RHTower/FiniteZeroHadamardProduct.lean` — the divisor-carrying Hadamard product at every
  finite order: an entire function with a finite-order envelope and finitely many zeros is
  `p · exp q` with `p, q` polynomials (`finiteDivisorPoly`,
  `exists_polynomial_mul_expPolynomial_of_envelope`).
- `HTGeometry/PolynomialDriftExpansion.lean` — the shift expansion `P(y+a) - P(y)` in the base
  point, with the exact top coefficient `n · lead(P) · a` (`driftCoeff`,
  `eval_driftCoeff_expansion`, `eval_driftCoeff_pred`).
- `HTGeometry/FiniteOrderPolynomialDescent.lean` — a nonconstant polynomial dominates its argument
  (`‖w‖ ≤ R + c‖P w‖`), so finite order descends through a polynomial outer factor.
- `HTGeometry/AlgebraicOverStateFieldOrder.lean` — the differential-order bound for elements
  *algebraic over* a state field; the corpus previously required membership in it.
- `HTGeometry/ExpPolynomialRational.lean` — `G · exp T = Q` with `G, Q` nonzero polynomials forces
  the exponent `T` to be constant, by an exact polynomial degree comparison.
- `HTGeometry/OneSidedJetIndependence.lean` — **the one-sided independence criterion**: a sequence
  is algebraically independent exactly when each term is transcendental over the field generated by
  its strict successors (`algebraicIndependent_of_transcendental_tail`), plus descent of
  transcendence along a subalgebra inclusion (`transcendental_of_le_subalgebra`).
- `HTGeometry/DerivativeShadowStaircase.lean` — the jet-tail tower as a staircase: each step is a
  simple primitive extension of transcendence degree at most one, and hypertranscendence is exactly
  the all-ones staircase.
- `HTGeometry/KoszulCartanContraction.lean` — left exterior multiplication between exterior powers,
  the **Cartan identity** `ι_φ(e ∧ ω) + e ∧ ι_φ ω = φ(e)·ω`, the chain homotopy from an invertible
  coordinate, and exactness of the Koszul complex of a linear functional.
- `RHTower/UnitaryResolventOffCircle.lean` — a unitary minus a scalar off the unit circle is
  invertible, with the reverse-triangle lower bound `| |λ|-1 | ‖y‖ ≤ ‖(U-λ)y‖`.
- `RHTower/FiniteT0SchurThresholdDivergence.lean` — the telescoping test
  `t Q_n(t) = 1 - (1-t/R)^n` and the unshifted Hankel tower with a chosen finite part; no finite
  zeroth moment makes the tower PSD at all orders.
- `RHTower/SemilocalProlateControlDeformation.lean` — the second resolvent identity and the
  relative-resolvent corner splitting, in an abstract associative `ℂ`-algebra.
- `RHTower/SemilocalProlateUnitaryTransport.lean` — a scaling/grading unitary must match the first
  Jacobi coefficient of two cyclic pairs; two distinct prolate parameters force the same.
- `RHTower/EulerDivisorUltrametricStability.lean` — the max-triangle law for absolute-convergence
  abscissae (`abscissa_le_max`) and for the outer divisor exponent (`divisorExponent_le_max`), the
  two critical-ball threshold classes, the monotone `max`-preserving exponentiation, and
  ultrametric path rigidity (`constant_of_connected_of_ultrametric`).
- `RHTower/RelativeStripDivisorReflection.lean` — normal convergence and holomorphy of a
  generalized Dirichlet series on its half-plane of absolute convergence, the sparse-support and
  accumulated-variation abscissa bounds, and the divisor reflection band `1 - A ≤ Re ρ ≤ A` with its
  two threshold classes.
- `HTGeometry/CoefficientwisePowerSeriesDerivation.lean` — a derivation of the coefficient ring
  extended coefficientwise to formal power series (`coeffwiseAdd`), its Leibniz rule, the formal
  parameter as a differential constant, and the commutation of constant-term extraction with every
  jet.  This is gate item (a) of `leading-laurent-coefficient-differential-algebraicity`.
- `HTGeometry/FormalParameterRelationNormalization.lean` — removal of the common parameter power
  from a formal-parameter differential relation (`exists_normalized_relation`,
  `eval₂_of_eq_C_X_pow_mul`) and the assembled power-series descent
  (`differentialAlgebraicOver_constantCoeff_of_formalRelation`).  Gate item (b) and the
  power-series half of the assembly.
- `HTGeometry/LaurentCoefficientwiseDerivation.lean` — the coefficientwise derivation on
  `LaurentSeries K = HahnSeries ℤ K`: `laurentCoeffwise`, the Leibniz rule proved by summing both
  product terms over **one** Hahn antidiagonal (`HahnSeries.coeff_mul_left'`/`coeff_mul_right'`
  applied with the original supports, since a coefficientwise derivative has smaller support),
  every monomial `E^m` a differential constant, restriction to the power-series derivation, and the
  jet shift `D^j F = E^{ord F} · D^j (powerSeriesPart F)`.
- `HTGeometry/LeadingLaurentCoefficientDescent.lean` — the degreewise **parameter rescaling** of a
  differential relation (`parameterRescale`, `coeff_parameterRescale`, `parameterRescale_ne_zero`)
  and the identity `ofPowerSeries_eval₂_parameterRescale` showing that substituting `E^m · v i` for
  the variables is, up to one fixed power `E^c`, evaluation of the rescaled relation at `v` — with
  `k(d) = c + m·deg(d)` realizable in `ℕ` for either sign of `m`.  Gives
  `differentialAlgebraicOver_leadingCoeff_of_laurentRelation` and its contrapositive.
- `HTGeometry/PrimeSideOrthogonality.lean` — the torus/compact-form uniqueness wrapper: the
  tensor-duality involution on the weight lattice is negation, the Cartan involution on the unit
  torus is inversion, and a scaled inversion `g ↦ c·g⁻¹` is a homomorphism only for `c = 1` — hence
  the FE involution is not a torus automorphism and differs from the prime-side polarization.
  Includes the `p`-adic Morita coboundary-class step.
- `HTGeometry/SeamFirewall.lean` — the CC class as an actual invariant (`orbitDegreeHom`), the
  finite-place block inside its kernel, the archimedean class of degree one outside it, and hence the
  **generator-level firewall** `archimedeanDivisor ∉ primeBlock`; plus the Door-5 calibration that the
  distinction collapses when every place is a coboundary.  Uses no `ω`.
- `RHTower/ArchimedeanPrimeCrossTerm.lean` — the FE-conspiracy cocycle `ρ_∞·ρ_ζ = 1`, the exact
  purely-archimedean form `χ(s) = π^{s−1/2}Γ((1−s)/2)/Γ(s/2)`, the values `Γ_ℝ(−1) = −2π`,
  `Γ_ℝ(2) = π^{-1}`, `χ(1/2) = 1`, `χ(2) = −2π²`, and the **symbolic** non-horizontality
  (`zetaChi_not_constant`) replacing the card's numerical `∂_s log χ ≠ 0` certificate.
- `HTGeometry/AtomicMomentDeterminacy.lean` — **Mergelyan-free moment determinacy**: a summable
  atomic family whose atoms are nonzero and accumulate only at the origin is determined by its
  moments of order `≥ 1`.  The proof normalizes by a maximal-modulus atom and applies Tannery's
  theorem to the Cesàro averages; mathlib has no Mergelyan theorem and none is needed.  Includes the
  closed-unit-disc Cesàro lemmas, the difference form, and the version with one extra atom at the
  accumulation point.
- `HTGeometry/ReciprocalSeamGaugeExtraction.lean` — the seam extractor as a Laurent residue pick
  (`seamContributes_iff`: the residue occurs at exactly one term), canonical extraction
  `E_k(Xi) = T_k`, the analytic gauge law `logDeriv_evenGauge`, the gauge shift
  `2k(−1)^{k+1} a_k`, and the induced Hankel counterterm on the shifted `Q₀` tower.
- `HTGeometry/EvenSeamFinitePart.lean` — the distribution-free even-seam finite-part package: seam
  exponents are even and therefore never `-1` (no logarithm), the punctured-seam integral of a seam
  monomial is a pure power with cutoff-independent finite part `1/(a+1)`, the contrasting logarithm
  at the excluded exponent, the `t = ε u` scaling law that gives cutoff independence, and the Hankel
  rearrangement of a convolution-only functional.
- `HTGeometry/SimplexTestSet.lean` — **not in mathlib**: the nonnegative integer simplex
  `{m : Σ mᵢ ≤ T}` is a test set for polynomials of total degree `≤ T`
  (`eq_zero_of_eval_natCast_eq_zero_on_simplex`), with the contrapositive and the
  monomial-coefficient-independence form.  mathlib carries only the *box* (Combinatorial
  Nullstellensatz) version; the simplex version is what any `‖m‖₁ ≤ d` exponent index set needs.
  Proof: induction on the number of variables via `MvPolynomial.finSuccEquiv`, using
  `totalDegree_coeff_finSuccEquiv_add_le` and a univariate root count.
- `RHTower/FriableCoefficientSurjectivity.lean` — the friable simplex index set, the edge-coefficient
  rows, their linear independence, and **surjectivity of the coefficient map** by finite-dimensional
  duality (`LinearMap.dualMap_injective_iff`), plus the weighted and no-soft-spot forms.
- `RHTower/FriableEdgeCoefficients.lean` — the multinomial collection of `(Σ_p m_p log p)^T` and the
  edge identity with the coefficients `C_a` isolated, plus `𝒜_{S,d}` as a `ℂ`-submodule.
- `HTGeometry/SourceOddLowAritySuccessorOrbits.lean` — the full orbit classification of fully
  supported source-odd binary forms: arities two, three and four are single orbits, and the quintic
  cross invariant is **complete** (`sourceProjectivelyEquivalentOddQuintic_iff_cross_invariant`),
  giving infinitely many quintic orbits.
- `HTGeometry/DSSOrbitEdgeOrthogonality.lean` — the `s = 1` edge form of a friable auxiliary, its
  nonvanishing from unique factorization, the **failure of any uniform lower bound**
  (`not_exists_uniform_edge_lower_bound`, from the rank-two prime-log density), the height blow-up
  along a small-edge family, and unboundedness above.  This is the orbit ⊥ edge separation.
- `HTGeometry/F1TwoFaceCriterion.lean` — the two-face `F₁` datum (`PlaceDatum`), its flow-imbalance
  (orbit degree) and corank (rational rank of the value group) faces, the `SingleFrobenius`
  necessity theorems, the `F_q` and `ℚ` calibrations, and the four-way orthogonality realization.
- `RHTower/ZeroEstimateUniformity.lean` — the diagonal pullback of a Bohr polynomial
  (`diagonalFrequency`, `injective_diagonalFrequency`, `cpow_neg_eq_exp_mul_diagonalFrequency`), the
  uniform order bound with constant one, the `S`-free Vandermonde determinant product size estimate
  (`prod_inv_primeLogHeight_le_abs_det_vandermonde`), the `P_S`-polynomial height and form bounds at
  fixed degree (`primeLogHeight_le_pow`, `inv_pow_le_abs_primeLogForm`), the stars-and-bars monomial
  count `C(|S|+d,d)` (`card_boundedDegreeMonomials_le`), and the PNT link
  (`eventually_nth_prime_le_two_mul`, `eventually_nth_prime_le_sq`) built on the in-tree
  `nth_prime_asymp`.
- `RHTower/DirichletMonomialIndependence.lean` — the **triviality lemma for Dirichlet polynomials**:
  a finite combination of `n^{-t}` vanishing at every real exponent has all coefficients zero
  (`coeff_eq_zero_of_dirichletSum_eq_zero`), hence the family `n ↦ (s ↦ n^{-s})` over the positive
  integers is linearly independent over `ℂ` (`linearIndependent_dirichletMonomial`).  Smallest-modulus
  rescaling argument; only real exponents are needed.
- `HTGeometry/PureFibreExteriorOccupation.lean` — the exterior occupation dictionary: occupation
  states are the standard index set `Set.powersetCard` of the exterior-power basis, horizon exchange
  is particle–hole complementation (an involution), the pure critical fibre itself indexes a basis of
  `⋀^m K^L`, and the rank of that exterior power is the critical binomial multiplicity.
- `HTGeometry/InvolutionIdempotentHost.lean` — self-inverse elements ↔ idempotents over a
  commutative ring with `2` invertible.
- `HTGeometry/ScalarMonodromyAlgebraicIndependence.lean` — unbounded scalar monodromy forces
  transcendence over a fixed subalgebra.
- `HTGeometry/WickInteractionMatroidLabels.lean` — **`contract_eRk_add_eRk_eq`, the relative-rank
  law for matroid contraction (a mathlib gap)**, plus the labeled algebraic matroid layer.
- `RHTower/OneSidedCompressionUnbounded.lean` — diagonal inner products of a bounded operator are
  bounded by the operator norm; `ℓ²(ℕ)` basis layer.
- `RHTower/ShiftedTowerTailClasses.lean` — exponential-scale summability comparison and three
  separated weight classes.
- `RHTower/ShiftedEulerPrimeOrbitPF2.lean` — shifted local Euler orbit, its generating identity,
  and its negative order-two Toeplitz minor.
- `RHTower/ThetaAnalyticRealDefectKernel.lean` — the analytic/real defect comparison and its exact
  RH equivalence (uses `SlabMassSquareCertificate.riemannHypothesis_iff_xiC_zero_im_eq_zero`).
- `RHTower/DiscriminantCrossPositiveInterval.lean` — exact root interval of the degree-one
  discriminant cross term and its universal scale bound.
- `RHTower/FiniteDegreeReciprocalPerturbation.lean` — **coercive Hermitian perturbation stability**
  (`posDef_add_of_coercive`) and the conjugate-pair reciprocal blindness theorem.
- `RHTower/ReciprocalSeamZerothMoment.lean` — reciprocal seam atoms, absolute convergence of every
  positive-order moment, divergence of the zeroth, and the `Infinite XiZeroCopy` instance.
- `RHTower/RealSourceMicrolocalQuartet.lean` — real even quartet polynomial, its exact zero set,
  and the point-supported distribution whose Laplace transform it is.
- `HTGeometry/EvenFrequencySeamMoments.lean` — the whole seam-moment layer of the FE-even frequency
  family: closed form `T_k = (-1)^(k+1) M_k/(2k-1)!`, half-turn repair, sign alternation, the
  measure-level positive cone, finite signed atoms, bounded packets against the sharp threshold
  `(17 + 2√70)/3`, and polynomial coefficient multipliers. Builds on the pre-existing
  `HTGeometry/SingleEvenFrequency.lean`.
- `HTGeometry/ContractionCompressionExhaustion.lean` — dense compression exhaustion for a bounded
  operator, and the rank-one finite-depth blindness witness.
- `RHTower/MonomialTailGateBound.lean` — coercivity is bounded by every diagonal entry; the shifted
  Hankel gate decays like `R^(2d)`.
- `RHTower/LoewnerCongruenceNormalization.lean` — **Sylvester congruence invariance for complex
  Hermitian matrices** (`posSemidef_congruence_iff`, `posDef_congruence_iff`,
  `negativeSubspace_congruence`) and the relative-contraction normalization.
- `RHTower/PositiveJetHorizonLevelBlindness.lean` — the `ξ - ξ(2)` countermodel: same positive
  jets, same functional equation, same Schwarz reality, same growth envelope, off-line zero.
- `RHTower/SummationGraphDenseCollapse.lean` — the finite summation graph in `ℓ² ⊕ ℂ` has trivial
  orthogonal complement, so its closure is everything; includes `ellTwo_const_eq_zero`.
- `RHTower/FixedRankHankelNonStieltjes.lean` — the exact quadratic-form split of a signed-atom
  shifted Hankel block, the **explicit Lagrange-budget threshold** `ε = 1/(1 + Σ L_j(1)²)` that
  replaces the eigenvalue/compactness step, and the node-polynomial failure vector.
- `RHTower/BoundaryWeylThresholdNonMonotone.lean` — dual-vector extraction from non-proportional
  functionals, the realizing positive definite bulk form, and the variational Schur threshold.
- `RHTower/PoleBudgetUvarovNoGo.lean` — the one-negative-square pole-budget form, its positive
  completion, the invisible negative direction, and the degree-one evaluation-functional layer.
- `HTGeometry/BoundaryKernelSchurSplit.lean` — **the coordinate-free rank-one Schur split.**
  `exists_kernelRiesz` builds the `ker β`-representative of any vector from kernel positive
  definiteness alone (orthogonal projection ∘ operator, injective hence surjective in finite
  dimension); `repairedForm_split` is the exact congruence transport
  `H[v] = A[v - (βv)(q - w)] + ‖βv‖²(A q + t - A w)`; `repairedForm_pos_iff` /
  `repairedForm_nonneg_iff` are the scalar Schur criteria; `shadow_scalar_not_faithful` is the
  positive-scalar/negative-kernel countermodel on `ℂ²`.
- `HTGeometry/StieltjesExteriorChristoffelMonotone.lean` — **zero location for Stieltjes moment
  bulks** (`ShiftedPositiveAt`, `shiftedPositiveAt_of_measure`, `monicOrtho_root_ge`) and the
  resulting exterior monotonicity of the Christoffel–Darboux diagonal and of the Christoffel
  function (`cdKernel_diag_strictAntiOn`, `christoffel_strictMonoOn`).  The monotonicity proof is
  purely algebraic — the node product, not the logarithmic derivative.
- `RHTower/ReciprocalAtomTestSpaceClosure.lean` — **the whole reciprocal-atom test layer on the
  actual `xi` divisor**: the folded atom set `Y`, the compact test set `K = Y ∪ {0}`
  (`isCompact_xiReciprocalTestSet`), isolatedness of every nonzero point, the conjugation-symmetric
  isolator and its continuity on `K`, the form `xiQZero`, its uniform-norm modulus
  (`norm_xiQZero_sub_le`), transfer of positivity to uniform limits, and the atom-visibility
  criterion equivalent to RH.  This is the reusable base for the whole `Q₀` card family.
- `RHTower/ReciprocalAtomCounterterm.lean` — folded atom multiplicities (`xiAtomMultiplicity`,
  finite fibers, conjugate equality), the exact isolator readings `M_a a ζ²` and `2 M_a Re(a ζ²)`,
  and the counterterm layer: finite-rank kernel visibility, atom locality, the local domination
  thresholds, the zero-fed rank-one countermodel, and the vanishing-point-mass criterion.
- `RHTower/ReciprocalAtomPolynomialApproximation.lean` — **an elementary replacement for Mergelyan
  on the reciprocal test set.**  `exists_realPolynomial_atomIsolator_approx` builds, for any atom
  and any prescribed vanishing order at the hard edge, a real polynomial approximating the
  conjugation-symmetric isolator uniformly on `Y`: Lagrange basis over the finitely many test
  points of norm `≥ ‖a‖/2`, times `(z/a)^N`, coefficientwise symmetrized.  On top of it:
  `riemannHypothesis_iff_forall_polynomial_xiQZero_nonneg`, the hard-edge counterterm theorem,
  the preconditioner/filter visibility dichotomy, the finite-boundary-ideal equivalence, and
  the unconditional first-trivial-zero pre-gate (`-4/25` is not an atom).
  `xiQZero_polynomialTest_eq_hankel` identifies `Q₀[p]` with the shifted-moment Hankel form.
- `RHTower/FiniteProbeRHNonselection.lean` — **the even-polynomial perturbation sector of `ΞC`.**
  `xiPerturbed R t = ΞC t + R(t²)` with parity, Schwarz reality, entirety, the inherited order-one
  envelope, and the seam-jet divisibility clause.  Two reusable algebraic engines:
  `exists_indep_pair_of_finiteCodim` (a finite-codimension subspace of `ℝ[X]` still meets
  `Xᴺ⁺¹ℝ[X]` in a 2-dimensional slice) and `exists_nonreal_spanning` (**an algebraic replacement
  for the open mapping theorem**: two `ℝ`-independent real polynomials span `ℂ` over `ℝ` at some
  non-real point, proved by the shifted Wronskian vanishing identically).  Consequences: finite
  linear probes, finite-codimension landscape slices, prescribed seam jets, and finite-type source
  functors all fail to select RH.
- `HTGeometry/ShiftedHankelStrictPositivity.lean` — the shifted Hankel quadratic form of a measure
  as a weighted square integral, and strict positive definiteness of every finite block from
  `d+1` charged positive points (with the singular-block contrapositive).
- `RHTower/SeamJetFunctionComplete.lean` — holomorphic germs with equal Taylor coefficients agree
  (`eventuallyEq_of_iteratedDeriv_eq`), entire functions agreeing near a point are equal
  (`entire_eq_of_eventuallyEq`), and the all-order seam-log jet determines an even entire function
  up to its central scalar, hence determines its zero divisor.  Also `triangular_determines`:
  a triangular coordinate change over the seam-log coefficients is invertible.
- `RHTower/SeamWeldIdentity.lean` — `Ξ' w / (w Ξ w) = 2 logDeriv Φ (w²)` for `Ξ w = Φ (w²)`, its
  holomorphic extension across the seam, and the odd-to-even tower division.
- `RHTower/SeamSquareTestNotAdmissible.lean` — the coefficient reversal `seamRevPoly`, the exact
  hard-edge exponent of the reciprocal-seam square test, its non-interval-integrability across the
  seam, and its exactly polynomial decay at infinity.
- `RHTower/CountableWindowBasis.lean` — rational windows isolate the points of any discrete set, so
  a countable window family detects all off-seam divisor mass.
- `RHTower/DeterminantLineDivisorBlindness.lean` — polynomial sections of the trivial line realize
  any prescribed finite divisor; nowhere-zero homotopies already contain the nonvanishing claim;
  signed crossing counts cancel.
- `RHTower/AcyclicFiniteFibersDerivedLimit.lean` — `lim` and `lim¹` of a tower as kernel/cokernel of
  shift-minus-identity, their vanishing on towers of zero objects, and contractibility of the
  specialized finite prime complexes in the strip.
- `RHTower/TranslationInvariantDefectForm.lean` — a translation-invariant Hermitian form pairs only
  conjugate frequencies, off-real orbits are isotropic, and each such orbit is a hyperbolic plane.
- `RHTower/HurwitzScalarComparisonNoGo.lean` — the exponential seam defect `q(1-s) - q(conj s)`
  vanishes along the critical line and has nonzero transverse slope, so it is not a continuous
  scalar multiple of any holomorphic germ vanishing there.

## Triage of the remaining folder (2026-08-16 scan)

**Warning learned the hard way:** "no open gate box" does *not* mean "formalized". Several such
cards (e.g. `zeta-summation-constraint-graph-dense-collapse`) named a Lean module that proved only
one auxiliary lemma. Always compare the card's numbered statements against the module's actual
declaration list before promoting.

- 131 cards have open gate boxes that are **only** Lean/formalization boxes — these are the
  highest-yield targets. Many say "optional finite-dimensional theorem".
- 75 cards carry no open box at all (status must be read from prose).
- 11 cards already name a Lean declaration but still have an open Lean box.

Known heavy prerequisites still outstanding, with the cards they gate:

- ~~entire-function **order** — needed by the `finite-*-rh-nonselection` family.~~  **Resolved
  2026-08-16 without an order lower bound**: the perturbation differs from `ξ` by a polynomial, so
  it carries exactly the corpus envelope `XiC_order`; the whole family is now stage 3.
- ~~Newton's inequalities for elementary symmetric functions~~ — **built 2026-08-16**
  (`HTGeometry/NewtonInequalities.lean`); `pa9-turan-newton-floor` is closed at stage 3.
- ~~Hölder + a reflection-stable meromorphic carrier — `gamma-reflection-clock-observable-split`.~~
  **Resolved 2026-08-17**: the right carrier is the *global* meromorphic field `meroField Set.univ`,
  which the corpus already equips with the reflection automorphism `complexReflectionMeroEquiv`,
  with Euler reflection (`gammaNegativeShiftMero_reflection`) and with the signed-Gamma-product
  form of Hölder (`hypertranscendentalOver_gammaOrbitProductMero`).  No algebraic-extension step
  and no log-derivative detour are needed: `R·P = Γ²` reduces the whole card to the one-orbit case
  of that product theorem.  The card is stage 3.

## Triage snapshot

- 83 cards carry no open gate box at all (status must be read from the prose).
- 165 cards mention at least one Lean module that already exists in `formal/`.
- 330 cards mention no Lean module at all.
- `HTGeometry/ComplexExponentialPolynomial.lean` — **entire exponential polynomials with complex
  frequencies** (mathlib gap).  `cexpFn c P z = ∑ⱼ Pⱼ(z) e^{cⱼ z}` is entire
  (`differentiable_cexpFn`), has finite exponential type with an explicit constant pair
  (`exists_exponentialType_bound`, built on the reusable `norm_eval_le` and
  `one_add_norm_pow_le_exp`), and is not identically zero when the frequencies are distinct and the
  blocks nonzero (`eq_zero_of_cexpFn_eq_zero`, `exists_cexpFn_ne_zero`) — proved algebraically by
  the block-killing induction `cexpFn_shift` / `cexpFn_eq_zero_iterate` / `cshiftD_iterate_ne_zero`,
  which replaces Rolle in the complex-frequency regime.  Combined with the corpus Jensen count this
  gives `exists_zeroCount_linear`: the number of *distinct* zeros in a disc of radius `r` is at
  most `K(1 + r)`.  Also `negComp` (variable reflection) with its degree and nonvanishing lemmas.
- `HTGeometry/PrimeValuationLeadingEchelonInfinite.lean` — **the leading-echelon law with only
  infinitely many nonzero private coefficients**
  (`primeValuationLeadingEchelonJets_algebraicIndependent_of_infinitePrimeDependent`,
  `primeValuationLeadingEchelon_differentialIndependent_of_infinitePrimeDependent`).  The original
  law needs the private prime coefficient nonzero at *every* prime, which any nontrivial filter can
  destroy.  The weakening rests on `finite_setOf_clockPoly_eq_zero`: a nonzero polynomial in the
  injective rotated prime clock vanishes at only finitely many primes, so tail independence — a
  statement modulo finite support — survives a weight that is merely nonzero infinitely often.
  Reusable for every "the source survives after filtering" argument.
- `HTGeometry/ExponentialPolynomialZeroBound.lean` (extended) — the zero bound now also covers
  vanishing blocks (`card_lt_of_expPoly_eq_zero'`) and **complex** polynomial coefficients with real
  frequencies (`cexpPoly`, `card_lt_of_cexpPoly_eq_zero`), via the coefficientwise real/imaginary
  parts `rePoly`/`imPoly` and their evaluation, degree and joint-vanishing lemmas.
- `RHTower/PrimeSourceCancellationBudget.lean` — the filter calculus itself:
  `filterSymbol`, the filtered coefficient law `filterAction`, the summability transfer
  `lseriesSummable_filterSymbol`, the finite-abscissa threshold `filterAbscissa` /
  `filteredSource_finiteAbscissa`, the cofinite prime-log uniqueness theorem
  `eq_zero_of_exponentialType_of_cofinite_primeLog_zeros`, and the source-survival theorem
  `infinite_survivingPrimes`.  Any card about applying a finite differential-translation operator
  to a Dirichlet source can start from these.
- `HTGeometry/CommonLayerPrimeJetIndependence.lean` — **algebraic independence from a common
  valuation layer** (`commonLayerJetRectangle_algebraicIndependent`).  The leading-echelon law
  separates sources by private valuation coordinates; translates and jets of a *single* source have
  none.  What separates them is the first-layer feature family
  `p ↦ g(p) · (rotated prime clock at p)^k`, and its tail independence is exactly the input the
  prime-ray Jacobian criterion needs at a constant layer exponent.  Higher layers stay arbitrary.
- `RHTower/PrimeShiftJetIndependence.lean` — the **prime-feature tail-span law** for arbitrary
  distinct complex shifts (`primeShiftJet_tailCoefficientIndependent`), obtained from the
  exponential-polynomial prime-log sampling stack; its consequences
  `dirichletShiftFamily_differentialIndependent` (over `ℂ`, formal) and
  `dirichletShiftFamily_upperEnd_differentialIndependent` (over the rational coordinate field, for
  the actual meromorphic carriers), and the xi instance
  `filteredVonMangoldt_translates_differentialIndependent`.
- `HTGeometry/EntireMultiplierDefectUniversality.lean` — the entire-multiplier defect toolkit:
  membership in a multiplier ideal as an analytic-order condition (`mem_multiplierIdeal_iff`), the
  nowhere-zero translation multiplier and its descent to the defect
  (`translation_mem_multiplierIdeal_iff`), the local character with its unipotent correction
  (`translationMultiplier_sub_character`), and the classification of faithful positive
  translation-invariant Hermitian forms on a finite character core
  (`nonempty_positiveInvariantForm_iff`: such a form exists exactly when every point is real).

## Open build: the Nevanlinna small-growth field `F_s`

Eight stage-2 cards state their conclusion over Nagoshi's field `F_s` of meromorphic functions with
`T(r, φ) = o(r)`: `prime-power-dirichlet-complex-jet-independence`,
`atomic-increment-full-orbit-codimension-law`, `da-gauge-ht-divisor-blindness`,
`entire-composition-hypertranscendence-or-law`, `exact-rational-rg-generation-dichotomy`,
`exponential-tower-exact-differential-order`, `finite-order-symmetry-ht-rational-gauge-blindness`,
`prime-poisson-superselection-screen`.

State of the build:

- mathlib supplies `ValueDistribution.characteristic`, the first main theorem, and the sum/product
  characteristic bounds, so `F_s` as a **field** is reachable directly.
- `F_s` as a **differential** field additionally needs the lemma on the logarithmic derivative,
  `m(r, f'/f) = O(log r + log T(r,f))` off a finite-measure exceptional set.  Mathlib does not have
  it; the corpus's `SecondMainTheoremChain` stops exactly there, and the corpus already owns Borel's
  growth lemma (`HTGeometry.BorelGrowthLemma.borel_growth`) and the Jensen/Herglotz–Riesz kernel
  machinery that a Poisson–Jensen derivation needs.
- The Chiang–Feng coefficient-separation lemma (ordinary Dirichlet series are independent over
  `F_s`) reduces to Borel's theorem for exponential sums with small-growth coefficients, which in
  turn uses the logarithmic-derivative lemma.  So the logarithmic-derivative lemma is the single
  keystone for the whole cluster.

For `prime-power-dirichlet-complex-jet-independence` everything except the `F_s` upgrade is already
formalized: the tail-span lemma, the constant-coefficient algebraic independence of every finite
rectangle of complex translates and derivative jets, the analytic transfer to the actual carriers,
and the xi instance.

### Nevanlinna keystone: build log

- `HTGeometry/PoissonInteriorLogKernel.lean` — the Poisson average of `log ‖· − ρ‖` for `ρ`
  anywhere in the closed disc.  Mathlib only computes it for `ρ` on the boundary circle; the
  interior case needs the Blaschke-corrected kernel
  `innerLogKernel c ρ R z = (R² − conj(ρ−c)(z−c))/R`, whose modulus on the boundary is exactly
  `‖z − ρ‖` and which is analytic and nowhere zero on a neighbourhood of the closed disc.  Hence
  `circleAverage ((re ∘ herglotzRieszKernel c w) • log ‖· − ρ‖) c R = log ‖innerLogKernel c ρ R w‖`
  for every `ρ` in the closed disc
  (`circleAverage_re_herglotzRieszKernel_mul_log_of_mem_closedBall`).
- `HTGeometry/PoissonJensenFormula.lean` — the **Poisson–Jensen formula** (`poissonJensen`):
  for `f` meromorphic and not identically zero on a closed disc and `w` interior,
  `circleAverage ((re ∘ herglotzRieszKernel c w) • log ‖f‖) c R
     = ∑ᶠ u, divisor f u · log ‖innerLogKernel c u R w‖ + log ‖g w‖`,
  together with the divisor decomposition `log ‖f‖ = ∑ᶠ u, divisor f u · log ‖· − u‖ + log ‖g‖`
  that produced it.  Also `continuousOn_re_herglotzRieszKernel`.

- `HTGeometry/HerglotzTransformKernel.lean` — the Herglotz transform `herglotzTransform c R v w`
  (the analytic completion of the Poisson integral of a boundary function), the differentiated
  kernel `herglotzDerivKernel c w z = 2(z − c)/(z − w)²` with
  `hasDerivAt_herglotzRieszKernel`, the modulus bound `norm_herglotzDerivKernel_le`
  (`≤ 2R/δ²` once the circle keeps distance `δ` from `w`), and the uniform geometry
  `le_norm_circleMap_sub` / `circleMap_ne_of_mem_ball` on a small ball around an interior point.
  These are exactly the hypotheses needed to differentiate the transform under the integral sign.

  Now also carries the analytic half of the estimate:
  `hasDerivAt_herglotzTransform` (differentiation under the integral, via mathlib's
  `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the bound above),
  `re_herglotzTransform` (the real part is the Poisson integral),
  `deriv_eq_zero_of_re_eq_zero` (open-mapping rigidity),
  `exists_analytic_log` (a zero-free analytic function on a ball is `exp` of an analytic function
  whose derivative is its logarithmic derivative — built from Morera's theorem for a disc), and the
  capstone

  `logDeriv_eq_circleAverage_of_ne_zero` :
    for `g` analytic and zero-free on the closed disc and `w` interior,
    `g'(w)/g(w) = circleAverage (2(z − c)/(z − w)² · log ‖g z‖) c R`.

  This is the boundary-integral representation of the logarithmic derivative that Nevanlinna's
  estimate rests on: combined with `norm_herglotzDerivKernel_le` it already gives the classical
  pointwise bound `|g'/g| ≤ 2R/(R − r)² · circleAverage |log ‖g‖|`.

  The divisor half of the transport is now proved as well:
  `hasDerivAt_innerLogKernel`, `logDeriv_innerLogKernel`, and

  `circleAverage_herglotzDerivKernel_log_norm_sub` :
    for an interior divisor point `u`,
    `circleAverage (2(z − c)/(z − w)² · log ‖z − u‖) c R
       = −conj(u − c)/(R² − conj(u − c)(w − c))`.

  The proof reuses the capstone: on the boundary circle `log ‖z − u‖` *is* `log ‖innerLogKernel‖`,
  and for interior `u` that kernel is analytic and zero-free on the whole closed disc, so its
  logarithmic derivative is exactly the Blaschke term.

Remaining for the logarithmic-derivative lemma: assemble the two halves over the finite divisor
(the same finsum-to-Finset linearity already used in `poissonJensen`), extend the divisor-term
computation to points on the boundary circle, the circle estimate for `log⁺(1/‖Re^{iθ} − a‖)`, and
the exceptional-set removal through `HTGeometry.BorelGrowthLemma.borel_growth`.

Note: rechecking the eight cards showed only three genuinely need Nagoshi's field —
`prime-power-dirichlet-complex-jet-independence`, `atomic-increment-full-orbit-codimension-law`
and `da-gauge-ht-divisor-blindness` (the ξ specialization in the last).  In
`exact-rational-rg-generation-dichotomy` and `prime-poisson-superselection-screen` the symbol
`F_s` denotes something else entirely, and the remaining three need Nevanlinna *estimates*
(Steinmetz reduction, Pólya growth-depth, product inequalities) rather than the small-growth
field.

### `RHTower/PrimeZeroSusceptibility.lean` — reusable pieces

Built for `prime-zero-susceptibility-transverse` (now stage 3):

- `exists_zeroBranch_hasDerivAt` — mathlib's curried bivariate implicit function theorem applied to
  `(ε, s) ↦ ζ(s) + ε·n^{-s}`, giving the analytic zero branch and `dρ/dε = −n^{-ρ}/ζ'(ρ)`.  The
  supporting `continuousAt_deriv_riemannZeta` and `isInvertible_smulRight` are reusable.
- `eventually_exists_perturbedZero` — existence of a perturbed zero in any prescribed neighbourhood,
  from the **open mapping theorem** applied to `f/h` rather than from Rouché.  This is the cheap
  substitute for Rouché whenever only existence (not the zero count) is needed.
- `tendsto_multiplicitySplit` — the Puiseux limit law `(s − ρ)^m/ε → −h(ρ)/G(ρ)`, with no
  simplicity hypothesis.
- `chiFE`, `riemannZeta_one_sub_chiFE`, `eventually_mirror_factorization`,
  `norm_mirror_leadingCoeff` — the functional-equation multiplier and the mirror factorization: a
  zero and its functional-equation mirror have the same multiplicity, with leading coefficients
  related by `(−1)^m χ(ρ)`.
- `rpow_frequency_independent_iff`, `mirrorRatio_frequency_independent_iff` — a power `n^{1−2β}`
  (times any nonzero frequency-independent factor) is independent of `n ≥ 2` exactly when `β = ½`.


### `exponential-tower-exact-differential-order` — half closed (2026-08-18)

The differential-order half `ord_DA(F_n) = n` is **done**, unconditionally and for arbitrary complex
parameters: `HTGeometry/AffineExponentialCascadeOrder.lean`.  The route is not the card's (real-axis
domination + triangular Jacobian + logarithmic velocities) but a reduction: composing the affine
layer of one map with the exponential of the next turns a cascade of `w ↦ a_j + b_j exp(c_j w)` into
*one* affine map applied to a cascade of `w ↦ exp(α w + β)`, and the corpus already owns
`exactDifferentialOrder_expAffineCascade` for the latter.  The only missing input was invariance of
exact order under affine **post**composition (`exactDifferentialOrder_const_mul_add_iff`), which is
unconditional.

The composition-depth half `cd_+(F_n) = n` is open.  New infrastructure landed for it:

- `HTGeometry/IteratedExponentialGrowthHeight.lean` — `iterExp`, `GrowthHeightAtLeast`,
  `GrowthHeightAtMost`, `PositiveLowerOrder` (liminf-free), and their incompatibility one step apart.
- `HTGeometry/AffineExponentialCascadeGrowth.lean` — the two absorption lemmas on the
  iterated-exponential scale and the upper bound `M(r,F_n) ≤ exp_n(r^C)`, hence
  `not_growthHeightAtLeast_affExpCascade`.

**The one gate left** is a *quantitative* minimum-modulus floor.  `RHTower/EntireMinimumModulus`
already builds one — inside its proof, `L = ‖g 0‖·exp(−2 log(M/‖g 0‖)·B/(R−B))` — but only exports
`0 < L`.  Exposing the classical `min_{|w|=s}|f| ≥ M(R',f)^{−C}` form would immediately give the
Pólya growth-depth lemma through the already-owned
`HTGeometry/PolyaConnectedTransfer.exists_le_norm_comp_of_floor`, and with it the composition-depth
half of this card and of `asymptotically-exponential-algebraic-cascade-unit-cost`.

## Sweep 2026-08-21

Folder size at start of this pass: **262** top-level cards.

| Date | Card | Lean module(s) |
|---|---|---|
| 2026-08-21 | `joint-hurwitz-exponent-half-plane-removal` | `Hurwitz/ContinuedJointUpperEndDifferentialIndependence.lean` (pre-existing, unrestricted) + new `HTGeometry/DerivativeTailDifferentialIndependence.lean` |
| 2026-08-21 | `polarization-transport-component-collapse` | `HTGeometry/WedgeRealization.lean` (pre-existing seed) + new `HTGeometry/PolarizationTransportComponentCollapse.lean` (general law) |
| 2026-08-21 | `euler-dirichlet-laurent-residue-double` | `RHTower/EulerLaurentResidueDouble.lean` (pre-existing) + new `RHTower/EulerCharacterGroupCompletion.lean` |

### New reusable infrastructure (2026-08-21)

- `HTGeometry/DerivativeTailDifferentialIndependence.lean` — **the derivative-tail law**
  `differentialIndependent_of_jetShift`: for a finite nonempty index type, if
  `fun j => differentialJet (m j) (x j)` is differentially independent over `F`, then so is `x`.
  Proved by the dtrdeg count inside `F⟨x⟩` using `differentialIndependent_of_spanning_of_cardinalMk_le`
  and `cardinalMk_le_differentialTranscendenceDegree`.  Also
  `injective_of_differentialIndependent_jetShift` and `differentialIndependent_coe_of_subfield`
  (the converse of `differentialIndependent_subfield`).  Use this whenever an independence
  certificate is available only after differentiating.
- `HTGeometry/PolarizationTransportComponentCollapse.lean` — `ConstraintComplex` + its `1`-skeleton,
  `CompatibleOrientation`, `compatibleOrientationEquivComponents` (compatible Boolean orientations
  ≃ functions on `π₀`), `compatibleOrientationEquivBool`, `uniquePointedCompatibleOrientation`, and
  the one-dimensional-form isometry sign law `sameSign_of_isometryScalar` over any linearly ordered
  field.
- `RHTower/EulerCharacterGroupCompletion.lean` — `EulerCharGroup` (= `ℚ_{>0}^×`) with
  `closure_natRange_eq_top` (group completion of the Dirichlet monoid) and
  `closure_primeRange_eq_top` (prime-exponent lattice); the character map `eulerRatCharacter` with
  multiplicativity, reflection-inverts-characters and injectivity; and the group algebra
  `ℂ[ℚ_{>0}^×]` with the scale derivation `scaleDeriv` (Leibniz: `scaleDeriv_mul`), the
  constant-term functional (`constantTerm_scaleDeriv : CT ∘ D = 0`) and the residue pairing
  (`residuePairing_single/_swap/_natMode_eq_zero/_opposite_ne_zero`).  Reusable for any
  "constant-term residue seam of a character algebra" argument.
| 2026-08-21 | `self-dual-quartet-defeats-generic-shift-curvature-bound` | new `RHTower/SelfDualQuartetShiftCurvature.lean` |
| 2026-08-21 | `anti-causal-cauchy-trace-unique-phase-noncancellation` | new `RHTower/WeightedAntiCausalCauchyTrace.lean` |
| 2026-08-21 | `shifted-euler-quotient-twisted-cocycle-flatness` | new `RHTower/ShiftedEulerQuotientCocycleFlatness.lean` |

### More reusable infrastructure (2026-08-21)

- `RHTower/SelfDualQuartetShiftCurvature.lean` — the degree-four self-dual counterexample family
  with its functional equation, Schwarz symmetry, exact zero set, strip geometry, boundary
  unimodularity (`norm_selfDualShiftRatio_eq_one`), full-shift cocycle, residue profile
  `4e^{-at}cos(γt)` and exact corner energy `4/a + 4a/(a²+γ²)` (`> 8`, `→ ∞` as `a → 0⁺`).
- `RHTower/WeightedAntiCausalCauchyTrace.lean` — **the `t^α`-weighted off-line Cauchy Gram law**
  `weightedOfflineEnergy_eq` (`E_α = 4Γ(α+1)∑ mⱼm_k Re[(conj zⱼ+z_k)^{-(α+1)}]`, every `α > -1`),
  the polar sign law `re_cpow_neg_ofReal` (`(w^{-c}).re = ‖w‖^{-c} cos(c·arg w)`), entrywise
  positivity at `α = 0`, an explicit negative cross entry for every `α > 0`, the single-mode floor
  `E₀ = 2m²/a > 4`, and the **Hankel first-moment identity**
  `lintegral_hankelSquare_eq_firstMoment` (`∫_{x>0}∫_{y>0} g(x+y) = ∫_{t>0} t·g(t)`) with its
  half-line translation lemma `lintegral_Ioi_add_left`.  Reuse for any weighted boundary-energy or
  Hankel Hilbert–Schmidt computation.
  Key upstream find: `GaloisForLFunctions.HTGeometry.integral_cpow_mul_exp_neg_mul_Ioi` already
  gives `∫_0^∞ t^{s-1}e^{-wt} = Γ(s)w^{-s}` for **complex** rate `Re w > 0`
  (`HTGeometry/BarnesMellinRepresentation.lean`).
- `RHTower/ShiftedEulerQuotientCocycleFlatness.lean` — the abstract shifted-quotient cocycle
  `shiftedQuotient_cocycle`, its two triple decompositions and the zero-curvature statement, plus
  the twisted Dirichlet convolution `suzukiCoeffAF_add_eq_twistedConvolution` and
  `dirichletShift_one`.  The abstract cocycle applies to *any* `F : ℂ → ℂ`.
| 2026-08-21 | `absolute-euler-paired-gauss-resolvent-autocorrelation-law` | new `HTGeometry/HalfLineExponentialPacketGram.lean` + new `RHTower/PairedCauchyLaplaceIdentities.lean` |

- `HTGeometry/HalfLineExponentialPacketGram.lean` — **the half-line Gram toolkit for finite
  exponential packets**: `halfLineExpPacket`, `integral_exp_atom_mul`, `integral_expPacket_mul`,
  `integral_conj_expPacket_mul`, `normSq_sub_re_sq`, `re_conj_mul_sub_re_mul`,
  `integral_im_sq_expPacket`, `integral_im_mul_im_expPacket`.  Use this for *any* half-line
  "Hermitian square minus bilinear square" computation; it turns such an expression into the
  half-line energy of the imaginary part of the packet.
- `RHTower/PairedCauchyLaplaceIdentities.lean` — `pairedTransform` / `pairedQuadratic` with the
  three exact laws `paired_const_law` (`8cA`), `paired_cauchyAtom_law` (`4cZ_a²+8acB_a`),
  `paired_lag_law` (`-8d∫y(x+τ)y(x)`), plus `pairedQuadratic_add` and the contact-mass law
  `pairedQuadratic_const_shift`.  These serve every `absolute-euler-paired-*` card.

### Blocker triage refresh (2026-08-21)

Cards read in this pass and the *exact* remaining obligation, so the next session does not
re-diagnose:

- `infinitesimal-euler-leakage-cauchy-energy-threshold` — the finite-profile half is already
  stage-3-certified (`RHTower/FiniteOfflineCauchyEnergy.lean`, `FiniteOfflineCauchyL2.lean`).
  What is left: **Theorem A** (`ω⁻¹ ℓ_ω → ℓ₁` from the differentiated Xi leakage quotient),
  **Theorem B** `(3)`–`(5)` (`∂_ω Θ_ω|₀ = -2ξ'/ξ`; `∂_ω c_ω(n)|₀ = 2Λ(n)`;
  `∂²_ω c_ω(n)|₀ = 4(Λ⍟Λ)(n)`; the corpus already has
  `RHTower.hasDerivAt_LSeries_suzukiShiftedCoefficient` and `LSeries_two_mul_vonMangoldt` for the
  series form), and **Theorem D** (the Toeplitz/Hankel `I - T*T = L*L` construction, which needs a
  Hardy-space `H²` compression layer).
- `absolute-euler-paired-{cumulative-critical-error-current,translation-resolvent-functional-calculus,
  normalized-screw-current-identification}` — their formalization gates are explicitly *conditional
  on an open analytic inequality*; the reusable algebra they share is now
  `RHTower/PairedCauchyLaplaceIdentities.lean`.  The translation-resolvent card additionally needs a
  half-line translation-semigroup functional calculus on `L²(ℝ₊)`.
- `noisy-binary-tree-channel-rg-clock-hypertranscendence`,
  `gadc-tree-population-rg-clock-hypertranscendence` — the exact channel algebra is in
  `HTGeometry/BetheHolographicIsingRG.lean`, but the **headline HT conclusion is not**: it needs
  hypertranscendence of the Schröder/Abel/Poincaré linearizer of a rational map (the
  Fernandes-survey theory).  *That brick is shared by both cards.*
- `thermodynamic-divisor-charge-finite-ancestor-or-boundary-index` — §1 is Lean
  (`RHTower/PrimeQuasiLocalCharge.nonzero_winding_has_finiteAncestor`); §2 needs **operator
  K-theory** (six-term exactness), absent from mathlib.
- `semilocal-prolate-extension-rank-two-ambiguity`,
  `semilocal-jacobi-linear-growth-prolate-domain-gate` — deficiency indices, von Neumann/Krein
  extension theory and half-line Jacobi orthogonal-polynomial comparison.  mathlib has no unbounded
  self-adjoint extension theory.
- `locally-infinite-repaired-frequency-source-for-compact-markov`,
  `zero-frequency-repaired-source-mellin-threshold`,
  `reservoir-density-complete-monotonicity-markov-equivalence` (+ the two other reservoir cards) —
  need **Carleman's determinacy criterion** and **Bernstein's theorem** (completely monotone ⇒
  Laplace transform).  The corpus has the *discrete* half
  (`HTGeometry/CompletelyMonotoneSampling.exists_hausdorffSource_of_completelyMonotoneDiff`).
- `first-order-autonomous-algebraic-ap-periodicity` — needs algebraic-curve normalization on a
  compact Riemann surface **plus Schwartz's minimal-set trichotomy for `C²` surface flows**
  (a Poincaré–Bendixson generalization).  Nothing of either is in mathlib.
- `first-order-composition-two-defect-decomposition`,
  `autonomous-cap-derivative-shadow-law`,
  `asymptotically-exponential-algebraic-cascade-unit-cost` — all gated on **Clunie composition
  growth**, i.e. the Nevanlinna lane.
- `drifting-periodic-primitive-ramification-exclusion` — needs the **Nevanlinna second main theorem
  with ramification** (at most two totally ramified finite values for an entire function).  The
  omitted-value case alone would follow from little Picard.
- `verified-height-one-zero-turing-extension` — the generic one-zero implication is already Lean
  (`RHTower.rhVerifiedThrough_amplify_of_increment_ncard_le_one`); the missing input is a
  **certified Turing zero count** `N(T₁) = 12363153437139`, i.e. verified interval arithmetic for
  `ζ`.  This is the one card whose obligation is a computation, not a theorem.
- `de-branges-ht-gauge-saturation` — needs Hermite–Biehler/de Branges space theory.  The corpus
  already owns the two nontrivial inputs: Hölder for `Γ` (the whole
  `HTGeometry/*Gamma*Hypertranscendence*` stack) and Weierstrass products
  (`HTGeometry/WeierstrassFactorizationTheorem.lean`), plus the finite-order rigidity half
  (`HTGeometry/FiniteOrderHadamard.exists_polynomial_exp_of_ne_zero_of_growth`).  What is missing is
  the de Branges space `H(E)` with its bounded-type conditions and the unitary gauge theorem.

**Highest-leverage bricks, in order:** (1) the Nevanlinna lemma on the logarithmic derivative
→ second main theorem → Clunie/ramification (unblocks the eight `F_s` cards plus at least four
more); (2) Bernstein + Carleman determinacy (the five reservoir cards); (3) the ADH
rational-or-hypertranscendental theorem (18 cards); (4) hypertranscendence of rational-map
linearizers (the two tree-channel cards and the Böttcher family).
| 2026-08-21 | `shifted-hardy-leakage-static-continuity-no-go` | new `HTGeometry/HardyLeakageRankOne.lean` |

- `HTGeometry/HardyLeakageRankOne.lean` — **the rank-one Hardy leakage channel**, on the corpus's
  own `H²(D)`: `blaschkeMul` / `blaschkeIsometry` / `adjoint_blaschkeMul_comp`,
  `modelSpace hb = ℂ ∙ k_β` with `orthogonal_modelSpace`,
  `starProjection_modelSpace_blaschkeMul` (`P_{K_B} T_A = b_α(β) P_{K_B}`),
  `norm_sq_adjoint_blaschkeMul` (`‖T_B^* g‖² = ‖g‖² - ‖P_{K_B}g‖²`), and the Schur defect
  `hardyLeakage_sq : ‖f‖² - ‖T_B^*(T_A f)‖² = |b_α(β)|² ‖P_{K_B} f‖²` with its rank-one and
  norm corollaries.  Plus `cayleyPoint` and `norm_blaschkeFactor_cayley` (`= ω/a`).
  **Reuse this for every `…-hardy-leakage-…` card**: the Toeplitz compression of a
  Blaschke-quotient symbol is `T_B^* T_A`, entirely internal to `H²`, so no ambient `L²(𝕋)` and no
  half-plane Hardy space is needed.
| 2026-08-21 | `sonin-relative-resolvent-sylvester-factorization` | new `RHTower/SoninSylvesterFactorization.lean` + new `HTGeometry/DisjointSpectrumIntertwiner.lean` |

- `HTGeometry/DisjointSpectrumIntertwiner.lean` — **Rosenblum for self-adjoint elements** (mathlib
  gap): `aeval_mul_eq_mul_aeval_of_intertwine`, `cfc_mul_eq_mul_cfc_of_intertwine`
  (`S X = X T ⇒ f(S) X = X f(T)` for continuous real `f`, via Weierstrass + `norm_cfc_le`), and
  `eq_zero_of_intertwine_of_disjoint_spectrum` (disjoint spectra ⇒ `X = 0`, via Urysohn).
  *Import note:* the real cfc instance needs
  `Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic` **and** `…/Instances`;
  `NormOneClass A` needs `[Nontrivial A]`.
- `RHTower/SoninSylvesterFactorization.lean` — the abstract Sonin corner algebra:
  `sonin_sylvester_factorization`, `sonin_transport`, `isCompactOperator_equiv_comp_iff`,
  `memSchattenClass_equiv_comp_iff`, `memSchattenClass_one_sylvester`, `sonin_corner_eq_zero_iff`,
  `sonin_cfc_intertwine`, `soninCross_eq_zero_of_disjoint_spectrum`.
  **Pattern worth repeating:** a card whose "hypotheses" are its own quantified operator data is
  fully formalizable as an abstract theorem — that is not a smuggled analytic assumption.

### In flight: `sonin-euler-inverse-polar-corner-noncompact`

Its **"Abstract operator lemma" (items 1–4) is now fully Lean-proved** in the new module
`HTGeometry/ProjectionCornerCommutator.lean`:

- `crossCorner Q A = (1-Q) A Q`, `upperCorner Q A = Q A (1-Q)`, `projCommutator Q A = [Q,A]`;
- `projCommutator_eq_corners`, `crossCorner_eq_neg_compression`, `upperCorner_eq_adjoint`;
- **`isCompactOperator_crossCorner_iff`** (item 1; the hard direction uses the corpus's Schauder
  theorem `HTGeometry.isCompactOperator_adjoint_rectangular`);
- `projCommutator_inv`, **`isCompactOperator_projCommutator_inv_iff`** (item 2);
- `projCommutator_mul`, `isCompactOperator_projCommutator_sq`,
  **`isCompactOperator_crossCorner_sq`** (items 3–4);
- **`not_isCompactOperator_crossCorner_inv`**, **`not_isCompactOperator_crossCorner_sqrt`** — the
  propagation form the card actually uses.

**What is left on that card:** the concrete instantiation at `W_p = M_{|1-p^{-1/2-is}|²}` on
`SoninL2`.  The parent noncompactness is already stage 3
(`RHTower.centralPositiveEulerCorner_not_isCompactOperator`, with
`crossBoundary e a = (1-e) a e` matching `crossCorner`), so what remains is: `W_p` self-adjoint,
the two-sided bound `(1-p^{-1/2})² ≤ w_p ≤ (1+p^{-1/2})²` giving a bounded inverse, the cfc square
roots, and the `θ_p`-transport of the polar corner (for which
`RHTower.isCompactOperator_equiv_comp_iff` is already available).

**Reusable elsewhere:** every "corner is/ is not compact" Sonin card can now argue through
`projCommutator`.

### Sweep continued (2026-08-21, batch 2)

**Promoted**

| Card | Modules |
|---|---|
| `sonin-euler-inverse-polar-corner-noncompact` | `HTGeometry/ProjectionCornerCommutator.lean` (+ `mixedCorner` transport), `RHTower/SoninEulerInversePolarCorner.lean` |
| `depth-three-face-signature-completeness` | `HTGeometry/DepthThreeFaceSignatureCompleteness.lean` |
| `absolute-euler-paired-translation-resolvent-functional-calculus` | `RHTower/PairedTranslationResolventCalculus.lean` |

**New reusable infrastructure**

- `HTGeometry/ProjectionCornerCommutator.lean` also gained `mixedCorner P Q A = (1-P) A Q`,
  `mixedCorner_eq_comp`, `crossCorner_eq_comp` and **`isCompactOperator_mixedCorner_iff`** —
  transport of corner compactness along a bounded isomorphism carrying `ran Q` onto `ran P`.
  Only the two range identities are used; no analytic input.
- `RHTower/SoninEulerInversePolarCorner.lean` — the concrete Euler weight `W_p` on `SoninL2`:
  self-adjointness, Neumann invertibility (`‖p^{-1/2}(D+D*)‖ ≤ 2/√p < 1+p⁻¹`), positivity of the
  real spectrum, and the cfc weights `W_p^{-1}`, `W_p^{1/2}`, `W_p^{-1/2}`.
  **Instance trap:** `ContinuousFunctionalCalculus ℝ (SoninL2 →L[ℂ] SoninL2) IsSelfAdjoint` does
  *not* resolve by instance search, but the term `IsSelfAdjoint.instContinuousFunctionalCalculus`
  elaborates.  Declare it as a `local instance` at the top of the module.
- `HTGeometry/DepthThreeFaceSignatureCompleteness.lean` — the `d = 3` instance of the all-depth
  pair-face classification, plus the multiplicative face charge `multFaceCharge` and the
  simple-pole reduction of a logarithmic-derivative face signature to order `-1`.
- `RHTower/PairedTranslationResolventCalculus.lean` — **the half-line translation-resolvent
  calculus of the exponential core**: `(4)` the resolvent of a packet is a packet, `(5)`
  `y_c' = c y_c - y`, `(6)` the exact contact identity `Z_c² + 2 c B_c = 2⟨y, R_c y⟩` (proved by
  Cauchy-kernel algebra, *not* by integration by parts, so no decay estimate is needed), `(7)` the
  Cauchy atom is `8 d ⟨y, R_c y⟩`, and the Euler-block operator algebra: geometric resolvent
  `∑_{k≥1} T^k = T(1-T)^{-1}`, Cayley form `(1+T)(1-T)^{-1} = 1 + 2T(1-T)^{-1}`, accretivity
  `Re⟨(1+T)v,(1-T)v⟩ = ‖v‖² - ‖Tv‖² ≥ 0`, and `‖p^{-1/2}S‖ < 1`.

**Heavy pile — precise remaining bricks (do not re-triage, build these)**

1. `absolute-euler-paired-cumulative-critical-error-current-law` and
   `absolute-euler-paired-normalized-screw-current-identification` both reduce to one
   *infinite-aperture* Stieltjes passage.  The clean route is **not** the card's cutoff argument:
   generalize `RHTower.criticalMellinStieltjesPairing_integrationByParts` to keep the boundary
   term (drop `hFend`, add `+ E_crit(2a) F(2a)`), then let `a → ∞`.  Needed:
   (i) that boundary-term generalization;
   (ii) `∑_{m ≤ x} Λ(m) m^{-1/2} = O(√x log x)` by partial summation from Chebyshev, giving
        `|E_crit(h)| = O(h e^{h/2})`;
   (iii) `C_y ∈ C¹` with `C_y'(h) = ∫_0^∞ y'(x+h) y(x) dx` and `|C_y| + |C_y'| = O(e^{-a h})`,
        `a > 1/2` — available from the packet Gram algebra of
        `HTGeometry/HalfLineExponentialPacketGram.lean`;
   (iv) the limit.
   The screw-current card additionally needs the exact primitive
   `A_∞(h) = ∫_h^∞ e^{-t/2}/(1 - e^{-2t}) dt` and the contact laws `C_y'(0) = 0`,
   `C_y''(0) = -∫ (y')²`, both of which are one integration by parts on the exponential core.

### Sweep continued (2026-08-21, batch 3)

**Promoted**

| Card | Modules |
|---|---|
| `absolute-euler-paired-cumulative-critical-error-current-law` | `RHTower/PacketAutocorrelationExplicit.lean`, `RHTower/CriticalMellinBoundaryStieltjes.lean`, `RHTower/PairedInfiniteApertureCurrent.lean`, `RHTower/PacketAutocorrelationLaplace.lean`, `RHTower/PairedCompletedEulerCurrent.lean` |

**New reusable infrastructure — the half-line damped-exponential analysis stack**

Every module below works on the *finite real damped-exponential core*
`E(x) = ∑ⱼ rⱼ e^{-wⱼ x}`, `y = Im E`, with `1/2 < α ≤ Re wⱼ`.

- `RHTower/PacketAutocorrelationExplicit.lean` — **the key structural fact**: the half-line
  autocorrelation of a packet is *again a packet in the lag variable*,
  `2 C_y(h) = Re ∑ₖ qₖ e^{-w_k h}` with
  `qₖ = r_k ∑ⱼ rⱼ (1/(conj wⱼ + w_k) - 1/(wⱼ + w_k))`.  Smoothness, the explicit derivative, the
  integral form `C_y'(h) = ∫_0^∞ y(x) y'(x+h) dx`, and the decay `O(e^{-α h})` all follow.  Also
  `norm_halfLineExpPacket_le`: a uniform `(∑‖qₖ‖) e^{-αx}` bound for any packet.
- `RHTower/CriticalMellinBoundaryStieltjes.lean` — the corpus finite-aperture Stieltjes law with
  its **boundary term restored**.  Derived from the existing endpoint-vanishing theorem by
  applying it to `F - F(2a)` and using the value of the pairing on constants; no new analysis.
  This is the general device for turning any endpoint-vanishing integration-by-parts law into an
  aperture-limit law.
- `RHTower/PairedInfiniteApertureCurrent.lean` — the aperture limit.  Uses only
  `abs_criticalMellinCompletedError_le_sqrt` (`|E_crit(h)| ≤ 23 e^{h/2}`), so **no PNT remainder
  and no Chebyshev partial summation was needed** — the corpus already owns the sharp bound.
  Contains the explicit-tail technique (`‖∫_{Ioi T}‖ ≤ C e^{-cT}/c` from an exponential majorant)
  that replaces any abstract dominated-convergence argument for `∫_{Ioc 0 T} → ∫_{Ioi 0}`.
- `RHTower/PacketAutocorrelationLaplace.lean` — `⟨y, R_c y⟩ = ∫_0^∞ e^{-ch} C_y(h) dh`, and the
  polar pair `⟨y,R_{1/2}y⟩ + ⟨y,R_{-1/2}y⟩ = ∫_0^∞ 2cosh(h/2) C_y(h) dh`.
- `RHTower/PairedCompletedEulerCurrent.lean` — **`hasSum_pairedQuadratic`**: the paired quadratic
  form commutes with a convergent series of value functions (only nodewise convergence is needed,
  because the node set is finite).  Plus the Gauss digamma series as a value function, the prime
  lag series, and the completed identity.

**Heavy pile — `absolute-euler-paired-normalized-screw-current-identification`**

Sections 1–2 of that card now have all their inputs; what it still needs, in order:

1. `C_y'(0) = 0` and `C_y''(0) = -∫_0^∞ (y')²`.  Both are **pure algebra** on the explicit packet
   form: with `S = ∑_{j,k} rⱼ r_k w_k/(conj wⱼ + w_k)` and `T = ∑_{j,k} rⱼ r_k w_k/(wⱼ + w_k)`,
   swapping `(j,k)` gives `2 Re S = (∑ r)²` and `2T = (∑ r)²`, so the two cancel.  No integration
   by parts is required.
2. The tail primitive `A_∞(h) = ∫_h^∞ e^{-t/2}/(1-e^{-2t}) dt = artanh(e^{-h/2}) + arctan(e^{-h/2})`.
   Prove it by FTC: differentiate the closed form to `-k_∞` and show it tends to `0` at `+∞`.
3. `(11)`: `∑_{n≥0} (C_0/(2(n+1)) - ⟨y,R_{a_n}y⟩) = -∫_0^∞ k_∞(h)(C_y(h) - e^{-3h/2}C_0) dh`.
   Use `1/(2(n+1)) = ∫_0^∞ e^{-2(n+1)h} dh`, `∑_n e^{-a_n h} = k_∞(h)`,
   `∑_n e^{-2(n+1)h} = k_∞(h) e^{-3h/2}`, and Tonelli.
4. `(12)`–`(14)`: integration by parts against `A_∞`, whose `-½ log h` singularity at contact is
   absorbed by the `O(h)` vanishing from item 1; and the explicit value
   `∫_0^∞ A_∞ e^{-3h/2} = log 2 + π/6`.
5. `(19)`–`(21)` are distributional; formalize them as the *function* identity `(20)` plus the
   Laplace-transform identities `(24)`–`(25)`, which is what the card actually uses.

### Sweep continued (2026-08-21, batch 4)

**Promoted**

| Card | What was missing, and what closed it |
|---|---|
| `triangle-fact-orientation-transmutation` | full `S₃`-equivariance — added to `HTGeometry/TriangleFactOrientationTransmutation.lean` |
| `da-gauge-ht-divisor-blindness` | `HTGeometry/BaseGaugeJetField.lean`, `HTGeometry/DAGaugeDivisorBlindness.lean`, `RHTower/XiFinitePacketGauge.lean` |

**New reusable infrastructure**

- `HTGeometry/BaseGaugeJetField.lean` — **the Leibniz expansion of a base gauge**:
  `Dⁱ(a x) = ∑_{k≤i} c_{i,k} Dᵏ x` with `c_{i,i} = a`; hence every finite jet field
  `F(x,…,Dᵐx)` and the "fresh jet algebraic over the prefix" predicate are invariant under
  multiplication by a nonzero base element.  Use this for any *aperture*/minimal-order claim.
- `HTGeometry/DAGaugeDivisorBlindness.lean` — the complete gauge-invariant data list, assembled
  from the corpus's `AffineBaseJetGauge` theorems.
- `RHTower/XiFinitePacketGauge.lean` — **arbitrary finite off-critical packet implantation**: a
  product of centered quartic gauges realizes any prescribed finite quartet family while keeping
  both completed-xi symmetries, real-axis nonvanishing and exact order one.  Also
  `exists_radius_norm_polynomial_ge` (a nonzero polynomial is bounded below outside a disc), the
  general device for "a polynomial factor does not lower the order".
- `RHTower/CommonProfileBooleanAnchorCurvature.lean` gained the **base-general** rank-one
  sign-surjectivity classification (`rankOneBaseCoordinate`,
  `rankOneBaseCurvature_eq_one_add_two_mul`, `exists_rankOneBaseCurvature_eq`), i.e. equations
  `(CG9)`–`(CG12)` over an arbitrary anchor-disjoint base.  That closes the first of the three
  Lean obligations on `common-profile-boolean-anchor-curvature`.

**Techniques worth reusing**

- To prove an `S_n`-equivariance law without enumerating the group: prove the single-transposition
  case and close with `Equiv.Perm.swap_induction_on` plus multiplicativity of `sign`.
- `norm_num` fails to evaluate `!![…] i j` at index `2`; `simp` does.
- To convert `∀ᶠ z in cocompact ℂ, p z` into `∃ R, ∀ ‖z‖ ≥ R, p z`:
  `rw [← Metric.cobounded_eq_cocompact, ← comap_norm_atTop (E := ℂ), Filter.eventually_comap]`
  then `Filter.eventually_atTop`.

**Still open on `common-profile-boolean-anchor-curvature`** (two obligations):
`(SG2)` rank `2^r` and inertia `(2^{r-1}, 2^{r-1}, l-2^r)` of the shear kernel — needs matrix rank
of a signed sum of independent outer products and a Sylvester-type inertia statement; `(SG3)` the
local nonzero eigenvalues `λ_± = p(1 ± √(4p-3))/2` — these are the roots of
`λ² - pλ + (p² - p³)`, the characteristic polynomial of `diag(1,-1)·G` for the `2×2` Gram
`G = [[p², p(1-p)], [p(1-p), p²-p]]` of `(a_p, b_p)`; `(SG6)` the Fourier normalization; and
`(SG7)`–`(SG10)` in the first-crossing section.

### Nevanlinna keystone: the logarithmic-derivative Poisson–Jensen formula is CLOSED (2026-08-21)

`formal/GaloisForLFunctions/HTGeometry/LogDerivPoissonJensen.lean` proves

**`logDeriv_poissonJensen`** — for `f` meromorphic on `closedBall c |R|` with finite order at every
point, no divisor on the boundary circle, and `w` an interior point where `f` is analytic and
nonzero:

```text
f'(w)/f(w) = ∑ᶠ u, m_u ( 1/(w−u) + conj(u−c)/(R² − conj(u−c)(w−c)) )
             + circleAverage (2(z−c)/(z−w)² · log ‖f z‖) c R .
```

This is the identity the classical estimate `m(r, f'/f) = O(log r + log T(r,f))` is read off.
Supporting declarations, all reusable:

- `eventuallyEq_nhdsNE_of_codiscreteWithin`, `eq_of_eventuallyEq_nhdsNE`,
  `eventuallyEq_nhds_of_codiscreteWithin` — **germ transport across a codiscrete equality**: a
  codiscrete identity on a neighbourhood of `w`, plus continuity of both sides at `w`, upgrades to
  an identity of germs at `w`.  This is the general device for turning mathlib's
  `extract_zeros_poles` factorization into pointwise derivative statements.
- `logDeriv_sub_zpow`, `finprod_shiftPow_apply`, **`logDeriv_eq_divisorSum_add`** — the logarithmic
  derivative of an extracted factorization at a point off the divisor.
- `circleIntegrable_herglotzDeriv_mul` — circle integrability against the differentiated kernel.
- **`circleAverage_herglotzDeriv_log_split`** — the divisor/zero-free split of the boundary
  integral, assembling `circleAverage_herglotzDerivKernel_log_norm_sub` (one Blaschke term) and
  `logDeriv_eq_circleAverage_of_ne_zero` (the zero-free factor) over the finite divisor.

**Steps 1 and 3a are now also closed** in the same module:

- `norm_circleAverage_le` — `‖circleAverage F‖ ≤ circleAverage ‖F‖` for a vector-valued average
  (mathlib only had the real `abs` version).
- `norm_circleAverage_herglotzDeriv_log_le` — the boundary term is at most
  `2R/(R−‖w−c‖)² · circleAverage |log ‖f‖|`, via `norm_herglotzDerivKernel_le` and
  `circleAverage_mono`.
- **`norm_logDeriv_le`** — the Nevanlinna pointwise bound:
  `‖f'(w)/f(w)‖ ≤ ‖divisor sum‖ + 2R/(R−‖w−c‖)² · circleAverage |log ‖f‖|`.
- `abs_log_eq_posLog_add_posLog_inv` and **`circleAverage_abs_log_norm_eq`** —
  `circleAverage |log ‖f‖| = m(r,f) + m(r,1/f)` exactly, in mathlib's
  `ValueDistribution.proximity` language.

**What is still needed** (in order):
1. `m(r,f) + m(r,1/f) ≤ 2 T(r,f) + O(1)`.  The inversion half is mathlib's
   `ValueDistribution.characteristic_sub_characteristic_inv_le` together with the corpus's
   `SecondMainTheoremChain.characteristic_zero_eq_inv_top`; the only missing ingredient is
   `0 ≤ logCounting f a r` for `1 ≤ r` (mathlib has no `logCounting_nonneg`).
2. the circle estimate `∫₀^{2π} log⁺ (1/‖Re^{iθ} − a‖) dθ = O(1)`, needed to bound the divisor sum
   in `norm_logDeriv_le` by `N(r,f) + N(r,1/f)` after averaging in `w` over a circle;
3. the exceptional-set removal through `HTGeometry.BorelGrowthLemma.borel_growth`.

### PROMOTED: `two-edge-boundary-quartet-amplification-law` (2026-08-21)

`formal/GaloisForLFunctions/RHTower/TwoEdgeBoundaryQuartet.lean` now proves §§1–3 of the card and
the analytic half of §4, all unconditional and axiom-clean:

- `edgeLaplace`, `twoEdgeTransform`, **`twoEdgeTransform_eq`** — **equation `(4)`**, the exact
  two-edge identity `G_a(w) = e^{aw}A_f(w) + e^{-aw}A_f(-w)`, by the two boundary-layer
  substitutions `x = a − s` and `x = s − a` (`intervalIntegral.integral_comp_sub_left` /
  `integral_comp_add_left`).  No smoothness or decay of `f` is used — only that the layers are the
  interval `[a−L, a]` and its reflection.
- `twoEdgeTransform_neg` — **equation `(5)`**, evenness.
- `quartetEdge`, `quartetContribution`, `quartetContribution_eq_mul`,
  **`quartetContribution_expand`** — **equations `(7)`–`(8)`**, the three-term aperture expansion.
- `apertureSeq`, **`exp_apertureSeq_mul_sq`** — **equation `(9)`**: at
  `a_k = (π − 2 arg A + 2πk)/(2T)` the leading oscillatory factor is *exactly* `−‖A‖²`.
- `apertureSeq_atTop`, `quartetContribution_apertureSeq_le`,
  **`tendsto_quartetContribution_atBot`** — **equation `(10)`**: the quartet contribution tends to
  `−∞` along the aperture sequence, for every `δ > 0`, `T > 0` with `A_f(δ+iT) ≠ 0`.
- `norm_twoEdgeTransform_imaginary_le` — **equation `(11)`**.
- `abs_quartetContribution_imaginary_le`, `summable_quartetContribution_imaginary`,
  **`abs_tsum_quartetContribution_imaginary_le`** — **equation `(12)`**: the all-line background is
  bounded by `4 ∑ (‖A_f(it_n)‖ + ‖A_f(−it_n)‖)²`, *uniformly in the aperture*.  The summability of
  that divisor sum is the all-line carrier's own datum.
- `norm_integral_oscillatory_le`, `abs_integral_trigPolynomial_le` — a finite trigonometric
  polynomial with strictly positive frequencies has primitive bounded by `∑ ‖c_j‖ / T_j`.

§4 is now closed as well, and its machinery is **reusable for any exponential-sum no-go**:

- `norm_integral_oscillatory_le'` — primitive bound `‖c‖/|T|` at any nonzero frequency;
- `norm_integral_indexedSum_le` — the same for a finite indexed family;
- `trigPoly`, `trigPoly_sq`, `conj_trigPoly`, `trigPoly_normSq`, `trigPolyRe_sq` — the expansion
  `(Re A)² = Re(A²)/2 + ‖A‖²/2` with both halves written as double sums over the frequency pairs
  `T_j + T_k` and `T_j − T_k`;
- **`abs_integral_trigPolyRe_sq_sub_le`** — the **mean-square (Parseval) law**
  `|∫_0^Y P² − (Y/2) ∑ ‖c_j‖²| ≤ C`, from the diagonal split of `‖A‖²`;
- **`exists_neg_trigPolyRe`** — a nonzero finite real trigonometric polynomial with distinct
  strictly positive frequencies drops below a fixed negative level at arbitrarily large arguments.
  The argument is elementary: `P ≥ −η` on a ray gives `Q = P + η ≥ 0`, hence
  `∫ Q² ≤ (B+η) ∫ Q = O(1) + O(ηY)`, contradicting the linear growth once
  `(B+η)η < (∑‖c_j‖²)/2`.  **No almost-periodic theory is used** — this replaces the "almost
  periodic recurrence" step every card in this lane appeals to.
- `eventually_augmented_neg` — equation `(13)`: against any uniformly bounded background the
  augmented form is eventually negative.

### PROMOTED: `semilocal-number-form-equivalence` (2026-08-21)

`formal/GaloisForLFunctions/HTGeometry/FiltrationNumberForm.lean` — a **reusable** abstract layer,
not a card-specific file:

- `filtCost`, `filtForm` — the distance to a filtration member and the total number form
  (`ℝ≥0∞`-valued, so no summability side conditions anywhere);
- `mul_filtCost_le`, `filtCost_le_mul`, `mul_filtForm_le`, `filtForm_le_mul`,
  **`filtForm_ne_top_iff`**, `filtForm_equivalence` — comparable costs give comparable number forms
  with the *same* constants and a common finiteness domain.  This is the general "two equivalent
  Hilbert norms on a common filtration have the same form domain" statement, and it needs no
  Hilbert structure at all;
- `filtCost_comp_addMonoidHom`, `filtForm_comp_addMonoidHom` — transport along a realisation map;
- `basisFiltration`, `repr_eq_zero_of_mem_basisFiltration`, `basisTruncation`,
  **`filtCost_normSq_basisFiltration`**, **`filtForm_normSq_basisFiltration`** — the spectral
  identity `∑_n dist(f, E_n)² = ∑_j j |c_j|²`, by `ENNReal.tsum_comm` and `#{n : n < j} = j`;
- `filtForm_realization`, **`number_form_equivalence`** — the card's whole statement for two
  comparable Hilbert realisations of one filtration;
- **`abs_bilin_le_of_abs_diagonal_le`** — a symmetric continuous bilinear form with
  `|B(x,x)| ≤ ‖x‖²` satisfies `|B(x,y)| ≤ ‖x‖‖y‖` (parallelogram law + the `t`/`t⁻¹` rescaling).
  Reusable for every "indefinite form has a bounded representative" argument;
- `formRieszMap`, `formRiesz`, `isSelfAdjoint_formRiesz`, `norm_formRiesz_le_one`,
  **`exists_energy_contraction`** — the canonical self-adjoint contraction representing the form.

### PROMOTED: `high-shell-codiagonal-closability-dichotomy` (2026-08-21)

`formal/GaloisForLFunctions/RHTower/WeightedCodiagonalDichotomy.lean` proves the full dichotomy for
an arbitrary **complex Banach space** `H` (no inner product of `H` is used):

- `memℓp_finsupp`, `codiagEmbed`, `codiag`, `norm_codiagEmbed_sq` — the algebraic core
  `c₀₀(ℕ;H) ⊂ ℓ²(ℕ;H)` and the weighted row on it;
- `codiagMap`, `codiagCLM`, `codiagCLM_codiagEmbed`, `norm_codiagMap_le` — the bounded extension,
  built **directly as the convergent series** `∑' a_m x_m` (absolute convergence from
  `‖a_m‖‖x_m‖ ≤ (‖a_m‖²+‖x_m‖²)/2`), so no density-and-extension argument is needed;
- `testVector`, `codiag_testVector`, `norm_codiagEmbed_testVector_sq`, **`norm_codiagCLM`** — the
  exact operator norm `‖C_a‖ = ‖a‖₂`;
- `graphNullVector`, `codiag_graphNullVector`, `norm_codiagEmbed_graphNullVector`,
  **`not_isSequentiallyClosableBetween_codiag`** — the singular graph sequence;
- **`codiagonal_closability_dichotomy`**, `not_isSequentiallyClosableBetween_unitCodiag`.

Reuses `RHTower.IsSequentiallyClosableBetween` and
`not_isSequentiallyClosableBetween_of_exact_norm_graphNull`
(`RHTower.ArithmeticSchurExactNormRiggingNoGo`), plus
`ContinuousLinearMap.tsum_mul_le_sqrt_mul_sqrt` and
`GaloisForLFunctions.summable_mul_of_summable_sq`.  **Read this before building any `ℓ²`
Cauchy–Schwarz or nonclosability argument.**

### PROMOTED: `semilocal-prolate-extension-rank-two-ambiguity` (2026-08-21)

`formal/GaloisForLFunctions/RHTower/JacobiDeficiencyRankTwoAmbiguity.lean`:

- `IsJacobiSolution`, **`IsJacobiSolution.ext`**, `jacobiSolutions`,
  **`rank_jacobiSolutions_le_one`** — a half-line Jacobi solution is determined by its first
  coordinate, so the solution space is at most one-dimensional;
- `IsJacobiSolution.conj`, `sqSummable`, `jacobiDeficiency`, `mem_jacobiDeficiency_conj`,
  **`jacobiDeficiency_eq_bot_iff_conj`**, **`jacobi_deficiency_indices`** — the `(0,0)`-or-`(1,1)`
  alternative, obtained by comparing only *triviality* of the two spaces (no antilinear dimension
  theory);
- `exists_isSelfAdjoint_extension_of_deficiency_one` — von Neumann's construction, packaged from
  `HTGeometry.VonNeumannDeficiency`;
- `hasRankLE_neg`, `hasRankLE_sub`, **`hasRankLE_add`** — ranks add (a mathlib-gap lemma the corpus
  did not have in this two-operator form);
- **`memSchattenClass_congr_of_hasRankLE`**, `memSchattenClass_congr_of_two_block` — Schatten
  membership is *unchanged* (an `iff`) by a finite-rank perturbation.  Reuse this for every
  "boundary choice does not affect the ideal" argument.

### PROMOTED: `nodal-charge-character-fan-realization` (2026-08-21, audit only)

No new Lean was needed: `HTGeometry/NodalChargeCharacterRealization.lean` already covered §§1–3 of
the card in full (all sixteen declarations axiom-clean).  The card's §5 items (1)–(6) are the
*candidate-new* presentation-invariant construction, which the card itself excludes from what it
banks.  **Lesson repeated:** re-audit every card whose Lean section predates the current tree
before assuming work remains.

### PROMOTED: `finite-jet-graded-reality-nonselection` (2026-08-21)

Two new modules, both reusable well beyond this card.

**`formal/GaloisForLFunctions/HTGeometry/ResidueFilledFluxGerm.lean`** — the general layer the whole
completed-flux lane was missing:

- `fluxGerm f w x = if x = 0 then -(ord_w f) else -x·f'(w+x)/f(w+x)`;
- **`fluxGerm_analyticAt_zero`** — analyticity at the filled centre for *any* `f` with a zero of
  finite order (the corpus previously had only `xi`-specific and model-specific versions);
- `eventually_ne_zero_of_analyticOrderAt_eq` — a finite-order zero is isolated;
- **`fluxGerm_mul`** — the germ of a product is the sum of the germs, at arbitrary orders.

**`formal/GaloisForLFunctions/RHTower/GradedRealityQuartetRealization.lean`** — the realization.  The
key structural simplification: **do not rescale the function, rescale the coordinate change.**
Writing `X_N(s) = F_N(-2πi(s-1/2))` with `F_N(w) = cosh(w-π/2)cosh(w+π/2)·(1 + (w⁴+π⁴/4)^{2N+1})`
puts the whole construction inside the corpus's *unscaled* `coshQuartetEnvelope`, so
`CoshQuartetEnvelope`, `CoshPolynomialPeriodClassification` and `CoshPolynomialExactOrderOne` apply
verbatim.  `(w²-α²)(w²-conj α²)` collapses to the closed form `w⁴ + π⁴/4`.

Contents: `gradedRealityXi_functional_equation`, `gradedRealityXi_conj`,
`gradedRealityXi_ne_zero_of_real`, the four quartet zeros, simplicity
(`analyticOrderAt_gradedRealityFn_fePartner`/`_schwarzPartner`), `gradedRealityFn_periodic_iff`,
`gradedRealityFn_exact_order_one_bounds`, the multiplier germ layer (`quartetShiftPoly`, `multUnit`,
`multFlux`, `multFlux_eventuallyEq`), the exact separation
(`four_mul_fePartnerCentre_cube = π³(1-i)`, `four_mul_schwarzPartnerCentre_cube = π³(1+i)`,
`multUnit_zero_ne` via `1-i = -i(1+i)` and `(-i)^{2N+1} ≠ 1`), and the capstone
**`finite_jet_graded_reality_nonselection`**.

**Still open in the same lane (two sibling cards).**
`simultaneous-multiquartet-finite-passport-realization` and
`finite-completed-flux-passport-surjectivity` need the *multi*-quartet base
`∏_j cosh(w - A_j) cosh(w + A_j)` with independently prescribed depths.  Everything local
transfers; the two genuinely missing pieces are

1. the **period classification for a product of envelopes** times a nonconstant polynomial
   (`CoshPolynomialPeriodClassification` covers only a single envelope), and
2. the **two-sided order-one sandwich for a product of envelopes**
   (`CoshPolynomialExactOrderOne` likewise).

Simplicity of each quartet zero is then automatic from distinctness of the positive displacements
`A_j` (all `±A_j - A_k ≠ 0`), and the germ comparison is the same `fluxGerm_mul` split, one `j` at
a time.  `FiniteHermiteCRT.lean`, `FiniteFluxPassport.lean` and `ImaginaryAxisPositiveRepair.lean`
already supply the passport half of the third card.

### PROMOTED: `simultaneous-multiquartet-finite-passport-realization` (2026-08-21)

The multi-quartet layer flagged as missing in the previous entry is now built.

**`formal/GaloisForLFunctions/RHTower/MultiQuartetEnvelope.lean`** — products of displaced cosh
quartet envelopes: `multiEnvelope`, its evenness/Schwarz/`πi`-periodicity, the zero-set criterion,
imaginary-axis positivity, **`multiEnvelope_mul_polynomial_periodic_iff`** and
**`multiEnvelope_mul_polynomial_order_one_bounds`**.  The period proof is *shorter* than the
corpus's single-envelope one: an infinite orbit of envelope zeros injects its real parts into the
finite set `{±A_j}`, forcing `Re h = 0`; two consecutive orbit points quantise `Im h` into `πℤ`.
Also `eventually_norm_polynomial_eval_ofReal_ge` (a nonzero polynomial is eventually
`≥ ‖lc‖/8` on the positive real ray), extracted from the corpus's `a = 0` envelope bound.

**`formal/GaloisForLFunctions/RHTower/MultiQuartetPassportRealization.lean`** — the realization,
with independently prescribed depths `M_j` at pairwise distinct positive displacements.  Capstone
**`simultaneous_multiQuartet_realization`**.  Two reusable pieces beyond the card:

- **`polynomial_wronskian_shift_eq_zero`** — `P'(z)P(z+h) = P'(z+h)P(z)` identically forces `h = 0`
  for nonconstant `P`, by the leading-coefficient identity `deg P = deg (P(·+h) − P)` (with
  `leadingCoeff_derivative_eq`).  This replaces every "the ratio is constant" limiting argument in
  this lane.
- **`iteratedDeriv_eq_zero_of_eventuallyEq_pow_mul`** — a germ that is eventually `x^M·W(x)` with
  `W` analytic has vanishing jet below `M`, with the `W ≡ 0` case handled separately.

**`formal/GaloisForLFunctions/HTGeometry/ResidueFilledFluxGerm.lean`** gained the affine dictionary
**`analyticOrderAt_comp_affine`** and **`fluxGerm_comp_affine`**, so germ statements transfer
between the entire coordinate and the functional-equation normalization without hand-waving.

**Still open in this lane:** `finite-completed-flux-passport-surjectivity` — the *arbitrary*
prescribed-passport version.  Its components (`FiniteHermiteCRT`, `FiniteFluxPassport`,
`ImaginaryAxisPositiveRepair`, plus the new `MultiQuartetEnvelope` layer) are all present; what
remains is the assembly, which needs the degree-controlled equivariant CRT to be matched against
the new product envelope.

### PROMOTED: `rational-hurwitz-lorentz-boost-colligation` (2026-08-21)

`formal/GaloisForLFunctions/RHTower/RationalHurwitzLorentzBoost.lean`.  Cheap card: the seam-energy
half was already in `XiRationalHurwitzDyadicRefinement` (`normalizedScaleSeamEnergy_eq_sinh` is
`(11)`, `normalizedScaleSeamEnergy_sq_sub_linear` is `(12)`), so only the colligation was new.

- `lorentzBoost u = !![cosh u, sinh u; sinh u, cosh u]`, `kreinMatrix`, `lightConeChart`;
- `lorentzBoost_krein`, `det_lorentzBoost`, `lorentzBoost_mul` (rapidity additivity),
  `lorentzBoost_pow`, `lorentzBoost_mulVec_plus/minus` (the light-cone eigenvectors);
- `hurwitzBoost`, `hurwitzBoost_mul`, `hurwitzBoost_pow`, **`hurwitzBoost_lightCone`** (the two
  inverse reflected responses `n^{±(Re ρ − 1/2)}`);
- `normalizedScaleSeamEnergy_eq_boost_offDiagonal_sq`, `arsinh_sqrt_normalizedScaleSeamEnergy`;
- **`metricForm`, `IsPositiveMetric`, `IsContractionIn`, `rapidity_eq_zero_of_contraction_pair`,
  `re_eq_half_of_contraction_pair`, `hurwitzBoost_eq_one_iff`** — the positive-metric rigidity
  `(15)`, stated with no hypothesis beyond the definitions.

The card's last gate was a deferral *policy* ("formalize only if the source supplies
contractivity"), not a mathematical gap; the theorem is unconditional and is now machine-checked.

**Direct sibling, next in line:** `local-euler-valuation-lorentz-log-colligation` builds the matrix
logarithm `C_p(ρ) = ∑_m T^m/m = −Log(I − T)` on top of exactly this boost.  Items `(1)`–`(10)` are
algebra plus a geometrically convergent series; item `(16)` (the Gamma–Meixner threshold
`θ > 2|a|`) additionally needs `∑_p (log p)² p^{-σ}` convergence for `σ > 1` and divergence at
`σ = 1` — the latter follows from the corpus's `log_log_sub_one_le_sum_primesBelow_inv`.

### PROMOTED: `local-euler-valuation-lorentz-log-colligation` (2026-08-21)

`formal/GaloisForLFunctions/RHTower/EulerValuationLorentzLog.lean` is **built, wired and
axiom-clean**, and already covers items `(1)`–`(10)` and `(17)` of the card:

- `eulerLightConePlus/Minus` = `p^{-(1-ρ)}`, `p^{-conj ρ}`, with `norm_eulerLightConePlus/Minus`
  and the strip bounds `..._lt_one` — this is `(4)`;
- `eulerLogEven`, `eulerLogOdd` = `(f(z₊)±f(z₋))/2` — `(7)`–`(8)`;
- `eulerPhase`, `eulerRapidity`, `eulerTransfer`, **`eulerTransfer_pow`**,
  `eulerTransfer_pow_entry_diagonal/offDiagonal` — `(2)`, `(3)`, `(5)` degreewise, built on
  `RationalHurwitzLorentzBoost.lorentzBoost_mul`;
- **`hasSum_eulerLogOdd`**, `hasSum_eulerLogEven` — `(9)`: the connected-cycle series
  `∑_m (T^m)_{ij}/m` converges to the even/odd coordinates (via
  `Complex.hasSum_taylorSeries_neg_log`);
- **`eulerLightCone_eq_iff`**, **`eulerLogOdd_eq_zero_iff`** — `(10)`: the odd coordinate vanishes
  *exactly* on the critical line;
- `max_norm_eulerLightCone`, `max_norm_eulerLightCone_lt_one` — `(17)`.

**The Gamma–Meixner threshold `(11)`–`(16)` is now proved as well**, so the card is promoted:

- `eulerConeScale p ρ = p^{|a|-1/2}`, `eulerConeCoScale p ρ = p^{-|a|-1/2}`,
  `norm_eulerLightCone_sub` (`‖z₊ − z₋‖ = X − Y` exactly);
- **`norm_eulerLogOdd_le`** (`‖v_p‖ ≤ 2X` once `X ≤ 1/2`) and **`le_norm_eulerLogOdd`**
  (`‖v_p‖ ≥ X/8` once `X ≤ 1/8` and `Y ≤ X/2`), both from the corpus's *order-two* uniform Taylor
  estimate `HTGeometry.ComplexLogTaylorUniform.norm_log_one_add_sub_taylor_le'`
  (`‖−log(1−z) − z‖ ≤ ‖z‖²`) — no series manipulation at all;
- `gammaMeixnerWeight`, `cosh_two_log_bounds`, `gammaMeixnerWeight_le`, `le_gammaMeixnerWeight`;
- `tendsto_primes_cofinite_atTop`, `eventually_eulerConeScale_le`,
  `eventually_eulerConeCoScale_le`, `eventually_sq_log_ge` — the "for all but finitely many primes"
  layer, obtained from `Function.Injective.tendsto_cofinite` and `Nat.cofinite_eq_atTop`;
- **`summable_eulerAntiReflectionTerm_iff`** — the exact threshold, by
  `Summable.of_norm_bounded_eventually` in *both* directions, against
  `summable_abs_log_natCast_pow_mul_rpow_neg` (restricted to primes) above the threshold and
  against `not_summable_one_div_primes` at or below it.

**Reusable pattern:** the cofinite/`atTop` transfer plus `Summable.of_norm_bounded_eventually` in
both directions is the cheapest way to prove an *exact* prime-Dirichlet convergence threshold from
two-sided eventual bounds — no `Set.Finite.summable_compl_iff` juggling is needed.

## `physical-interval-anchor-coarea-phase-law` — PROMOTED to stage 3

Module `formal/GaloisForLFunctions/RHTower/PhysicalIntervalAnchorCoarea.lean`
(namespace `RHTower.PhysicalAnchor`), wired into `GaloisForLFunctions.RHTower`.

The only open gate was `(PI3)`–`(PI4)` and `(PI12)`–`(PI16)`.  All are now closed
unconditionally; `#print axioms` on every capstone returns exactly
`[propext, Classical.choice, Quot.sound]`.

Key design decision: the aperture pairing `anchorInner A f g = ∫_{Ioc 0 A} f g` is used as a
plain bilinear form on functions, not as an `L^2` inner product.  This avoids the `MeasureTheory.Lp`
instance stack entirely; every overlap integral reduces to
`volume.real (Ioc 0 A ∩ Ioc (max a c) (min b d))` through `cellIndicator_mul` +
`setIntegral_indicator`.  The price is that the corpus lemma
`RHTower.commonGramBooleanAnchorCurvature` (stated for `InnerProductSpace ℝ E`) does not apply
directly, so the module proves the strictly more general `gramBooleanAnchorCurvature` for an
arbitrary real Gram kernel `G : κ → κ → ℝ`.  That generalization is reusable and should be
preferred over the inner-product version whenever the "energy" is a bilinear pairing rather than
a genuine norm.

Reused from the corpus without change: `coordinatePacketWeight`, `commonAnchorWeight`,
`coordinatePacketWeight_union`, `sum_powerset_signed_commonCoordinateWeight`
(`RHTower.CommonProfileBooleanAnchorCurvature`).

Capstones: `physical_anchor_sign_conjecture_false`,
`physical_interval_anchor_coarea_phase_law`.

Arithmetic facts that carry the falsification, each proved from a single integer inequality:
`physWeight_two_lt_three` (`2^3 < 3^2`), `two_physWeight_three_lt_three_physWeight_two`
(`3^4 < 2^9`), `log_two_lt_three_physCellWidth` (`2 < 64/27`).

## `zeta-fisher-superspace-global-negative-curvature` — PROMOTED to stage 3

New module `formal/GaloisForLFunctions/RHTower/EulerFisherPoincareBoundary.lean`, wired into
`GaloisForLFunctions.RHTower`.  The card already had the moment determinant and the strict
negativity; the two open items were the curvature identification and the Poincare asymptotic.
Both are now unconditional; `#print axioms` returns exactly
`[propext, Classical.choice, Quot.sound]` on every capstone.

Two decisions worth remembering.

1. **Mathlib has Riemannian metrics but no curvature tensor.**  `Mathlib.Geometry.Manifold.
   Riemannian.Basic` and the Riemannian vector-bundle files carry metrics only; there is no
   `scalarCurvature`.  The module therefore defines the two-dimensional conformal scalar
   curvature by the Liouville formula `-Laplacian(log G)/G` and proves the classical identity
   `-(G G'' - (G')^2)/G^3`.  Any later card needing surface curvature should reuse
   `conformalScalarCurvature` rather than reinventing it.

2. **The pole is reached through mathlib's Hurwitz machinery, not through a Laurent expansion.**
   `HurwitzZeta.differentiableAt_hurwitzZetaEven_sub_one_div 0` plus `hurwitzZetaEven_zero` gives
   differentiability of `zeta(s) - 1/((s-1) Gamma_R(s))` at `s = 1`; adding back
   `Gamma_R(s)^{-1}` (entire, value `1` at `1`) produces an entire `zetaPoleUnit` agreeing with
   `(s-1) zeta(s)`.  This is much cheaper than building the Laurent series.

The link between the corpus Euler logarithm and the moment family is
`canonicalEulerLogZeta_ofReal`, proved by `Function.Injective.tsum_eq` along
`(p, k) |-> p^{k+1}`; it also yields reality and positivity of `zeta` on `(1, infinity)`
without a separate argument.

Termwise differentiation `M_j' = -M_{j+1}` uses `hasDerivAt_tsum_of_isPreconnected` on `Ioi c`
with `1 < c < beta`; the dominating series is the harmonic-weight-free
`summable_eulerPrimePowerEnergy_pow_rpow`.

## `compact-group-minimax-return-volume-law` — PROMOTED to stage 3

Three new modules under `formal/GaloisForLFunctions/HTGeometry/`:
`CompactConnectedAbelianGenerators.lean`, `CompactGroupCoveringVolume.lean`,
`CompactGroupMinimaxReturn.lean`; all wired into `GaloisForLFunctions.HTGeometry`, all capstones
audited at `[propext, Classical.choice, Quot.sound]`.

**The key fact for future cards: mathlib has no Pontryagin duality.**
`Mathlib/Topology/Algebra/PontryaginDual.lean` defines the dual and proves it discrete for a
compact group, and nothing else — no double-dual theorem, no separation, no classification of
closed subgroups of the circle.  Any card whose paper proof uses duality has to be re-routed.
Two replacements were built here and are reusable:

1. *A proper closed subgroup is invisible to Haar without duality.*
   `measure_character_fibre_eq_zero` shows a nontrivial character of a **connected** compact
   abelian group has null kernel by observing that its fibres are translates of the kernel (so
   all of equal measure) and that its image is infinite — the latter from
   `infinite_range_of_character`, which applies `IsPreconnected.Icc_subset` to
   `z |-> ‖z - 1‖` on the image.  No circle subgroup classification is needed.

2. *The dual is countable because `L²` is separable.*  `countable_charSet` maps characters into
   `Lp ℂ 2 μ` (second countable, since `MeasureTheory.IsSeparable μ` is an instance for a finite
   Borel measure on a second-countable space — remember to
   `import Mathlib.MeasureTheory.Measure.SeparableMeasure`, it is not in the usual closure),
   where distinct characters sit at distance `√2`.  The generic helper
   `countable_of_separated` (a uniformly separated set in a second-countable metric space is
   countable) is reusable.

Divisibility of a compact connected abelian group (`exists_pow_eq_of_connected`) is what mathlib's
`Measure.measurePreserving_zpow` is missing: it takes `RootableBy G ℤ` as a hypothesis, and
`rootableByIntOfCompactConnected` now supplies it.

Bridging additive Peter-Weyl (`CompactAbelian.exists_character_ne_one`, stated for
`AddCommGroup`) to a multiplicative group needs `letI : MeasurableSpace (Additive G) := ‹_›` and
`letI : SecondCountableTopology (Additive G) := ‹_›` — those two type-synonym instances are
missing in mathlib, while `CompactSpace`, `T2Space` and `IsTopologicalAddGroup` transfer
automatically.

For the covering side, mathlib's `Metric.coveringNumber` / `packingNumber` API in
`Mathlib/Topology/MetricSpace/CoveringNumbers.lean` is complete enough that the sandwich is only
translation invariance of balls plus `coveringNumber_le_packingNumber`.  Note the current names
are `Metric.closedEBall` / `Metric.eball`; `EMetric.closedBall` is deprecated.

Only the "external specialist audit" gate remains unchecked; it is not a Lean gate.

## `euler-support-energy-position-uncertainty` — PROMOTED to stage 3

Module `formal/GaloisForLFunctions/RHTower/EulerSupportEnergyUncertainty.lean`, wired into
`GaloisForLFunctions.RHTower`; capstones audited at `[propext, Classical.choice, Quot.sound]`.

Two reusable pieces:

1. `summable_mul_of_rpow_summable` — Hölder for **summable real families** (mathlib only exposes
   the `ℝ≥0` version `NNReal.summable_and_inner_le_Lp_mul_Lq_tsum`).  Any card needing an
   `ℓ^p`–`ℓ^q` pairing on a countable index should call this instead of re-deriving it.
2. `summable_absDiscrepancy_of_holder` — the abstract weighted-Hölder abscissa bound in the
   generalized-Dirichlet framework of `RelativeStripDivisorReflection.lean`.  It turns an
   `ℓ^q` energy abscissa plus a support exponent into an absolute-convergence abscissa.

**Technique worth copying.**  The paper proof of the support half compares
`∑_{k≥1} p^{-ku}/k = -log(1 - p^{-u})` with `C_u p^{-u}`, which is only valid once `p^{-u}` is
bounded away from `1` — in Lean that forces a cofinite exception argument.  Replacing it with
`p^{-(k+1)u} ≤ p^{-u} (2^{-u})^k` (true because every prime is at least `2`) gives a uniform
geometric majorant with no exceptional set.  The same device handles the deep prime powers
`k ≥ 2` with the shift `p^{-(j+2)σ} ≤ p^{-2σ}(2^{-σ})^j`.

The position half `(U)`/`(P)` is a one-line consequence of the parent card's
`abs_re_sub_half_le_of_reflection`; the parent
(`3-formalized/.../euler-support-transverse-divisor-rigidity.md`) already owns the
divisor-avoids-the-half-plane step, so nothing is assumed here.
