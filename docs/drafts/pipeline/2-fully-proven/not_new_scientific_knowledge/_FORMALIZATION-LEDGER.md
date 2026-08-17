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

