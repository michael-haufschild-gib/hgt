# Mathematical walls: three core families

Every wall below belongs to one of three requirements: **P — arithmetic production**, **U — uniform exclusion**, or **R — faithful realization and transport**. These are an organizational classification, not a theorem that all obstacles are mathematically equivalent. Several routes meet more than one wall. The AAL finite-exception problem crosses all three.

**Available** means the specified input is proved in the inspected Lean source. **Open** means the needed input is not supplied by the audited corpus. **Excluded** means a precise mechanism or axiom package has a proved obstruction; it does not retire every route using related objects. No builds or fresh kernel audit were run. Evidence and theorem statements are in [the fact log](../../../logs/review-1411-facts.txt) and [search evidence](../../../logs/review-1411-evidence.jsonl).

## P — Arithmetic production

The shared question is whether actual prime/Möbius arithmetic produces the required signed bound. Exact transforms, functional equations and downstream receivers do not produce cancellation by themselves.

| Wall | Status and exact boundary | Remaining mathematical input |
|---|---|---|
| **P1. Fixed strip** | **Available:** MMD excludes ζ zeros in `Re s>7/8` and gives the reflected strip. Dirichlet and specified Eisenstein Hecke-family statements are available. [MMD] | A stronger producer with all family, conductor, phase and length hypotheses discharged. General-number-field transfer is not included. |
| **P2. Gauss-monomial exponent** | **Excluded:** below `2/3` in the uncoupled class and below `3/5` in the coupled class. The `3/5` equality case is classified; changing order/arity within this class cannot escape. [GAUSS] | A genuinely different signed producer, not another representative of the same completed pairing. |
| **P3. Completion versus reflection** | **Available:** uncompleted correction is holomorphic and nonzero on `Re s>σ` for every `σ>1/2` after a suitable finite cutoff. **Open:** usable reflection after decompletion. [DECOMPLETE] | An exact reciprocal identity with a controlled boundary defect, retaining target phases. |
| **P4. Critical cancellation** | **Open:** critical subpower bounds for the actual MC, WD, FU, CTF, PBM and CHMD sources. Their RH receivers are available. [MC] [WD] [FU] [CTF] [PBM] [CHMD] | A source-specific signed estimate in the full required parameter range. |
| **P5. Long-mollifier range** | **Available:** short-mollifier twisted moments and bounded-length Euler-block factorization. **Excluded:** the excessive near-unit target at fixed power length in the stated class. [WD-SHORT] [WD-BLOCK] [LONG-MOMENT] | Long-range cancellation compatible with the actual receiver; not a false near-unit asymptotic and not an all-length raw-polynomial bound. [WD-RAW] |
| **P6. Higher arithmetic correlations** | **Available:** prime second-trace control and `O(d/L²)` pole perturbation of the fourth trace. **Open:** the actual prime fourth/higher trace bound. [CENSUS] | A signed higher-correlation estimate, or a different invariant with sufficient census information. |
| **P7. Family transfer** | **Available:** general Brauer/Hecke meromorphic completion, unit functional equation and signed multiplicity accounting. [ARTIN] | Pole cancellation for holomorphy, plus independent critical-line control. Meromorphic completion is not Artin holomorphy or GRH. |

The short exponent-`13/50` Levinson construction proves an explicit positive proportion of critical odd fibres. It supplies actual arithmetic information, but neither an all-zero theorem nor WD's long-prefix low-set criterion. [MZF-PROPORTION] [WD-PROPORTION]

Fixed-shift logarithmic two-point Liouville cancellation is proved. The rate and growing-shift uniformity needed for a critical prefix estimate are not part of that statement. This is a useful arithmetic input with a precise quantifier boundary. [CHOWLA]

### Excluded production shortcuts and positive survivors

| Excluded mechanism | Scope of obstruction | Positive survivor |
|---|---|---|
| Increasing Gauss-monomial complexity to break `3/5` | The explicitly classified Möbius-signed pairing class. | Exact optimum and equality classification; focus on nonmonomial or incompletely completed transforms. [GAUSS] |
| Average away target phases and infer target cancellation | The average annihilates the target and reciprocal target in the stated construction. | Retain the reciprocal pair in a phase-sensitive observable before estimating. [AVERAGE] |
| Demand a near-unit long-mollifier moment at fixed power length | The formalized unit-coefficient, fixed-power-length near-unit target. | Subpower-in-length fixed-window receivers and less restrictive moment bounds remain meaningful. [LONG-MOMENT] [WD] |
| Infer geometry from two matching moments | Explicit split-band compressions match second/fourth moments with different singleton counts. | Use additional source information or higher invariants; the lower moments remain valid partial statistics. [CENSUS-AMBIGUITY] |
| Treat reflected cubic Gram terms as automatically nonnegative | Actual exponential-evaluation Gram data can have negative reflected cubic interference. | Preserve and estimate the signed interference rather than delete it. [GRAM-SIGN] |

## U — Uniform exclusion

The shared question is whether the arithmetic bound excludes every relevant defect: every aperture, order, height, scale or exceptional zero. A finite theorem may be strong and still leave this wall intact.

| Wall | Status and exact boundary | Remaining mathematical input |
|---|---|---|
| **U1. First overlap floor** | **Available:** full complex Weil floor `1/50000` at aperture `1881/5000`, and all block sizes at ratio at most `10609/5000`, cutoff `Q≥2`. [FLOOR] [BLOCK-FLOOR] | A larger actual floor. No full floor through radius two follows merely from Gamma comparisons. [GAMMA-CHARGES] [GAMMA-LAGS] |
| **U2. Finite overlap ladder** | **Available:** first Schur excess and first level are zero. **Open:** remaining levels needed for ratio three. [GREEN-FIRST] [GREEN-LADDER] | Prove `levelAt 2 4=0`, or another sufficient actual signed estimate. The first step used a fixed-aperture floor, not a reusable free contraction. |
| **U3. Global overlap/margin** | **Available:** exact additive-loss calculus and RH equivalence of a bounded global level/margin. [GREEN-LOSS] [GREEN-GLOBAL] [ACS] | A bound uniform in all scales and prime cutoffs, with the binding ceiling respected. |
| **U4. Critical-state exclusion** | **Available:** closed soft-logarithmic attainment; critical-state uniqueness up to sign, outerness, cyclicity, Laplace zero-freeness and sharp terminal-wall structure. [SOFT] [HF] [HF-OUTER] [HF-CYCLIC] [HF-BOUNDARY] [HF-WALL] | Exclude the actual positive-threshold critical state. None of the listed structural properties is the contradiction. |
| **U5. Universal tests/orders** | **Available:** complete moment, character, shift, heat-grid and charge criteria. [PA] [TH] [ECP] [ACT] [HCF] [GTA] | Their arithmetic inequalities for every required order/profile. Fixed order, finite rank or two sampling grids do not remove the universal quantifier. |
| **U6. Heat boundary** | **Available:** large forward monodromy, local collision permutations, fixed-positive-time real-zero horizons and finite Jensen rungs. [MONODROMY] [HEAT-TURN] [HEAT-HORIZON] [JENSEN-RUNG] | Control conjugation/branch data uniformly enough to reach time zero and unbounded height. [ZCG] |
| **U7. Finite exceptions / AAL** | **Available:** AAL is equality of total and tail abscissae; failure is a finite nonempty top layer; height-transport and prime-error formulations are exact. [AAL] [AAL-LAYER] [AAL-TRANSPORT] [AAL-OSCILLATION] | Prove arithmetic transport or exhibit a genuine exceptional layer with a strictly narrower tail. |
| **U8. Near-line concentration** | **Available:** the sech multiplicity envelope and a compensation theorem forcing nearby off-line mass from large critical multiplicity. [SECH] [COMPENSATION] | Exclude that compensating configuration; concentration/density bounds alone need not eliminate individual exceptions. |
| **U9. Arithmetic recurrence and topology** | **Available:** source-target recurrence and sub-unit topological gates characterize RH. [BAG] [TG] | Establish the required target-uniform recurrence or strict bound. Generic recurrence and integer winding alone are insufficient. |

### Excluded uniformity shortcuts and positive survivors

| Excluded mechanism | Scope of obstruction | Positive survivor |
|---|---|---|
| Fixed-rank charge-product gluing at ratio four | In the prescribed lowered comparison model, rank `r` fails once `H≥600(r+1)`. | Full coupling plus auxiliary charges remains possible; growing-rank response data are mathematically necessary in that model. [RANK-WALL] |
| Obtain the global arithmetic bound from a contact-only gap/curvature | The dilation process has no such gap; the floor-tree curvature mechanism is zero. | Full signed jets, contacts and pole contributions remain in the exact form. [TREE-GAP] [TREE-CURVATURE] |
| Demand a strictly positive margin uniform over all long windows | Under RH the long-window continuum margin tends to zero. | A finite lower bound, or the exact bounded-level criterion, is sufficient. [MARGIN-DECAY] [ACS] |
| Exclude the critical state by proving it unique or outer | These properties already hold in the alternative to RH. | Its weak equation, explicit wall energy and unique profile give a much more constrained arithmetic object to attack. [HF] [HF-OUTER] [HF-WALL] |
| Infer AAL from counting laws insensitive to finite edits | Integer-norm edit models retain such laws and finite exceptional layers. | Exact source/reflection defects identify additional invariants that a successful rigidity theorem must detect. [EDIT] [EDIT-REMOVE] [EDIT-DEFECT] |
| Infer reality from maximal signed monodromy | Odd nonreal-quartet count can force the full signed group. | The arithmetic conjugation-transport criterion remains a real target. [HEAT-ODD] [ZCG] |
| Take a global analytic square root of ξ | ξ has an odd-order zero. | Regional off-critical multiplicity descent is a distinct, unconstructed possibility; quartet-total parity is already automatic. [ROOT-WALL] [QUARTET-PARITY] |
| Realize the critical adelic Green matrix by a bounded inverse | The critical precision has no bounded right inverse, and the Green matrix has no bounded realization in the stated charge space. | The unbounded/form-domain theory survives; damping detects logarithmic energy. [HAT-INVERSE] [HAT-DOMAIN] |

U7 has three precise subproblems: finite-stratum rigidity, landing of a tail that approaches the line, and the specified asymptotic Deuring–Heilbronn implication. Their conjunction is AAL; none is supplied by the fixed MMD strip alone. [AAL-LANDING]

## R — Faithful realization and transport

The shared question is whether the constructed object is the actual arithmetic source and whether transfer preserves the obstruction. A correct model or exact reconstruction on a selected subspace can still fail here.

| Wall | Status and exact boundary | Remaining mathematical input |
|---|---|---|
| **R1. Full-divisor landing** | **Available:** many traces, Gram reconstructions, finite resolutions and approximation receivers. [APF] [WBF] [IRK] [W1C] | Source-derived identification of the entire ξ divisor, including multiplicity and hypothetical off-line zeros. |
| **R2. Source construction for candidate histories** | **Available:** Fock criticality and dark-history/price receivers, information accounting and depth identities. [SEC] [CDC] [FEL] [EWJ] | An actual arithmetic source/history with the required bound, endpoint admission and calibration. |
| **R3. Completion and normalization** | **Available:** exact jump, Gamma, root-number and scattering identities. [HATC] [SZ] [ARTIN] [PM] | Preserve these identities through any proposed new producer or realization; a pole/zero cancellation must be proved. |
| **R4. Arithmetic Galois constraints** | **Available:** prime-trace field, algebraic normal extension, faithful action, weight/orbit criterion and reflection square-class obstruction. [TRACE-FIELD] [WEIGHT-ORBIT] [REFLECTION] | Independent restrictions forcing the needed weights/reflection action. A small conjugate-pair orbit is not criticality. |
| **R5. Heat/field comparison** | **Available:** both theories separately; no global fixed-degree heat factor. [MONODROMY] [HEAT-FACTOR] [FIBRE-FIELD] | A proved comparison preserving the arithmetic information needed for reality. Generic monodromy cannot simply be substituted for an arithmetic Galois group. |
| **R6. Absolute geometry** | **Available:** graph contacts, jets, planar Bézout and sharp constraints on geometric diagonals. [CONTACT] [CONTACT-JET] [BEZOUT] [SELF-PAIRING] | A global source-independent realization/index theorem with the exact counterterm. |
| **R7. Physical interpretation** | **Available:** modular/Bianchi arithmetic scattering and strip/decay equivalences. [PM] [RINGDOWN] | For AdS: a constructed bulk/boundary arithmetic dictionary and independently derived sharp decay, with complete divisor visibility. |
| **R8. Return/phase transport** | **Available:** strip-dependent S3 receiver; exact no-go for literal reversible RFHM sewing. [S3] [RFHM] | A source-faithful return transfer or controlled nonreversible phase law. BAG's target returns do not automatically become S3 identity returns. |

### Excluded realization shortcuts and positive survivors

| Excluded mechanism | Scope of obstruction | Positive survivor |
|---|---|---|
| Realize the measured couplings with nonnegative geometric self-pairings | Such a matrix has at least two positive squares on the specified large windows. | Negative geometric self-pairings of logarithmic size are necessary; the neutral diagonal attains the order on dyadic windows. [SELF-PAIRING] |
| Perfect the absolute square and retain all contacts | The perfected construction loses the required contact structure. | Nonperfect ghost/planar constructions preserve explicit prime contacts. [PERFECT] [CONTACT] |
| Select a global fixed-degree polynomial factor of the heat zeros | No continuous monic positive-degree factor exists over the forward cover. | Finite-fibre arithmetic equations and local analytic factors remain meaningful; they live over different bases/domains. [HEAT-FACTOR] [FIBRE-FIELD] |
| Replace the arithmetic object by a generic geometric model | Compact Selberg models possess actual finite off-line zeros from small eigenvalues. | The model provides a test for the extra arithmetic/archimedean rigidity required of a Riemann-specific construction. [SELBERG] |
| Use norm exhaustion as endpoint identification | The Euler–Wold blind lane can exhaust in norm while losing the endpoint obstruction. | An endpoint-sensitive source admission theorem remains the correct target. [EWJ] |
| Require literal reversible all-prime RFHM sewing | The specified reversible sewing is impossible. | A nonreversible law with an explicitly controlled defect may retain phase and grade. [RFHM] |

## Which walls are work, which are research?

Known-input assembly includes strip-to-Jensen specialization, exact finite ladder arithmetic, normalization transfers, finite source equations and evaluation of fully specified certificates. These tasks do not discharge P4, U3, U7 or R1. The [summary's work list](obstacles-summary.md#21--tasks-that-are-work-rather-than-new-mathematics) states the deliverables.

The principal shared research targets are an arithmetic producer outside the exhausted completion mechanism; a signed overlap estimate stable under scale; finite-exception rigidity; and a realization that proves rather than assumes its arithmetic constraint. The first two-prime retained-charge question in [§2.21](obstacles-summary.md#221--the-one-priority-question) has a concrete finite-aperture success criterion and a useful obstruction outcome.

<!-- source references -->
[MMD]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/QuasiRiemannHypothesis.lean#L1
[GAUSS]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/MoebiusSignedGaussPairingsEndAtThreeFifths.lean#L586
[DECOMPLETE]: ../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/TheWallIsThePriceOfCompletion.lean#L211
[MC]: ../../../formal/GaloisForLFunctions/RHTower/MobiusHilbertFormEquivalence.lean#L219
[WD]: ../../../formal/GaloisForLFunctions/MultiscaleMollifiedZetaField/TheWidthIsReadInOneWindow.lean#L485
[FU]: ../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorOneSidedPowerGapBootstrap.lean#L596
[CTF]: ../../../formal/GaloisForLFunctions/RHTower/ChronologicalRiemannEquivalence.lean#L414
[PBM]: ../../../formal/GaloisForLFunctions/RHTower/RegularizedLogZetaAbscissa.lean#L402
[CHMD]: ../../../formal/GaloisForLFunctions/RHTower/CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion.lean#L385
[WD-SHORT]: ../../../formal/GaloisForLFunctions/MultiscaleMollifiedZetaField/TwistedSecondMomentsBelowSquareRoot.lean#L128
[WD-BLOCK]: ../../../formal/GaloisForLFunctions/MultiscaleMollifiedZetaField/TheTwistedMomentFactorsOverBlocks.lean#L585
[LONG-MOMENT]: ../../../formal/GaloisForLFunctions/ArithmeticProduction/LongMollifiersImplyCriticalClustering.lean#L422
[WD-RAW]: ../../../formal/GaloisForLFunctions/ArithmeticProduction/LongIntegerPolynomialsSeeParity.lean#L1
[CENSUS]: ../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ZetaSamplingPrimePoleFourth.lean#L262
[ARTIN]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/EveryArtinLFunctionHasACompletionWithAFunctionalEquation.lean#L220
[MZF-PROPORTION]: ../../../formal/GaloisForLFunctions/MultiscaleMollifiedZetaField/TheTwistedMomentGivesAPositiveCriticalProportion.lean#L109
[WD-PROPORTION]: ../../../formal/GaloisForLFunctions/MultiscaleMollifiedZetaField/TheExponentOfTheMollifiedErrorIsRigid.lean#L605
[CHOWLA]: ../../../formal/GaloisForLFunctions/LogarithmicChowla/LogarithmicChowlaTheorem.lean#L90
[AVERAGE]: ../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/TheAverageRowIsBlindToTheTarget.lean#L1
[CENSUS-AMBIGUITY]: ../../../formal/GaloisForLFunctions/IncommensurableGaborPinching/SplitBandMomentAmbiguity.lean#L1
[GRAM-SIGN]: ../../../formal/GaloisForLFunctions/IncommensurableGaborPinching/ReflectedExponentialCubicInterference.lean#L304
[FLOOR]: ../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheEvenWeilFormHasAFloorAtAperture1881Over5000.lean#L340
[BLOCK-FLOOR]: ../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheFirstOverlapWindowHasAPositiveWeilFloorAtEveryBlockSize.lean#L1
[GAMMA-CHARGES]: ../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheGammaComparisonRetainsItsChargesThroughRadiusTwo.lean#L1
[GAMMA-LAGS]: ../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheGammaRemainderRetainsHigherLagsThroughRadiusTwo.lean#L1
[GREEN-FIRST]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheFirstOverlapStepHoldsAtEveryBlockSize.lean#L1
[GREEN-LADDER]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheExcessOfAnOverlapStepAndTheFourStepLadderToRatioThree.lean#L1957
[GREEN-LOSS]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheLossOfAnOverlapStepIsAdditiveBelowTheBindingEnergyOfTheMiddle.lean#L568
[GREEN-GLOBAL]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheExcessOfAnOverlapStepAndTheFourStepLadderToRatioThree.lean#L2178
[ACS]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/AUniformLowerBoundOnTheMarginOfTheWindowMatricesForcesTheRiemannHypothesis.lean#L505
[SOFT]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/SoftLogarithmicClosedAttainment.lean#L27
[HF]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalHalfLineStateIsUniqueUpToSign.lean#L96
[HF-OUTER]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineLaplaceMultiplierIsOuter.lean#L45
[HF-CYCLIC]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineStateIsCyclic.lean#L59
[HF-BOUNDARY]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineStateHasNoBoundaryLaplaceZero.lean#L149
[HF-WALL]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/CriticalTerminalWallEnergy.lean#L131
[PA]: ../../../formal/GaloisForLFunctions/RHTower/PrimeArchEndpointCalibratedHausdorffRH.lean#L92
[TH]: ../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaHermiteTraceFlag.lean#L250
[ECP]: ../../../formal/GaloisForLFunctions/RHTower/Representation/EndpointCharacterCriterion.lean#L62
[ACT]: ../../../formal/GaloisForLFunctions/ArithmeticCriticalityTheory/SingleShiftCompleteness.lean#L177
[HCF]: ../../../formal/GaloisForLFunctions/RHTower/XiGaussianHeatTwoPrimeSourceSampling.lean#L123
[GTA]: ../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaSchurQuarticSpectralDecayEquivalence.lean#L293
[MONODROMY]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheForwardMonodromyGroupHasIndexAtMostTwoInTheSignedPermutationsOfFiniteSupport.lean#L1
[HEAT-TURN]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheTurnAroundAnIsolatedDoubleCollisionOffTheCentreIsTheExchangeOfTwoPairs.lean#L131
[HEAT-HORIZON]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/HeatScaleRepulsion/TheExplicitHeightOfTheWeylHorizon.lean#L356
[JENSEN-RUNG]: ../../../formal/GaloisForLFunctions/VerifiedHeightRungs/TheJensenRungAtTheSaddleScale.lean#L117
[ZCG]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheForwardMonodromyDeterminesTheReflectionAndTheConjugationOfTheZeros.lean#L186
[AAL]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AsymptoticAbscissaSpectralGapAndTopAnnihilator.lean#L158
[AAL-LAYER]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/TheFailureOfTheAbscissaLawIsAFiniteLayer.lean#L33
[AAL-TRANSPORT]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/TheAbscissaLawsOfAZeroConfiguration.lean#L106
[AAL-OSCILLATION]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/TheOneOffsAreFiniteOscillationsOfThePrimeError.lean#L736
[SECH]: ../../../formal/GaloisForLFunctions/SquareRootThreshold/SechMultiplicityEnvelope.lean#L91
[COMPENSATION]: ../../../formal/GaloisForLFunctions/SquareRootThreshold/GaussianLocalCompensation.lean#L110
[BAG]: ../../../formal/GaloisForLFunctions/RHTower/ZetaDiscRecurrenceOnEveryClosedDiscOfTheStrip.lean#L294
[TG]: ../../../formal/GaloisForLFunctions/RHTower/FormationAnchoredCubicEndpoint.lean#L220
[RANK-WALL]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheBindingOfTheTwoHalvesOfAWindowOfRatioFourHasRankProportionalToTheBlockSize.lean#L929
[TREE-GAP]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/TheDilationProcessHasNoGap.lean#L174
[TREE-CURVATURE]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/TheFloorTreesHaveCurvatureZero.lean#L1
[MARGIN-DECAY]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/UnderTheRiemannHypothesisTheMarginOfALongWindowTendsToZero.lean#L442
[EDIT]: ../../../formal/GaloisForLFunctions/WorldsOfTheZeroConfiguration/AFiniteLayerWithATailOverTheRationalPrimes.lean#L488
[EDIT-REMOVE]: ../../../formal/GaloisForLFunctions/WorldsOfTheZeroConfiguration/AFiniteLayerCanBeEditedAway.lean#L48
[EDIT-DEFECT]: ../../../formal/GaloisForLFunctions/WorldsOfTheZeroConfiguration/FakeEditsWithSubpolynomialDefectEnergy.lean#L67
[HEAT-ODD]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/AnOddNumberOfQuartetsOfNonrealZerosAtARealTimeGivesEverySignedPermutation.lean#L372
[ROOT-WALL]: ../../../formal/GaloisForLFunctions/RHTower/GlobalParityWall.lean#L117
[QUARTET-PARITY]: ../../../formal/GaloisForLFunctions/RHTower/OrbitParityOffLine.lean#L116
[HAT-INVERSE]: ../../../formal/GaloisForLFunctions/HyperbolicArakelovTheory/TheCriticalAdelicGreenInverseIsUnbounded.lean#L94
[HAT-DOMAIN]: ../../../formal/GaloisForLFunctions/HyperbolicArakelovTheory/TheGreenDampingDetectsTheCompleteWeilFormDomain.lean#L169
[AAL-LANDING]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/TheLandingLaw.lean#L117
[APF]: ../../../formal/GaloisForLFunctions/RHTower/PaperPrimeFredholmReconstruction.lean#L39
[WBF]: ../../../formal/GaloisForLFunctions/HTGeometry/PaperGenealogyFredholmRecovery.lean#L107
[IRK]: ../../../formal/GaloisForLFunctions/RHTower/Deninger/DeningerMeyerPrimeRotationResolution.lean#L25
[W1C]: ../../../formal/GaloisForLFunctions/InfiniteRankPurityTheory/TheIndexIsSemicontinuous.lean#L96
[SEC]: ../../../formal/GaloisForLFunctions/RHTower/TimeOneGammaJetFockRHCriterion.lean#L398
[CDC]: ../../../formal/GaloisForLFunctions/RHTower/XiSourceHistoryPriceEscape.lean#L140
[FEL]: ../../../formal/GaloisForLFunctions/RHTower/PaperThetaObservationHistory.lean#L52
[EWJ]: ../../../formal/GaloisForLFunctions/RHTower/PaperEulerWoldDepthCompression.lean#L48
[HATC]: ../../../formal/GaloisForLFunctions/HyperbolicArakelovTheory/TheJumpTailFloorNeedsTheFullArithmeticNormalization.lean#L38
[SZ]: ../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiTransitionCoreAlignedGammaCompletion.lean#L380
[PM]: ../../../formal/GaloisForLFunctions/RingdownOfTheCubicCover/BianchiHorizonRingdownEquivalence.lean#L1
[TRACE-FIELD]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ThePrimeTraceGaloisGroupOfTheZeros.lean#L850
[WEIGHT-ORBIT]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheOrbitOfAZeroIsItsConjugatePairIffItsWeightLiesInThePrimeTraceField.lean#L1
[REFLECTION]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ThePrimeReflectionKernelOfTheZeros.lean#L455
[HEAT-FACTOR]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheHeatCoverOverTheForwardTimesIsConnectedAndHasNoPolynomialFactor.lean#L125
[FIBRE-FIELD]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheFieldOfCompleteFibreTraces.lean#L409
[CONTACT]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheFrobeniusGraphsMeetInThePrimes.lean#L98
[CONTACT-JET]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/WeilsOffDiagonalIsContactsPlusJets.lean#L125
[BEZOUT]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/BezoutIsAnEqualityOnThePlanarSquare.lean#L124
[SELF-PAIRING]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheCouplingsOfAWindowAreNotMixedAreasAndTheIndexForcesLogarithmicSelfPairings.lean#L268
[RINGDOWN]: ../../../formal/GaloisForLFunctions/RingdownOfTheCubicCover/UnconditionalScatteringResonanceBounds.lean#L1
[S3]: ../../../formal/GaloisForLFunctions/SignFreePurityMechanisms/HomogeneousReturnTransferImpliesStripCollapse.lean#L35
[RFHM]: ../../../formal/GaloisForLFunctions/RHTower/JointAncestryAllPrimeReversibleRFHMSewingNoGo.lean#L132
[PERFECT]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/APerfectSquareKeepsNoContact.lean#L81
[SELBERG]: ../../../formal/GaloisForLFunctions/CompactHyperbolicSurfaces/SmallEigenvalueZeta.lean#L113
