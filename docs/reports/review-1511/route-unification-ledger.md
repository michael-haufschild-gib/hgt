# Route unification ledger

The routes read three invariants of one object, the zero configuration of `ξ`. Each route is a face of one of three problems: **move the width**, **empty the index**, **close the tail**. This is stronger than the observation that the routes' terminal statements are equivalent to RH: inside each face the routes share an exact invariant, and several routes are formally the same ruler. Evidence conventions: [route report](route-obstacles.md), [working log](../../../logs/review-1511-working-log.md). [W] marks untracked working-tree modules.

Kinds of connection used below:

- **Ruler identity** — both routes are exact two-sided readings of the same number; by the ruler calculus every bound, seed and lever passes between them with no loss [MEASURING] [LEVERTRANSPORT].
- **Invariant identity** — both routes compute the same integer or set (an index, a layer, a divisor).
- **Quantitative transfer** — a theorem moves a bound with stated losses.
- **Endpoint equivalence** — both full statements are RH, with no transfer of partial estimates.
- **Proposed bridge** — a missing theorem.

## The three faces

| Face | Invariant | RH | Unconditional value | Why the face does not close by itself |
|---|---|---|---|---|
| **W — width** | `w = sup |Re ρ − ½|` | `w = 0` | `w ≤ 3/8` [MMD_STRIP] | Readings do not move the number; no lever is proved; the Gauss class ends at `3/5`; levers need the functional equation and the Dirichlet series together [MEASURING] [WALLGEN] [EULERWORLD] [COSH]. |
| **I — index** | `κ = #` distinct zeros right of the line | `κ = 0` | counted exactly by windows and packets [INDEXLAW] [INDEX] | Each finite stage sees zeros only to a finite height; a finite positive `κ` occurs for compact Selberg zeta functions with Euler product and functional equation. |
| **T — tail** | `Θ∞`, the top layer, landing | ZAL ∧ AAL, i.e. ZAL ∧ `FiniteOffLine → RH` ∧ Landing [THREEATOMS] | `Θ∞ < 1` ⇔ `Θ < 1` [QUASITAIL] | Fakes realize the failure of each atom separately; Euler worlds realize every pair `Θ∞ < Θ < 2/3` [TWOTHIRDSWORLD]. |

The faces meet only at RH: `w = 0 ⇔ κ = 0 ⇔ ZAL ∧ AAL`. Off RH they separate into three worlds: **F** (`0 < κ < ∞`, the finite stratum), **S** (ZAL holds, Landing fails, `κ = ∞`), **D** (ZAL fails, `Θ∞ > ½`). The width face sees world D through `Θ∞ ≤ Θ`; the index face sees world F as a finite index; only the tail face distinguishes S.

## Routes on the faces

| Face | Exact rulers / invariant computers | Receivers at the RH endpoint | Shared object | What remains distinct |
|---|---|---|---|---|
| **W** | Zero abscissa, Möbius prefix at one height, unit window, zeros of `M_X`, signal, two-end state [RULERS]; WL [WL]; WD long moments [WD-LONG]; PBM [PBM]; SRT [SRT]; RW logarithmic-energy floor [LOGENERGY]; ACS margin law and its doubling factor at polynomial block size [MARGINRULER] [DOUBLING] [W]; cubic-probe correction abscissa [RUNG] [W]; PM strip [ADS]; JAS level via the signal [SIGNAL-JAS] | MC [MC], FU [FU], CFC [CFC], RP [RP], SQF [SQF], TT [TT], CHMD [CHMD], LI [LI], RB [RB], SZ [SZ], AIP [AIP], CTF [CTF] [BSY] | `w`; on the rulers literally the same number. Heat: `Λ ≤ w²/2` is a half ruler [NEWMAN]. | Receivers at exponent zero have no rate dictionary in Lean; their partial estimates do not transfer. Smoothing, one-sidedness and schedules differ. |
| **I** | Neutral windows (index `≤ 1 + κ`) [INDEXLAW]; real packets (index `= κ`) [INDEX]; SC glued index; HF finite threshold ⇔ `κ > 0` [HF]; RW index growth at null modes [NULLMODES]; TG integer count [TG]; W1C index-one approximants [W1C] | EWU, OWU, ACT [ACT], HAT-C [HATC], RN [RN], ECP [ECP], TH [TH], PA [PA], GTA [GTA], HCF [HCF], XN [XN], ACS margin [ACS] | `κ` and the Weil form; every sector sign is `κ = 0` restricted to a test class. | A finite aperture, rank, flag or degree is a finite stage; sector signs are not quantitatively comparable. |
| **T** | Finite top layer [AAL-LAYER]; three atoms [THREEATOMS]; landing TFAE [LANDING-TFAE]; Jensen nonreal counts increase to the total off-line multiplicity [JENSENCOUNT]; heat counts `N(t)` [HEAT-UNIFORM]; IWT recurrence [IWT] | BAG [BAG], ZCG [ZCG], PTR [PTR], SC/JAS shell signs ⇒ AAL [AKLT], S3 [RETURNRH], CTF | layers, tails, recurrence and heat counts of the same divisor | Tail laws are not interchangeable: one off-line zero falsifies RH but not AAL. |

The 12 candidates sit on the same faces: SEC, CDC/BSH, APF, EGC, EWJ, FEL, WBF on I (detectors of the divisor); IRK, MSC on I through algebraic counts; RFHM, W1C on I/T; S3 on T, where it reduces to RH itself [RETURNRH].

## Proved bridges

### 1. The width face is one ruler (ruler identity)

A ruler of `w` is a family `P β` with `w ≤ β ⇔ P β`; its readings are exactly the bounds of `w`, two rulers agree reading by reading, and a lever on one ruler is a lever on every ruler [RULERS] [MEASURING] [LEVERTRANSPORT]. The rulers in Lean include the zero abscissa, the Möbius polynomial at one height, one unit window, the zeros of `M_X`, the signal of the zeta kernel, the two-end antisymmetric state [RULERS], the Weil floor in the logarithmic energy [LOGENERGY], the margin law of the neutral windows at block sizes `K¹⁰ ≤ ρ(K) ≤ K^A` [MARGINRULER] [W], and the two-sided dictionaries of WL, WD, SRT and PBM [WL] [WD-LONG] [SRT] [PBM]. The seed is instantiated on each: `Λ ≤ 9/128`, heat threshold `≤ 3/64`, `M(n) = O(n^β)` for `β > 7/8`, rates `3/8` on prefixes, windows, moments, signal and states [NEWMAN] [HEATTHR] [MERTENS78] [RULERS].

**Consequence.** Every W-route needs the same missing object: a lever or a second seed. Improving one W-route's estimate below `3/8` improves all of them simultaneously; no W-route is closer to RH than another.

### 2. The index face carries the width (invariant identity plus ruler)

The neutral part of the window `(R, (3K+1)R]` has at most one negative square after a shift; the depth of its second negative square sinks at the rate of the width: for `θ ≥ w` the shift `C(1 + log K)²K^θ(1 + log R)` suffices at every block size, `C K^{θ+ε}` at block sizes polynomial in `K` [MARGINDEPTH] [MARGINPOLY], and the infimum of the admissible rates at block sizes `K¹⁰ ≤ ρ(K) ≤ K^A` equals `w` [MARGINSINF] [W]; the best doubling factor of the margin is `2^w` [DOUBLING] [W]. A bounded margin on all windows is RH [ACS]. So the integer `κ` (how many) and the number `w` (how far) are read by the same finite matrices: the index is the number of bound states beyond one, the width is the rate at which the second one sinks.

**Limit.** The factor `1 + log R` at large block size is the possible clustering of off-line zeros at the resolved height; the exact all-block-size ruler is open (wall U9).

### 3. Tail atoms (invariant identity)

| Statement | Content |
|---|---|
| AAL | `Θ = Θ∞`; equivalently zero transport to arbitrarily large heights [AAL] |
| ¬AAL | a finite nonempty top layer [AAL-LAYER] |
| `FiniteOffLine → RH` | real packet index `0` or `∞` [INDEX] |
| Landing | ZAL ⇒ finitely many off-line zeros; equivalently a Hadamard threshold bounded as `σ ↓ ½` [LANDING-TFAE] |
| RH | ZAL ∧ `FiniteOffLine → RH` ∧ Landing [THREEATOMS]; under AAL, RH ⇔ ZAL [AKLT] |

The finite stratum is an index statement (I) and a tail statement (T) at once: it is the bridge between these two faces, and the open bridge.

### 4. Galois structure and heat (finite-window identity)

Arithmetic automorphisms act on continued finite windows of zeros as heat monodromies [HEAT-FINITE]; no whole-fibre identification exists [HEAT-NOGO]. The prime-trace fields read the index face through the weight criterion: `Re ρ = ½` iff `p^{2Re ρ} ∈ B` and some automorphism sends `ρ ↦ 1 − ρ` [REFLECTION]; conjugation is central iff every ordinate value lies in `B` [CONJCENTRAL]; an orbit leaves its quartet only through another off-line quartet of the same ordinate [LEAVEQUART]. These are identities of the configuration, not exclusions.

### 5. Physics reads the width

The two-boundary AdS correlator is analytic on the strip `0 < |Im ω| < δ` iff all zeros satisfy `Re ρ ≤ 1 − 2δ` [ADS]: the strip width is a ruler of `w` (`δ = ¼ − w/2`), so `δ = 1/16` is the seed. The Bianchi analogue reads the product `ζ·L(χ₋₃)` [BIANCHI]. Causal, Euler, FE, passive and unitary prime-2 deformations have thresholds tending to zero [ADS-NOGO]: the physical axioms are rulers' hypotheses, not levers.

### 6. The producer acts on the width only

The Möbius-signed Gauss pairings act on the abscissa as affine frames `b ↦ (c + b)/k`; their towers converge to Cantor-series values between the extreme centres, `≥ 3/5` [GAUSS] [MIXED]. The cubic frame is itself a ruler between two abscissas: the correction has abscissa `(3 + Θ_rung)/6` [RUNG] [W]. The signal ruler carries a signal bound to joint-ancestry positivity levels [SIGNAL-JAS]. No producer theorem acts on `κ` or on the tail.

## Distinctions that no theorem removes

| Pair | Why they stay distinct |
|---|---|
| W at positive rate ↔ I | A bound `w ≤ β < 3/8` says nothing about whether `κ` is finite. |
| I ↔ T (finite stratum) | Finite positive `κ` is realized with Euler product and functional equation (compact Selberg zeta); `FiniteOffLine → RH` needs `ζ`'s arithmetic. |
| W ↔ T without the functional equation | Euler worlds realize any `Θ∞ < Θ < 2/3`: no function `G(Θ∞)` bounds `Θ` below `2/3` on that class [TWOTHIRDSWORLD]. |
| Receivers at exponent zero ↔ rulers | An RH-equivalent endpoint with no rate dictionary transfers no partial estimate. |
| Arithmetic Galois ↔ heat | Finite windows only [HEAT-NOGO]. |

## Proposed bridges

| Bridge | Faces | Available pieces | Missing theorem |
|---|---|---|---|
| **A lever** | W | ruler calculus; worlds theorems; halving descent as a configuration-specific forcing law [HALVING] | One map `T` with `T(b) < b` proved for `ζ`, using the Dirichlet series and the functional equation together. |
| **Doubling law from the gluing data** | W via I | margin and doubling rulers (best factor `2^w`), unconditional rate `3/8`, Green calculus, first-step dipole [MARGINSINF] [DOUBLING] [MARGIN38] [GREEN] [DIPOLE] | A factor `λ < √2` derived from the gluing data alone. |
| **Clustering law** | W ↔ I at all block sizes | margin converse with `1 + log R`, sampling in logarithmic energy [MARGINDEPTH] [SAMPLING] | A uniform bound on deep off-line zeros per unit window. |
| **Finite stratum** | I ↔ T | packet index dichotomy; filters and cofactors; world-I edits [INDEX] [COFACTORS] [WORLDI] | Exclude finite positive `κ` for `ζ`. |
| **Landing** | T | landing TFAE [LANDING-TFAE] | A uniform Hadamard threshold for `ζ`. |
| **Sign of `G₊`** | T (heat) | off-centre forward collision; isolated double collision criterion [OFFCENTRE] [DOUBLECOLL] | An isolated double collision off the centre. |
| **Selecting gates** | W (physical) | Euler–FE rigidity with decaying defect [RIGIDITY]; prime-2 deformations [ADS-NOGO] | A dynamical principle that forces integral unit-multiplicity gates and a rate. |

The highest-value assembly shares one independently proved partial input across faces. Chaining RH-equivalent endpoints through RH supplies nothing; chaining rulers supplies a ruler. The [summary](obstacles-summary.md) develops the assemblies and the research questions.

<!-- source references -->
[AAL]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/TheAbscissaLawsOfAZeroConfiguration.lean#L106
[AAL-LAYER]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/TheFailureOfTheAbscissaLawIsAFiniteLayer.lean#L33
[ACS]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/AUniformLowerBoundOnTheMarginOfTheWindowMatricesForcesTheRiemannHypothesis.lean#L505
[ACT]: ../../../formal/GaloisForLFunctions/ArithmeticCriticalityTheory/SingleShiftCompleteness.lean#L177
[ADS]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/TheEternalAdSPrimeMarkedDictionary.lean#L884
[ADS-NOGO]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/CausalIdentitiesCannotForceQuarterRingdown.lean#L1600
[AIP]: ../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/TheCompensatedRemainderOfTheFullLedger.lean#L878
[AKLT]: ../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/PrimeTowersAndConeCouplingProduceAsymptoticAbscissaLaw.lean#L306
[BAG]: ../../../formal/GaloisForLFunctions/RHTower/ZetaDiscRecurrenceOnEveryClosedDiscOfTheStrip.lean#L294
[BIANCHI]: ../../../formal/GaloisForLFunctions/RingdownOfTheCubicCover/EternalBianchiBoundaryDictionaryAndWardObstruction.lean#L469
[BSY]: ../../../formal/GaloisForLFunctions/RHTower/BalazardSaiasYorCriterionEquivalence.lean#L217
[CFC]: ../../../formal/GaloisForLFunctions/RHTower/CCM/CCMFirstClockTailLowerBoundCompleteness.lean#L1089
[CHMD]: ../../../formal/GaloisForLFunctions/RHTower/CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion.lean#L385
[COFACTORS]: ../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheGrowingFilterReachesPolynomiallyManyCofactors.lean#L1
[CONJCENTRAL]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ConjugationIsCentralAtAZeroIffItsOrdinateValueLiesInThePrimeTraceField.lean#L279
[COSH]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L138
[CTF]: ../../../formal/GaloisForLFunctions/RHTower/ChronologicalRiemannEquivalence.lean#L414
[DIPOLE]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheDipoleOfWeilsGreenMatrixCarriesTheFirstOverlapStep.lean#L364
[DOUBLECOLL]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheTurnAroundAnIsolatedDoubleCollisionOffTheCentreIsTheExchangeOfTwoPairs.lean#L162
[DOUBLING]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestDoublingFactorOfTheMarginIsTwoToTheWidth.lean#L217
[ECP]: ../../../formal/GaloisForLFunctions/RHTower/Representation/EndpointCharacterCriterion.lean#L62
[EULERWORLD]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L77
[FU]: ../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorOneSidedPowerGapBootstrap.lean#L596
[GAUSS]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/MoebiusSignedGaussPairingsEndAtThreeFifths.lean#L595
[GREEN]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheContinuumGreenKernelIsTheLimitOfTheTowerAndIsNegativeOnlyAlongTheCharge.lean
[GTA]: ../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaSchurQuarticSpectralDecayEquivalence.lean#L293
[HALVING]: ../../../formal/GaloisForLFunctions/ArithmeticHolographyOfTheModularHorizon/HalvingDescentAndShimuraZeros.lean#L40
[HATC]: ../../../formal/GaloisForLFunctions/HyperbolicArakelovTheory/TheJumpTailFloorNeedsTheFullArithmeticNormalization.lean#L38
[HCF]: ../../../formal/GaloisForLFunctions/RHTower/XiGaussianHeatTwoPrimeSourceSampling.lean#L123
[HEAT-FINITE]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheArithmeticGroupActsOnContinuedWindowsOfZerosAsHeatMonodromy.lean#L81
[HEAT-NOGO]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheArithmeticGroupIsAHeatMonodromyOnFiniteWindowsButNotOnAFibre.lean#L62
[HEAT-UNIFORM]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/AUniformSpecializationOfTheOffLineZerosForcesThemToBeFinite.lean#L29
[HEATTHR]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L162
[HF]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalHalfLineStateIsUniqueUpToSign.lean#L96
[INDEX]: ../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheFiniteStratumIsThePacketIndexDichotomy.lean#L85
[INDEXLAW]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheIndexOfTheNeutralPartIsOnePlusTheNumberOfZerosRightOfTheLine.lean#L166
[IWT]: ../../../formal/GaloisForLFunctions/InfiniteRankWeilTheory/TheInfiniteRankWeilProof.lean#L64
[JENSENCOUNT]: ../../../formal/GaloisForLFunctions/FiniteFreeProbability/JensenCountsOffLineZeros.lean
[LANDING-TFAE]: ../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheLandingLawForZeta.lean#L145
[LEAVEQUART]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/AnOrbitLeavesItsQuartetOnlyThroughAnotherOffLineQuartetOfTheSameOrdinate.lean#L43
[LEVERTRANSPORT]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L85
[LI]: ../../../formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockGrowthLaw.lean#L165
[LOGENERGY]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWidthIsTheRateOfTheWeilFloorInTheLogarithmicEnergy.lean#L428
[MARGIN38]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesSinksAtTheRateOfTheWidth.lean#L800
[MARGINDEPTH]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesSinksAtTheRateOfTheWidth.lean#L789
[MARGINPOLY]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesSinksAtTheRateOfTheWidth.lean#L810
[MARGINRULER]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesIsARulerAtPolynomialBlockSize.lean#L719
[MARGINSINF]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesIsARulerAtPolynomialBlockSize.lean#L741
[MC]: ../../../formal/GaloisForLFunctions/RHTower/MobiusHilbertFormEquivalence.lean#L219
[MEASURING]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L79
[MERTENS78]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L169
[MIXED]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/MixedTowersOfLeversStayAboveTheBestCentre.lean#L419
[MMD_STRIP]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/QuasiRiemannHypothesis.lean#L674
[NEWMAN]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L155
[NULLMODES]: ../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/NullModesForceApertureIndexGrowth.lean
[OFFCENTRE]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ACollisionAwayFromTheCentreExistsAtAForwardTime.lean#L625
[PA]: ../../../formal/GaloisForLFunctions/RHTower/PrimeArchEndpointCalibratedHausdorffRH.lean#L92
[PBM]: ../../../formal/GaloisForLFunctions/RHTower/RegularizedLogZetaAbscissa.lean#L402
[PTR]: ../../../formal/GaloisForLFunctions/RHTower/XiCosineShiftExceptionalPointCriterion.lean#L510
[QUASITAIL]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/QuasiRHIsATailLaw.lean#L34
[RB]: ../../../formal/GaloisForLFunctions/RHTower/RobinColossallyAbundantReduction.lean#L132
[REFLECTION]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ALiftOfTheReflectionIsConjugationExactlyWhereTheWeightLiesInThePrimeTraceField.lean#L55
[RETURNRH]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L254
[RIGIDITY]: ../../../formal/GaloisForLFunctions/EulerFETransportTheory/DecayingFunctionalEquationsDetermineThePrimes.lean#L486
[RN]: ../../../formal/GaloisForLFunctions/RHTower/CCM/CCMThetaGroundRHCriterion.lean#L49
[RP]: ../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePLinearFloorCriterion.lean#L478
[RULERS]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L55
[RUNG]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheCorrectionOfTheCubicProbeCarriesTheAbscissaOfItsRung.lean#L126
[SAMPLING]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TransformsSampledOnLogarithmicallyDensePoints.lean
[SIGNAL-JAS]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSignalExponentIsThePositivityLevel.lean#L165
[SQF]: ../../../formal/GaloisForLFunctions/RHTower/SquarefreeExponentialOneSided.lean#L605
[SRT]: ../../../formal/GaloisForLFunctions/SurfaceOfSpecZ/ScaleLocality/PrimeLogarithmicWindows.lean#L145
[SZ]: ../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiTransitionCoreAlignedGammaCompletion.lean#L380
[TG]: ../../../formal/GaloisForLFunctions/RHTower/FormationAnchoredCubicEndpoint.lean#L220
[TH]: ../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaHermiteTraceFlag.lean#L250
[THREEATOMS]: ../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheLandingLawForZeta.lean#L68
[TT]: ../../../formal/GaloisForLFunctions/RHTower/PaperWoldDirectedCovarianceRH.lean#L182
[TWOTHIRDSWORLD]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L92
[W1C]: ../../../formal/GaloisForLFunctions/InfiniteRankPurityTheory/TheIndexIsSemicontinuous.lean#L96
[WALLGEN]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/MixedTowersOfLeversStayAboveTheBestCentre.lean#L525
[WD-LONG]: ../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/LongMoebiusSecondMomentRigidity.lean#L659
[WL]: ../../../formal/GaloisForLFunctions/BiScaleUncertainty/WeilLagCriticalDeficitEndpointAndLimitLaw.lean#L868
[WORLDI]: ../../../formal/GaloisForLFunctions/WorldsOfTheZeroConfiguration/AFiniteLayerCanBeEditedAway.lean#L136
[XN]: ../../../formal/GaloisForLFunctions/RHTower/XiNewtonDiscSourceMargin.lean#L219
[ZCG]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheForwardMonodromyDeterminesTheReflectionAndTheConjugationOfTheZeros.lean#L186
