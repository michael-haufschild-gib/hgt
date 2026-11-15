# Route unification ledger

The routes read three invariants of one object, the zero configuration of `ξ`. Each route is a face of one of three problems: **move the width**, **empty the index**, **close the tail**. Inside each face the routes share an exact invariant, and many are formally the same ruler. A fourth layer, **selection**, is common to all faces: every mechanism that closes a face must fail on the worlds that lack one structure of `ζ`. Evidence conventions: [route report](route-obstacles.md), [fact log](../../../logs/review-1511-frontier-facts.md); [S] = tagged unintegrated by the frontier map, [W] = untracked file, [D] = deduction of this ledger.

Kinds of connection:

- **Ruler identity** — both routes are exact two-sided readings of the same number; every bound, seed and lever passes between them with no loss [MEASURING] [LEVERTRANSPORT].
- **Invariant identity** — both routes compute the same integer, threshold or set.
- **Quantitative transfer** — a theorem moves a bound with stated losses.
- **Endpoint equivalence** — both full statements are RH, with no transfer of partial estimates.
- **Proposed bridge** — a missing theorem.

## The three faces

| Face | Invariant | RH | Unconditional value | Why the face does not close by itself |
|---|---|---|---|---|
| **W — width** | `w = sup |Re ρ − ½|` | `w = 0` | `w ≤ 3/8` [MMD_STRIP]; `w ≤ 8999/24000` written [WIDTHSUB] [S] | Readings do not move the number; no lever is proved; the producer's frames stop at `3/5` and its estimates at `7/8`; a lever must use the Ramanujan property [MEASURING] [WALLGEN] [VERTEXPOS] [PAIRS]. |
| **I — index** | `κ = #` distinct zeros right of the line; its threshold `W₀ = inf_A windowThreshold(A)` | `κ = 0`, `W₀ = ∞` | counted exactly by windows and packets [INDEXLAW] [INDEX] | Each finite stage sees zeros to a finite height; a prime-2 deformation with off-line zeros passes the certified aperture [P2LOG2] [S]; compact Selberg zeta functions have finite positive `κ` [SMALLEIG]. |
| **T — tail** | `Θ∞`, the top layer, landing | ZAL ∧ `FiniteOffLine → RH` ∧ Landing [THREEATOMS] | `Θ∞ < 1` ⇔ `Θ < 1` [QUASITAIL] | Fakes realize each atom's failure; Euler worlds realize `Θ∞ < Θ < 2/3` [TWOTHIRDSWORLD]. |

The faces meet only at RH: `w = 0 ⇔ κ = 0 ⇔ W₀ = ∞ ⇔` ZAL ∧ AAL. Off RH they separate into three worlds: **F** (`0 < κ < ∞`), **S** (ZAL, Landing fails), **D** (ZAL fails). In every one of them the half-line state undergoes a Hawking–Page transition at the finite `W₀` [HPTRANS] [S].

## Routes on the faces

| Face | Exact rulers / invariant computers | Receivers at the RH endpoint | Shared object | What remains distinct |
|---|---|---|---|---|
| **W** | Zero abscissa, prefix, unit window, zeros of `M_X`, signal, two-end state [RULERS] [WD] [SIGNAL-WIDTH]; WL [WL]; WD long moments and their slope loss [WD-LONG] [SLOPE]; PBM [PBM]; SRT [SRT]; log-energy floor [LOGENERGY]; margin and doubling [MARGINSINF] [DOUBLING]; squarefree quotient on `[½, 9/16)` [SQFRULER]; cubic-probe correction [RUNG]; PM strip [ADS]; JAS level via the signal [SIGNAL-JAS] | MC [MC], FU [FU], CFC [CFC], RP [RP], SQF [SQF], TT [TT], CHMD [CHMD], LI [LI], RB [RB], SZ [SZ], AIP [AIP], CTF [CTF] [BSY], PRIMELAG [PRIMELAG] | `w`; on the rulers literally the same number. Heat time is a half ruler, `Λ ≤ w²/2` [NEWMAN], and no lower bound in `w` alone exists [HEATSPACING]. | Receivers at exponent zero have no rate dictionary; their partial estimates do not transfer. |
| **I** | Neutral windows [INDEXLAW]; packets [INDEX]; SC glued index; HF threshold and Hawking–Page point [HF] [HPTRANS] [S]; null modes [NULLMODES]; TG integer count [TG]; W1C and index-one realizations [W1C] [INDEXONE] | EWU, OWU, ACT [ACT], HAT-C [HATC], RN [RN], ECP [ECP], TH [TH], PA [PA], GTA [GTA], HCF [HCF], XN [XN], ACS margin and gap [ACS] [GAPRH] | `κ`, Weil's form, the threshold `W₀` | A finite aperture, rank, flag or degree is a finite stage; sector signs are not quantitatively comparable. |
| **T** | Finite top layer [AAL-LAYER]; three atoms [THREEATOMS]; landing TFAE [LANDING-TFAE]; finite oscillation and non-attainment [FINOSC] [NONATTAIN]; unit-gap form of AAL [UNITGAPAAL]; Jensen counts [JENSENCOUNT]; heat counts [HEAT-UNIFORM] [HEATUNIT]; IWT [IWT]; horocycle filters [HOROZAL] [HOROAAL] | BAG [BAG], ZCG [ZCG], PTR [PTR], SC/JAS shell signs ⇒ AAL [AKLT], S3 [RETURNRH] | layers, tails, recurrence, heat counts of one divisor | One off-line zero falsifies RH, not AAL. |

Candidates: SEC, CDC/BSH, APF, EGC, EWJ, FEL, WBF on I (detectors); IRK, MSC on I (algebraic counts); RFHM, W1C on I/T; S3 on T, where it is RH [RETURNRH].

## Proved bridges

### 1. The width face is one ruler (ruler identity)

The rulers listed above agree reading by reading; the seed is instantiated on each: `Λ ≤ 9/128`, heat threshold `≤ 3/64`, `M(n) = O(n^β)` for `β > 7/8`, rate `3/8` on prefixes, windows, moments, signal and states, slope loss `3/4`, doubling factors above `2^{3/8}` [NEWMAN] [HEATTHR] [MERTENS78] [RULERS] [SLOPE34] [DOUBLING38]. The written seed passes to all of them at once: every ruler jumps from `3/8` to `8999/24000` [AVOIDJUMP] [S]. **Consequence.** Every W-route needs the same missing object, a lever or a better seed; none is closer to RH than another.

### 2. The index face carries the width, and carries nothing more (invariant identity plus ruler)

The second negative square of the window of ratio `3K+1` sinks at rate `w` [MARGINDEPTH] [MARGINSINF]; the best doubling factor is `2^w` [DOUBLING]; RH ⇔ factor one ⇔ a constant level, and levels are bounded or polynomial [DOUBLINGONE] [LOSSDICHOT]. The gluing data of the windows — any finite prefix of contacts, every dyadic middle, both half-windows — support exactly the factor `√2`: a sub-Euler model shares all of them and has best factor `√2` [SQRT2] [SUBEULER] [S]. Contacts `k ≥ 3K+2` act only on the end-to-end block of a doubled window, and a factor below `√2` forces that block's prime form to be negative of order `√K` [TOPLOCAL] [TOPOCTAVE] [S]. [D] That form is a weighted prime sum over `(3K, 6K]`, a reading of `w`. **Consequence.** The window calculus is a complete finite model of the width and contains no producer: the index face reads `κ` and `w` but moves neither.

### 3. Tail atoms (invariant identity)

| Statement | Content |
|---|---|
| AAL | `Θ = Θ∞`; zero transport to arbitrarily large heights [AAL]; every line has `≤ 1` or infinitely many zeros to its right [UNITGAPAAL] |
| ¬AAL | a finite top layer [AAL-LAYER]; the prime error is a finite trigonometric oscillation attained on every late window [FINOSC] |
| `FiniteOffLine → RH` | packet index `0` or `∞` [INDEX] |
| Landing | ZAL ⇒ finitely many off-line zeros; bounded Hadamard threshold [LANDING-TFAE] |
| RH | ZAL ∧ `FiniteOffLine → RH` ∧ Landing [THREEATOMS]; under AAL, RH ⇔ ZAL [AKLT] |

The finite stratum is the bridge between I and T, and the open one.

### 4. Galois structure and heat (finite-window identity)

Arithmetic automorphisms act on continued finite windows as heat monodromies [HEAT-FINITE]; whole fibres are excluded [HEAT-NOGO]. `Re ρ = ½` iff `p^{2Re ρ} ∈ B` and an automorphism realizes the reflection [REFLECTION]. An isolated off-line quartet at a height without critical zero has a negative radicand at every prime, its square class in `B` is decided by the absence of partial flips, and its mixed traces are symmetric under the swap `(Re ρ − ½) ↔ i Im ρ` [REGIMEA] [PARTIALFLIP] [TRACEFACTOR]; a critical zero at the same ordinate confines the action to the Klein group [KLEIN]. These are identities, not exclusions.

### 5. Physics reads the width and the index threshold

The AdS two-boundary strip width `δ` is `¼ − w/2` [ADS]. The half-line confining problem has its Hawking–Page point at `W₀ = inf_A windowThreshold(A)`, the index-face threshold, and RH ⇔ the bare energy is nonnegative [HPTRANS] [HPEQUIV] [S]. Prime-2 deformations satisfy every physical axiom formalized, have decay thresholds `→ 0`, and pass the certified aperture [ADS-NOGO] [P2LOG2] [S]. **Consequence.** The physical routes are the W- and I-faces in thermal language; the axioms are hypotheses of rulers, and their only missing input is the temperedness of the gates.

### 6. The producer acts on the width only

Frames `b ↦ (c + b)/k` act on the abscissa; completed Gauss frames stay `≥ 3/5`; the Möbius sign alone allows `(k/2, k)` with centres `k/(2(k−1)) → ½` [GAUSS] [MIXED] [SIGNLINE] [SIGNWALL]; the cubic frame is a ruler between the correction and its rung [RUNG]. The estimate ladder has its published vertex at `7/8`, closes at `20999/24000` by rescaling [SUBSEED] [S], cannot go below `40535/46328` in this estimate system [FARKAS] [S], and has design floor `13/15` and Cauchy–Schwarz floor `5/6` [VERTEXPOS] [VERTEXFLOOR] [SAVING]. Every rung transfers to `ζ` and all Dirichlet `L` [LADDERTRANSFER]. No producer theorem acts on `κ` or on the tail.

### 7. Identity forcing is a ruler near the line

Exact forcing from `ζ`'s identities stops at the quartet [QUARTETFORCE]; coincidences `ζ(ρ) = ζ(ρ/k) = 0` force `Θ ≥ k/(k+1)` and are excluded for `k ≥ 7` by the written seed [ROOTCOINC] [S] [K7] [S]; Witt monomials, Brauer relations and shifted convolutions force nothing [WITTORD] [BRAUERCANCEL] [SHIFTMARGIN]. What survives is the squarefree quotient as a ruler on `[½, 9/16)` [SQFRULER]. Closure laws (right descent, right doubling) would place every real-zero-free configuration on the line [DESCENT] [RDOUBLE], and the band-forcing receivers turn any expanding forcing law into a lever [BANDFORCE] [COVERLEVERS]; no forcing law for `ζ` is proved. **Consequence.** The sign-free programme reduces, at present, to the W-face.

## The selection layer

| World | Structure it lacks | Face it defeats |
|---|---|---|
| Euler worlds [EULERWORLD] | functional equation | W below `2/3`; T (`Θ∞ < Θ`) |
| Cosh models [COSH] | Dirichlet series | W everywhere |
| Two-sided prime edits [EDIT] | arithmetic beyond the count | the seed |
| Shifted pairs [PAIRSABS] [TEMPERED] | Ramanujan bound | W in `[Θ, Θ + ½)` |
| Prime-2 deformations [P2FACTOR] [P2LOG2] | tempered gate at 2 | I at the certified apertures (`½log 2` for every `α`, `log 2` for `α` near `½`); physics |
| Compact Selberg zeta [SMALLEIG] | archimedean temperedness | I (finite positive `κ`) |
| Fake edits [EDITDEFECT] [RIGIDITY] | decaying FE defect | T (world I) |

[D] The last three rows are all non-tempered at one place, and a single Euler column is pure iff tempered [EULERCOLUMN]. Unit Euler parameters are the property that no Euler–FE countermodel of the corpus has and that no proved mechanism uses.

## Distinctions that no theorem removes

| Pair | Why they stay distinct |
|---|---|
| W at positive rate ↔ I | `w ≤ β < 3/8` says nothing about finiteness of `κ`. |
| I ↔ T (finite stratum) | Finite positive `κ` occurs with Euler product and functional equation (compact Selberg); `FiniteOffLine → RH` needs `ζ`'s arithmetic. |
| W ↔ T without functional equation | Euler worlds realize `Θ∞ < Θ < 2/3` [TWOTHIRDSWORLD]. |
| Receivers at exponent zero ↔ rulers | No rate dictionary; no partial transfer. |
| Arithmetic Galois ↔ heat | Finite windows only [HEAT-NOGO]. |
| Finite aperture ↔ `ζ` | Prime-2 deformations pass the same certificates [P2LOG2] [S]. |

## Proposed bridges

| Bridge | Faces | Available pieces | Missing theorem |
|---|---|---|---|
| **A lever** | W | ruler calculus; five worlds; band-forcing receivers [BANDFORCE] | One map `T` with `T(b) < b` proved for `ζ` using Dirichlet series, functional equation and unit Euler parameters. |
| **A better seed** | W | written seed `20999/24000` [SUBSEED] [S]; design floor `13/15` [BALANCED]; ladder transfer [LADDERTRANSFER] | The count `U^{1−δ}`; a pre-Cauchy–Schwarz saving. |
| **Sign-line frames** | W | Stickelberger pricing [SIGNPRICE] [SIGNLINE] | A completion of a Möbius-signed monomial of period `k ≥ 7` priced at `k/2`. |
| **Clustering law** | W ↔ I | margin converse with `1 + log R` [MARGINDEPTH] | A uniform bound on deep off-line zeros per unit window. |
| **Finite stratum** | I ↔ T | packet dichotomy; filters; world-I edits [INDEX] [COFACTORS] [WORLDI] | Exclude finite positive `κ` for `ζ`. |
| **Landing / non-attainment** | T | landing TFAE; non-attainment receivers [LANDING-TFAE] [NONATTAIN] | A uniform Hadamard threshold, or window non-attainment of the prime error. |
| **Sign of `G₊`** | T (heat) | off-centre collision; isolated double-collision criterion [OFFCENTRE] [DOUBLECOLL] | An isolated double collision off the centre. |
| **Selecting gates** | all | Euler column purity ⇔ temperedness [EULERCOLUMN]; prime-2 deformations [P2LOG2] [S] | An inequality for `ζ` that a non-tempered gate violates. |

Chaining RH-equivalent endpoints supplies nothing; chaining rulers supplies a ruler. The [summary](obstacles-summary.md) develops the assemblies and research questions.

<!-- source references -->
[AAL]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/TheAbscissaLawsOfAZeroConfiguration.lean#L106
[AAL-LAYER]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/TheFailureOfTheAbscissaLawIsAFiniteLayer.lean#L33
[ACS]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/AUniformLowerBoundOnTheMarginOfTheWindowMatricesForcesTheRiemannHypothesis.lean#L505
[ACT]: ../../../formal/GaloisForLFunctions/ArithmeticCriticalityTheory/SingleShiftCompleteness.lean#L177
[ADS]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/TheEternalAdSPrimeMarkedDictionary.lean#L884
[ADS-NOGO]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/CausalIdentitiesCannotForceQuarterRingdown.lean#L1600
[AIP]: ../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/TheCompensatedRemainderOfTheFullLedger.lean#L878
[AKLT]: ../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/PrimeTowersAndConeCouplingProduceAsymptoticAbscissaLaw.lean#L306
[AVOIDJUMP]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheAbscissaAvoidsAnIntervalBelowSevenEighths.lean#L186
[BAG]: ../../../formal/GaloisForLFunctions/RHTower/ZetaDiscRecurrenceOnEveryClosedDiscOfTheStrip.lean#L294
[BALANCED]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSevenEighthsGeometryIsAVertex.lean#L541
[BANDFORCE]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/ExpandingForcingLawsRulersAndTheRiemannHypothesis.lean#L154
[BRAUERCANCEL]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/WittMonomialsShiftedConvolutionsAndBrauerCancellation.lean#L497
[BSY]: ../../../formal/GaloisForLFunctions/RHTower/BalazardSaiasYorCriterionEquivalence.lean#L217
[CFC]: ../../../formal/GaloisForLFunctions/RHTower/CCM/CCMFirstClockTailLowerBoundCompleteness.lean#L1089
[CHMD]: ../../../formal/GaloisForLFunctions/RHTower/CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion.lean#L385
[COFACTORS]: ../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheGrowingFilterReachesPolynomiallyManyCofactors.lean#L1
[COSH]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L142
[COVERLEVERS]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/ExpandingForcingLawsRulersAndTheRiemannHypothesis.lean#L352
[CTF]: ../../../formal/GaloisForLFunctions/RHTower/ChronologicalRiemannEquivalence.lean#L414
[DESCENT]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/TheClosedConfigurationsOfHalvingAndDoubling.lean#L431
[DOUBLECOLL]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheTurnAroundAnIsolatedDoubleCollisionOffTheCentreIsTheExchangeOfTwoPairs.lean#L162
[DOUBLING]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestDoublingFactorOfTheMarginIsTwoToTheWidth.lean#L217
[DOUBLING38]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestDoublingFactorOfTheMarginIsTwoToTheWidth.lean#L191
[DOUBLINGONE]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheLossOfTheMarginIsBoundedOrPolynomial.lean#L81
[ECP]: ../../../formal/GaloisForLFunctions/RHTower/Representation/EndpointCharacterCriterion.lean#L62
[EDIT]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L186
[EDITDEFECT]: ../../../formal/GaloisForLFunctions/WorldsOfTheZeroConfiguration/TheWorldOneScenarioTable.lean#L38
[EULERCOLUMN]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/RamanujanIsRealityOfAnEulerColumn.lean#L91
[EULERWORLD]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L81
[FARKAS]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheTrueVertexBelowSevenEighths.lean#L328
[FINOSC]: ../../../formal/GaloisForLFunctions/FloorFreeArithmetic/ThePrimeNumberTheoremIsNotAttainedOnWindows.lean#L68
[FU]: ../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorOneSidedPowerGapBootstrap.lean#L596
[GAPRH]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheGroundEnergyOfAnApertureIsAGapOfEveryWindowInsideIt.lean#L408
[GAUSS]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/MoebiusSignedGaussPairingsEndAtThreeFifths.lean#L595
[GTA]: ../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaSchurQuarticSpectralDecayEquivalence.lean#L293
[HATC]: ../../../formal/GaloisForLFunctions/HyperbolicArakelovTheory/TheJumpTailFloorNeedsTheFullArithmeticNormalization.lean#L38
[HCF]: ../../../formal/GaloisForLFunctions/RHTower/XiGaussianHeatTwoPrimeSourceSampling.lean#L123
[HEAT-FINITE]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheArithmeticGroupActsOnContinuedWindowsOfZerosAsHeatMonodromy.lean#L81
[HEAT-NOGO]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheArithmeticGroupIsAHeatMonodromyOnFiniteWindowsButNotOnAFibre.lean#L62
[HEAT-UNIFORM]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/AUniformSpecializationOfTheOffLineZerosForcesThemToBeFinite.lean#L29
[HEATSPACING]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheHeatTimeIsTheWidthTimesTheSpacing.lean#L109
[HEATTHR]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L162
[HEATUNIT]: ../../../formal/GaloisForLFunctions/FloorFreeArithmetic/TheHeatFlowHasTheCountOfItsLimit.lean#L60
[HF]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalHalfLineStateIsUniqueUpToSign.lean#L96
[HOROAAL]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/TheOptimalHorocycleExponentAndEulerAnnihilators.lean#L1107
[HOROZAL]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/TheOptimalHorocycleExponentAndEulerAnnihilators.lean#L1090
[HPEQUIV]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ArithmeticHawkingPagePhaseStructure.lean#L352
[HPTRANS]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ArithmeticHawkingPagePhaseStructure.lean#L440
[INDEX]: ../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheFiniteStratumIsThePacketIndexDichotomy.lean#L85
[INDEXLAW]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheIndexOfTheNeutralPartIsOnePlusTheNumberOfZerosRightOfTheLine.lean#L166
[INDEXONE]: ../../../formal/GaloisForLFunctions/FloorFreeArithmetic/AnIndexOneRealizationIsAUnitGap.lean#L93
[IWT]: ../../../formal/GaloisForLFunctions/InfiniteRankWeilTheory/TheInfiniteRankWeilProof.lean#L64
[JENSENCOUNT]: ../../../formal/GaloisForLFunctions/FiniteFreeProbability/JensenCountsOffLineZeros.lean
[K7]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/EulerDilationAndRootCoincidenceExclusion.lean#L212
[KLEIN]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/GaloisClosureAndMixedTracesOfAnIsolatedQuartet.lean#L445
[LADDERTRANSFER]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheCubicCoverSpecializationOfTheBindingBin.lean#L344
[LANDING-TFAE]: ../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheLandingLawForZeta.lean#L145
[LEVERTRANSPORT]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L85
[LI]: ../../../formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockGrowthLaw.lean#L165
[LOGENERGY]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWidthIsTheRateOfTheWeilFloorInTheLogarithmicEnergy.lean#L428
[LOSSDICHOT]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheLossOfTheMarginIsBoundedOrPolynomial.lean#L106
[MARGINDEPTH]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesSinksAtTheRateOfTheWidth.lean#L789
[MARGINSINF]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesIsARulerAtPolynomialBlockSize.lean#L804
[MC]: ../../../formal/GaloisForLFunctions/RHTower/MobiusHilbertFormEquivalence.lean#L219
[MEASURING]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L79
[MERTENS78]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L169
[MIXED]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/MixedTowersOfLeversStayAboveTheBestCentre.lean#L419
[NEWMAN]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L155
[NONATTAIN]: ../../../formal/GaloisForLFunctions/FloorFreeArithmetic/ThePrimeNumberTheoremIsNotAttainedOnWindows.lean#L151
[NULLMODES]: ../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/NullModesForceApertureIndexGrowth.lean
[OFFCENTRE]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ACollisionAwayFromTheCentreExistsAtAForwardTime.lean#L625
[P2FACTOR]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/CausalIdentitiesCannotForceQuarterRingdown.lean#L95
[P2LOG2]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/PrimeTwoDeformedApertureLogTwoTest.lean#L278
[PA]: ../../../formal/GaloisForLFunctions/RHTower/PrimeArchEndpointCalibratedHausdorffRH.lean#L92
[PAIRS]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L295
[PAIRSABS]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L259
[PARTIALFLIP]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/GaloisClosureAndMixedTracesOfAnIsolatedQuartet.lean#L308
[PBM]: ../../../formal/GaloisForLFunctions/RHTower/RegularizedLogZetaAbscissa.lean#L402
[PRIMELAG]: ../../../formal/GaloisForLFunctions/InfiniteRankPurityTheory/ThePrimeLagIsPositiveDefiniteExactlyUnderRH.lean#L52
[PTR]: ../../../formal/GaloisForLFunctions/RHTower/XiCosineShiftExceptionalPointCriterion.lean#L510
[QUARTETFORCE]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/TheClosedConfigurationsOfHalvingAndDoubling.lean#L120
[QUASITAIL]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/QuasiRHIsATailLaw.lean#L34
[RB]: ../../../formal/GaloisForLFunctions/RHTower/RobinColossallyAbundantReduction.lean#L132
[RDOUBLE]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/TheClosedConfigurationsOfHalvingAndDoubling.lean#L549
[REFLECTION]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ALiftOfTheReflectionIsConjugationExactlyWhereTheWeightLiesInThePrimeTraceField.lean#L55
[REGIMEA]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/GaloisClosureAndMixedTracesOfAnIsolatedQuartet.lean#L247
[RETURNRH]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L254
[RIGIDITY]: ../../../formal/GaloisForLFunctions/EulerFETransportTheory/DecayingFunctionalEquationsDetermineThePrimes.lean#L486
[RN]: ../../../formal/GaloisForLFunctions/RHTower/CCM/CCMThetaGroundRHCriterion.lean#L49
[ROOTCOINC]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/EulerDilationAndRootCoincidenceExclusion.lean#L174
[RP]: ../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePLinearFloorCriterion.lean#L478
[RULERS]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L55
[RUNG]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheCorrectionOfTheCubicProbeCarriesTheAbscissaOfItsRung.lean#L126
[SAVING]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheRankTwoMultipleDirichletSeriesConvexityHull.lean#L830
[SHIFTMARGIN]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/WittMonomialsShiftedConvolutionsAndBrauerCancellation.lean#L426
[SIGNAL-JAS]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSignalExponentIsThePositivityLevel.lean#L165
[SIGNAL-WIDTH]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSignalExponentIsTheZeroAbscissa.lean#L212
[SIGNLINE]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheShortMoebiusMonomialsPayExactlyHalf.lean#L139
[SIGNPRICE]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheShortMoebiusMonomialsPayExactlyHalf.lean#L97
[SIGNWALL]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheShortMoebiusMonomialsPayExactlyHalf.lean#L157
[SLOPE]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestSlopeLossOfTheLongMomentsIsTwiceTheWidth.lean#L110
[SLOPE34]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestSlopeLossOfTheLongMomentsIsTwiceTheWidth.lean#L95
[SMALLEIG]: ../../../formal/GaloisForLFunctions/CompactHyperbolicSurfaces/SmallEigenvalueZeta.lean#L25
[SQF]: ../../../formal/GaloisForLFunctions/RHTower/SquarefreeExponentialOneSided.lean#L605
[SQFRULER]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/WittMonomialsShiftedConvolutionsAndBrauerCancellation.lean#L268
[SQRT2]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L149
[SRT]: ../../../formal/GaloisForLFunctions/SurfaceOfSpecZ/ScaleLocality/PrimeLogarithmicWindows.lean#L145
[SUBEULER]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L319
[SUBSEED]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/SubSevenEighthsZeroFreeHalfPlane.lean#L147
[SZ]: ../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiTransitionCoreAlignedGammaCompletion.lean#L380
[TEMPERED]: ../../../formal/GaloisForLFunctions/RHTower/NonTemperedShiftedZetaPairCountermodel.lean
[TG]: ../../../formal/GaloisForLFunctions/RHTower/FormationAnchoredCubicEndpoint.lean#L220
[TH]: ../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaHermiteTraceFlag.lean#L250
[THREEATOMS]: ../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheLandingLawForZeta.lean#L68
[TOPLOCAL]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheFloorGraphNormAndTopOctaveBlindnessOfWindowGluing.lean#L650
[TOPOCTAVE]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L663
[TRACEFACTOR]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/GaloisClosureAndMixedTracesOfAnIsolatedQuartet.lean#L372
[TT]: ../../../formal/GaloisForLFunctions/RHTower/PaperWoldDirectedCovarianceRH.lean#L182
[TWOTHIRDSWORLD]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L95
[UNITGAPAAL]: ../../../formal/GaloisForLFunctions/FloorFreeArithmetic/NonAttainmentGivesTheAbscissaLaw.lean#L117
[VERTEXFLOOR]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSevenEighthsGeometryIsAVertex.lean#L499
[VERTEXPOS]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSevenEighthsGeometryIsAVertex.lean#L333
[W1C]: ../../../formal/GaloisForLFunctions/InfiniteRankPurityTheory/TheIndexIsSemicontinuous.lean#L96
[WALLGEN]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/MixedTowersOfLeversStayAboveTheBestCentre.lean#L525
[WD]: ../../../formal/GaloisForLFunctions/MultiscaleMollifiedZetaField/TheWidthIsReadInOneWindow.lean#L85
[WD-LONG]: ../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/LongMoebiusSecondMomentRigidity.lean#L659
[WIDTHSUB]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/EulerDilationAndRootCoincidenceExclusion.lean#L60
[WITTORD]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/WittMonomialsShiftedConvolutionsAndBrauerCancellation.lean#L182
[WL]: ../../../formal/GaloisForLFunctions/BiScaleUncertainty/WeilLagCriticalDeficitEndpointAndLimitLaw.lean#L868
[WORLDI]: ../../../formal/GaloisForLFunctions/WorldsOfTheZeroConfiguration/AFiniteLayerCanBeEditedAway.lean#L136
[XN]: ../../../formal/GaloisForLFunctions/RHTower/XiNewtonDiscSourceMargin.lean#L219
[ZCG]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheForwardMonodromyDeterminesTheReflectionAndTheConjugationOfTheZeros.lean#L186
