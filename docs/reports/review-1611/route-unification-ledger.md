# Review 1611 — route unification ledger

Corpus: commit f3286e6206 with the working tree (16 November 2026). The ledger records which routes are faces of one problem, by the theorem that identifies them. Every Lean statement cited was read in source.

Grades are the frontier map's: **[L]** integrated, **[S]** source only (unfinished or unintegrated), **[K]** individually audited. **(src)** marks a statement read in the Lean source that has no grade of its own on the frontier map. *Readme* marks a statement taken from a programme README returned by the corpus search tool; it is not a Lean statement. *Reading* marks an interpretation of this report.

Companion reports: [routes and obstacles](route-obstacles.md) (route names and receivers), [obstacles summary](obstacles-summary.md) (open problems O1–O16), [walls ledger](walls-ledger.md) (walls P, R, U).

## 1. Result

The frontier map lists 39 live route formulations and 12 candidates. Under the identifications proved in Lean, and for the routes that have only a receiver under the reading stated in each group, they are faces of three statements about one configuration:

| Problem | Statement | Faces |
|---|---|---|
| **W — the width** | w = sup \|Re ρ − ½\| = 0 | every ruler (group A), every sign criterion (group B), every collision criterion (group D), every uniformity criterion (group E), every physical rate (group F) |
| **AAL — the abscissa law** | no line has a finite positive number of zeros to its right | group C |
| **ZAL — approach to the line** | the zeros approach the line, with landing | the second half of group C |

RH ⇔ W ⇔ ZAL ∧ AAL ([`riemannHypothesis_tfae`](../../../formal/GaloisForLFunctions/InfiniteRankWeilTheory/TheInfiniteRankWeilProof.lean#L64)). The routes differ in the input they accept:

| Family | Input a route accepts | What the identifications show |
|---|---|---|
| P | an estimate with cancellation | every estimate is a bound for w, and every bound for w is every estimate (group A); a lever valid on a class of models bites only where the class realizes no abscissa (§8) |
| R | a sign of a quadratic form, or the absence of its null vector | a sign with a loss of rate β is the bound w ≤ β; the sign without loss is w = 0; the null vector (critical state) exists exactly when w > 0 (bridges G1–G3, G10) |
| U | an exclusion or a statement uniform in an order | each finite stage is available; the uniform statement is w = 0, AAL or ZAL (groups C–E) |

## 2. Group A — one width, many rulers

**Common problem.** A ruler is a criterion that holds at exponent β exactly when w ≤ β. All rulers read one number; a bound proved in one is a bound in all ([`sub_three_eighths_ruler_jump`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheAbscissaAvoidsAnIntervalBelowSevenEighths.lean#L186) [L]). No ruler produces a bound.

| Ruler | Coordinate in which it reads w | Route | Lean |
|---|---|---|---|
| Mertens function, producer rate | a polynomial producer rate ⇔ M(n) = O(n^(1−σ)); M(n) = O(n^(7/8)) holds | MC | [`exists_hasRate_rpow_iff_mertens`](../../../formal/GaloisForLFunctions/ArithmeticAuxiliaryDynamics/TheRateAndTheMertensScaleCoincide.lean#L452), [`exists_mertens_le_seven_eighths_exact`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheAbscissaAvoidsAnIntervalBelowSevenEighths.lean#L229) |
| Squarefree power quotient | pole-free on Re s > β/2 ⇔ Θ ≤ β, β < 27001/48000 | SQF | [`squarefreePowerQuotient_poleFree_iff_zetaZeroAbscissa_le_sub`](../../../formal/GaloisForLFunctions/ZeroForcingCalculus/EulerDilationAndRootCoincidenceExclusion.lean#L309) |
| Long mollified moments | least slope loss = 2w | WD | [`zetaZeroWidth_le_of_slopeLaw`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestSlopeLossOfTheLongMomentsIsTwiceTheWidth.lean#L68), [`slopeLaw_sub_three_quarters`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheAbscissaAvoidsAnIntervalBelowSevenEighths.lean#L335) |
| Prime traces on logarithmic windows | w ≤ σ ⇔ one-sided bounds −K·p^σ | SRT | [`zetaZeroWidth_le_iff_bddBelow_primeDegrees`](../../../formal/GaloisForLFunctions/SurfaceOfSpecZ/TheWidthIsTheStepanovExponentAtThePrimes.lean#L909) |
| Even prime-trace moments | a_k/(2k) → w; the same for finite-monodromy bases | SRT, tensor powers | [`tendsto_momentExponent_div`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/ThePrimeTraceMomentsOfZetaReadTheWidthWithBaseLossAtMostOne.lean#L201), [`summable_classMomentTerm_iff`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/FiniteMonodromyIsARuler.lean#L121) |
| Valid levers | the wall of all levers valid for ζ is Θ | lever calculus | [`wall_validLevers_zeta`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/AWallAboveOneHalfIsAWorldOffTheLine.lean#L219) |
| Pulse ringdown on the modular surface | rate δ ⇔ no zero with Re ρ > 1 − 2δ | PM | [`zeroFreeStrip_iff_pulse_ringdown`](../../../formal/GaloisForLFunctions/BlackHoleRingdown/TheRingdownRateIsTheZeroFreeStrip.lean#L625) |
| Thermalization of Farey counts | the same strip | counting holography | [`zeroFreeStrip_iff_fareyCount_rate`](../../../formal/GaloisForLFunctions/CountingHolography/ThermalizationFasterThanTheSquareRootIsAZeroFreeStrip.lean#L486) |
| Floor of Weil's form in the logarithmic energy | w ≤ β ⇔ floor at rate β | RW | [`isRuler_logEnergyFloor`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWidthIsTheRateOfTheWeilFloorInTheLogarithmicEnergy.lean#L428) |
| Margin of the window matrices | infimum of margin rates = w | ACS | [`sInf_marginLaw_eq_zetaZeroWidth`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesIsARulerAtPolynomialBlockSize.lean#L804) |
| Doubling factor of the margin | infimum of factors = 2^w | ACS | [`zetaZeroWidth_le_logb_of_doublingLaw`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestDoublingFactorOfTheMarginIsTwoToTheWidth.lean#L178), [`exists_doublingLaw_lt_two_rpow_three_eighths_iff`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L771) |
| Decay of the critical state | ∫F²e^(−bu) < ∞ ⇒ every right zero has Re ρ ≤ (17 − b)/2; the seed gives averaged decay at every rate < 183001/24000 | ECS | [`criticalState_not_integrable_of_zero`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheDecayOfTheStateReadsTheZeros.lean#L316), [`criticalState_averaged_decay_beyond_barrier`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheAveragedStateDecaysAtTheRateOfTheZeros.lean#L701) |
| Remainder of the order-six unit layer | a remainder O(X^β) puts every zero of ζ·L(·, χ₋₃) with Re ρ > max(½, 3β−1) onto a zero of Λ₀ | OSM (MC support) | [`smoothedRemainder_forces_thetaSquare_zero`](../../../formal/GaloisForLFunctions/OrderSixMetaplecticTheory/TheSmoothedRemainderReadsTheZerosOfTheCubeZeta.lean#L316) |
| Return transfer on log² windows | the transfer ⇔ RH | S3 | [`homogeneousReturnWindowTransfer_iff_riemannHypothesis`](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheReturnTransferIsTheRiemannHypothesisUnderAStrip.lean#L44) |

**Members by receiver** (a bound at exponent ½ + ε implies RH or is equivalent to it): PBM, RB, SZ, TT, CTF, BAG, JAS. *Reading:* each is the endpoint w = 0 of a ruler of the table.

**The producer inside the group.** The only source of a bound is the estimate route. Its open steps are stages of half-power cancellation (O5), ordered by exponent: 13/15 (O1), 5/6 and 7/9 (O2), the branch below 7/9 (O2 with the remainder of P11), 2/3 (the frame), 3/5 (coupled towers, needs O3), k/(2(k−1)) and ½ (O4). The decay ruler of the critical state belongs here: a decay rate of the state beyond 17 − 2Θ is a new zero-free half-plane, so ECS improves the width only through family P.

## 3. Group B — one sign

**Common problem.** Nonnegativity of Weil's form on every test, in one of its coordinates; equivalently, absence of its null vector at every confinement.

| Face | Statement | Routes | Lean |
|---|---|---|---|
| Negative squares | number of negative squares = number of right zeros; Weil's archimedean state has negative index #right zeros + 1 | all of group B | [`pontryagin_law`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheHodgeDefectCountsTheRightZeros.lean#L490), [`negIndex_weilArchState_eq_rightZeros`](../../../formal/GaloisForLFunctions/AdelicKreinGeometry/WeilsArchimedeanStateCountsTheZeros.lean#L189) |
| Windows | RH ⇔ index one of every neutral window ⇔ every bound state has one sign | ACS, SC | [`riemannHypothesis_iff_forall_hermNegIndex_neutralWindow_eq_one`](../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheRiemannHypothesisIsOneNegativeSquareOfTheNeutralPartOfEveryWindow.lean#L622), [`riemannHypothesis_iff_forall_bound_state_one_sign`](../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/OneBoundStateIsTheHodgeIndexInequalityOnPositivePacketsWithoutCommonBlocks.lean#L536) |
| Positive packets | index ≥ 2 ⇔ two nonnegative packets without common blocks violate the Hodge inequality | ACS, AGZ | [`two_le_hermNegIndex_iff_exists_unbound_wells`](../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/OneBoundStateIsTheHodgeIndexInequalityOnPositivePacketsWithoutCommonBlocks.lean#L393) |
| Ground energy | μ(a) = floor of Weil's form on step packets inside a | RW, EWU/OWU, ACT | [`stepFloor_iff_le_groundEnergy`](../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheGroundEnergyOfAnApertureIsTheFloorOfWeilsFormOnTheWindowsInsideIt.lean#L500) |
| Onset aperture | onset = ⊤ ⇔ all zeros on the line | RW | [`onsetAperture_eq_top_iff_onLine`](../../../formal/GaloisForLFunctions/WindowVisibilityLaw/OnsetApertureAndPositivityDictionary.lean#L372) |
| Half-line form | RH ⇔ λ(R) ≥ 0 at every R | HF | [`riemannHypothesis_thermodynamic_equivalences`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ArithmeticHawkingPagePhaseStructure.lean#L352) [S] |
| Critical state | RH or a critical state at the finite threshold W₀; RH ⇔ the beyond-the-wall prime continuation | ECS, HF | [`riemannHypothesis_or_exists_criticalHalfLineGroundState`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/HalfLinePolarThresholdAndGroundStateOrthogonality.lean#L339), [`zetaBeyondTheWallPrimeContinuation_iff_riemannHypothesis`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheBeyondTheWallPrimeBalanceExcludesTheState.lean#L448) [S] |
| Kummer comparison | RH ⇔ reflection defect ≤ square mass; ⇔ nonnegative normalized graph degree on every scaling cycle | ACS | [`riemannHypothesis_iff_zeta_reflection_le_squareMass`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/Intersection/KummerActualZetaComparison.lean#L164), [`zeta_normalizedGraph_degree_nonneg_iff`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/Intersection/ZetaNormalizedGraphDegree.lean#L47) |
| Schur complements | RH ⇔ the Schur complement of every dyadic middle is nonnegative | ACS | [`riemannHypothesis_iff_forall_overlapSchur_nonneg`](../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheLossOfAnOverlapStepIsAdditiveBelowTheBindingEnergyOfTheMiddle.lean#L609) |
| Effectivity | Hodge index ⇔ an effectivity with Riemann–Roch and ampleness | ACS | [`exists_effectivity_iff_hodgeIndex`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HodgeIndexFromEffectivity.lean#L102) |
| Count | a form is the Tate limit of a count ⇔ it is nonnegative | counting holography | [`exists_count_tateLimit_iff`](../../../formal/GaloisForLFunctions/CountingHolography/TheCountDoorOfACurveAndOfZ.lean#L39) |
| Reflection Krein form | at most one negative square, zero at a critical zero, one off the line | PM | [`tentReflectionKrein_index`](../../../formal/GaloisForLFunctions/ArithmeticHolographyOfTheModularHorizon/TheReflectionKreinFormCountsTheOffLineResonances.lean#L244) |

**Members by receiver only:** WL, CHMD, TH, RN, GTA, AIP, ECP, PA, LI, HCF, FU, CFC, RP, HAT-C, and the candidates SEC, CDC/BSH, EWJ, MSC, RFHM, W1C, WBF, IRK. *Reading:* each asks for the sign of the same form on a subfamily of tests.

**What distinguishes the faces.** The certified range (aperture log 2, ratio three, rank 14, order 200, n ≤ 314), and, for ECS, the list of exact properties the null vector would have to carry. None of the certificates is a consequence of another in Lean.

## 4. Group C — one exclusion

**Common problem.** AAL: no finite nonempty top layer. Its failure has one shape ([`not_abscissaLaw_iff_finite_layer`](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/TheFailureOfTheAbscissaLawIsAFiniteLayer.lean#L33)).

| Face | Statement | Programme or route | Lean |
|---|---|---|---|
| Counting | AAL ⇔ no line right of ½ has a finite number > 1 of zeros to its right | floor-free arithmetic | [`asymptoticAbscissaLaw_iff_encard_rightOf_le_one`](../../../formal/GaloisForLFunctions/FloorFreeArithmetic/NonAttainmentGivesTheAbscissaLaw.lean#L117) |
| Trace classification | RH / empty top line / finite nonempty top line / infinite top line | floor-free arithmetic | [`zetaNormTrace_quadrichotomy`](../../../formal/GaloisForLFunctions/FloorFreeArithmetic/TheSplineTraceClassificationAtTheZeroAbscissa.lean#L437) |
| Non-attainment | AAL from non-attainment on windows of one length per depth | floor-free arithmetic | [`asymptoticAbscissaLaw_of_windowNonAttainment`](../../../formal/GaloisForLFunctions/FloorFreeArithmetic/NonAttainmentGivesTheAbscissaLaw.lean#L54) |
| Accumulation | AAL if every off-line zero has infinitely many zeros of nearly its real part | auxiliary dynamics, BAG | [`asymptoticAbscissaLaw_of_infinite_zeros`](../../../formal/GaloisForLFunctions/ArithmeticAuxiliaryDynamics/TheMissingInputOfTransport.lean#L236) |
| Very smooth degrees | AAL from a lower bound of the spline trace | surface of Spec ℤ | [`asymptoticAbscissaLaw_of_bddBelow_verySmooth`](../../../formal/GaloisForLFunctions/SurfaceOfSpecZ/VerySmoothDegreesNeedAnAttainedTop.lean#L889) |
| Thick lag | RH ⇔ ZAL ∧ bounded lag of one tower on a thick set (base change over ℤ) | IRW, WL | [`riemannHypothesis_iff_zerosApproachLine_and_thick_lag_bounded`](../../../formal/GaloisForLFunctions/InfiniteRankWeilTheory/TheTowersOfZeta.lean#L214) |

**The second half.** ZAL with landing: RH ⇔ ZAL ∧ (finite off-line set ⇒ RH) ∧ landing ([`riemannHypothesis_iff_three_atoms`](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheLandingLawForZeta.lean#L68)). Candidates EGC and APF belong here.

## 5. Group D — one collision

**Common problem.** The zeros of the heat family stay real down to time 0.

| Face | Statement | Route | Lean |
|---|---|---|---|
| Local constant | RH ⇔ Λ_X = 0 for every X | ZCG | [`riemannHypothesis_iff_forall_localNewmanConstant_eq_zero`](../../../formal/GaloisForLFunctions/RHTower/Heat/TheLocalDeBruijnNewmanConstant.lean#L103) |
| Branch times | RH ⇔ no positive real branch time; conjugation is the word of the real turns | ZCG | [ConjugationOfTheZerosIsTheWordOfTheTurnsAroundTheRealBranchTimes](../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ConjugationOfTheZerosIsTheWordOfTheTurnsAroundTheRealBranchTimes.lean) |
| Jensen polynomials | the non-real count increases to the total off-line multiplicity | LA | [`jensenNonrealCount_eq_zero_of_le_31922`](../../../formal/GaloisForLFunctions/VerifiedHeightRungs/TheJensenPolynomialsThroughDegree31922AreRealRooted.lean#L21) |
| Cosine shifts | collision-free descent in the shift ⇒ RH | PTR | frontier map [L] |

**Relation to the width.** One-sided: Λ ≤ w²/2 ([`newmanConstant_le_half_sq_zetaZeroWidth`](../../../formal/GaloisForLFunctions/SquareRootThreshold/TheWallsMeasureOneZeroWidth.lean#L331)) and Λ_X ≥ c·d²/log X ([`exists_le_localNewmanConstant_of_offLine_zero`](../../../formal/GaloisForLFunctions/RHTower/Heat/TheLocalDeBruijnNewmanConstant.lean#L157)). The heat time is not a ruler ([`exists_cosDefect_width_heatTime_lt`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheHeatTimeIsTheWidthTimesTheSpacing.lean#L109)).

## 6. Group E — one uniformity

| Order parameter | Uniform statement | Route | Lean |
|---|---|---|---|
| Tensor power k | one growth exponent for all even prime-trace moments ⇔ RH | SRT | [`riemannHypothesis_iff_moments_primeTraces`](../../../formal/GaloisForLFunctions/SurfaceOfSpecZ/TheTensorPowerTrick.lean#L34) |
| Adams power m | top bound one for all powers ⇔ temperedness | tensor powers | [`adamsPoleLaw_iff`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/TemperedIsTheUniformTopBound.lean#L87) |
| Power sums of a finite root set | an eventual one-sided bound ⇔ all roots in the unit disk | ZCG | [`roots_norm_le_one_iff_eventually_re_powerSum_bounded`](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/OneSidedPowerSumsDetectEveryExteriorRoot.lean#L78) |
| Mollifier length θ | long-prefix moments O(T^K), K independent of θ ⇒ RH | WD | frontier map [L] |
| Gauge moment order | a sublinear loss law excludes every positive depth; gauge moments lose linearly | amplification | [`nonpos_of_sublinear_loss`](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/MultiplicativeAmplificationLosesLinearly.lean#L71) |
| Period k of a frame | cofinal valid sign levers ⇔ one valid Deligne lever ⇒ RH | MC, tensor powers | [`signLevers_cofinal_iff_deligneLever`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/AWallAboveOneHalfIsAWorldOffTheLine.lean#L124), [`riemannHypothesis_of_signLevers`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/TheThreeLinesOfFrames.lean#L94) |
| Rank, degree, index n | positivity at every rank (TH, ECP), degree (LA, HCF), index (LI, PA) | TH, ECP, LA, HCF, LI, PA | frontier map [L] |

*Reading:* groups B and E overlap on TH, ECP, LI, PA, HCF.

## 7. Group F — the physical faces

| Physical statement | Mathematical face | Group | Lean |
|---|---|---|---|
| Ringdown of a pulse on the modular horizon at rate δ | zero-free strip | A | [`zeroFreeStrip_iff_pulse_ringdown`](../../../formal/GaloisForLFunctions/BlackHoleRingdown/TheRingdownRateIsTheZeroFreeStrip.lean#L625) |
| Thermalization of Farey counts | zero-free strip | A | [`zeroFreeStrip_iff_fareyCount_rate`](../../../formal/GaloisForLFunctions/CountingHolography/ThermalizationFasterThanTheSquareRootIsAZeroFreeStrip.lean#L486) |
| A one-sided bound on the dual side | a rate | A | [`not_oneSided_of_seen`](../../../formal/GaloisForLFunctions/ArithmeticHolographyOfTheModularHorizon/TheDualSideHasNoSign.lean#L867) |
| Hawking–Page transition of the confined half-line form | the critical state at W₀ | B | [`offLine_arithmetic_hawking_page_transition`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ArithmeticHawkingPagePhaseStructure.lean#L440) [S], [`riemannHypothesis_or_exists_criticalHalfLineGroundState`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/HalfLinePolarThresholdAndGroundStateOrthogonality.lean#L339) |
| Quasinormal expansion of the critical state | Σ_z LF(z)e^(−zu) = a(F⁺1_(u>0) − e^(−8u)F1_(u<0)) as distributions | B | [`criticalState_hasSum_zeroSeries_test`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheExplicitFormulaHoldsAtTheStateAgainstSmoothTests.lean#L312) |
| Reflection positivity of the cavity | Krein index | B | [`tentReflectionKrein_index`](../../../formal/GaloisForLFunctions/ArithmeticHolographyOfTheModularHorizon/TheReflectionKreinFormCountsTheOffLineResonances.lean#L244) |

Causality, passivity, Herglotz admittance, unitarity and KMS positivity are not faces of RH: they hold on the prime-two deformations ([`xiDeformed`](../../../formal/GaloisForLFunctions/BlackHoleRingdown/CausalIdentitiesCannotForceQuarterRingdown.lean#L215)) and on the positive Euler twins ([`exists_positive_passive_twin`](../../../formal/GaloisForLFunctions/BlackHoleRingdown/ThePositiveEulerTwinsArePassive.lean#L360)), which have off-line zeros.

## 8. What separates ζ from its models

The source-class wall theorem makes selectivity a theorem: the wall of the levers valid on a class of models is the largest abscissa the class realizes ([TheWallOfASourceClassIsTheLargestAbscissaItRealizes](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWallOfASourceClassIsTheLargestAbscissaItRealizes.lean)). So every argument is classified by the models it does not exclude. Each class keeps a list of properties of ζ and lacks one.

| Model class | Keeps | Lacks | Lean |
|---|---|---|---|
| Integer-norm Euler systems | Euler product over natural norms, reflection of the configuration; every finite datum of depth below ½ | functional equation | [`eulerSymmetric_layerConfig`](../../../formal/GaloisForLFunctions/FloorFreeArithmetic/TheZeroConfigurationDoesNotSeeTheEulerProduct.lean#L247) |
| Euler worlds | Euler product; abscissas in (½, 2/3) | functional equation | [`exists_eulerWorld_zeroAbscissa_eq`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L81) |
| Cosh models | functional equation; every abscissa ≥ ½ | Dirichlet series | [`wall_eq_seed_of_coshModels`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWallOfASourceClassIsTheLargestAbscissaItRealizes.lean#L206) |
| Shifted pairs ζ(s−a)ζ(s+a) | Euler product, functional equation, nonnegative coefficients | coefficient size n^ε | [`wall_eq_seed_of_shiftedPairs`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWallOfASourceClassIsTheLargestAbscissaItRealizes.lean#L228) |
| Multiplicative twins | degree one, functional equation, multiplicative coefficients in [1, 1 + A + p]; every abscissa ≥ Θ | level one; nonnegative Euler logarithm | [`zeroSupRe_zetaTwin`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMultiplicativeTwinsRealizeEveryAbscissaAboveTheZeros.lean#L99) |
| Positive passive twins | finite ζ prefix, entire reflected completion positive on ℝ, contractive scattering | nonnegative Euler logarithm | [`exists_positive_passive_twin`](../../../formal/GaloisForLFunctions/BlackHoleRingdown/ThePositiveEulerTwinsArePassive.lean#L360) |
| Prime-two deformations | functional equation, passivity, unitarity, Euler product, window positivity to (log 2)/2 | nonnegative coefficients; nonnegative Euler logarithm | [`xiDeformed`](../../../formal/GaloisForLFunctions/BlackHoleRingdown/CausalIdentitiesCannotForceQuarterRingdown.lean#L215), [`not_exists_nonnegative_primeTwo_representation`](../../../formal/GaloisForLFunctions/BlackHoleRingdown/ThePositiveEulerTwinsArePassive.lean#L81) |
| Finite rational edits | entire reflected completion | nonnegative Euler logarithm | [`not_exists_nontrivial_positive_finite_rational_twin`](../../../formal/GaloisForLFunctions/SelbergClass/FinitePrimeRationalEulerRigidity.lean#L197) |
| Sub-Euler gluing model | ζ's contacts through any cutoff, same dyadic middles | primes in the top octave | [`not_reweightedDoublingLaw_of_lt_sqrt_two_subEulerGluingWeight`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L174) |
| Golden datum | integrality, positive Euler data, functional equation | purity | [`goldenDatum_beurling`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheGoldenCurveIsABeurlingSystem.lean#L582) |
| Positive-weighted Beurling systems | positive weights, count Ax + O(x^(4/5)) | bounded functional-equation defect | [`exists_positiveWeighted_beurling_slow_defect`](../../../formal/GaloisForLFunctions/EulerFETransportTheory/ArbitrarilySlowDefectsOfPositiveWeightedSystems.lean#L569) |
| Approaching remainders | functional equation, reality, order one | Euler product | [`approachingModel_eq_zero_iff`](../../../formal/GaloisForLFunctions/InfiniteRankWeilTheory/TheFunctionalEquationAdmitsApproachingRemainders.lean#L312) |
| Meromorphic tempered Euler one-off | Euler product over ℚ's primes, Ramanujan-bounded coefficients | holomorphy in the left strip | [`asymptoticAbscissaLaw_or_exists_meromorphic_tempered_euler_oneOff`](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/TheMeromorphicTemperedEulerFirewall.lean#L1687) |

*Reading.* The class that keeps exact functional equation, Euler product over the rational primes, level one and a nonnegative Euler logarithm together is ζ alone (decaying-defect rigidity, [`beurlingSystem_rigidity_of_decaying_defect`](../../../formal/GaloisForLFunctions/EulerFETransportTheory/DecayingFunctionalEquationsDetermineThePrimes.lean#L579)). A proof of RH is therefore a proof about one object, and every exact property the corpus has found for the critical state also holds for the states of the models above wherever the state exists: the state equation, its continuation, its sign law and its finite index are soft.

## 9. Bridges between the problems

| ID | Bridge | From → to | Lean |
|---|---|---|---|
| G1 | A doubling law with factor λ gives the half-plane Re s > ½ + log₂ λ, and conversely | R ↔ P | [`riemannZeta_ne_zero_of_doublingLaw`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L793), [`doublingLaw_of_zetaZeroWidth_lt`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestDoublingFactorOfTheMarginIsTwoToTheWidth.lean#L184) |
| G2 | A floor of Weil's form at rate β in the logarithmic energy ⇔ w ≤ β | R ↔ P | [`isRuler_logEnergyFloor`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWidthIsTheRateOfTheWeilFloorInTheLogarithmicEnergy.lean#L428) |
| G3 | RH ⇔ a constant level law of the margin | R ↔ W | [`riemannHypothesis_iff_exists_const_isLevelLaw`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheLossOfTheMarginIsBoundedOrPolynomial.lean#L61) |
| G4 | The Hodge defect is the number of right zeros | R ↔ U | [`zeta_hodgeDefect_iff`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheHodgeDefectCountsTheRightZeros.lean#L556) |
| G5 | Λ ≤ w²/2 | P → heat | [`newmanConstant_le_half_sq_zetaZeroWidth`](../../../formal/GaloisForLFunctions/SquareRootThreshold/TheWallsMeasureOneZeroWidth.lean#L331) |
| G6 | Θ < 1 or AAL | U → P | [`quasiRH_or_asymptoticAbscissaLaw`](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/QuasiRHIsATailLaw.lean#L27) |
| G7 | RH ⇔ the reflection lifts to Gal(E/B) and every weight lies in B | arithmetic of the zeros ↔ W | [`forall_re_eq_half_iff`](../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ALiftOfTheReflectionIsConjugationExactlyWhereTheWeightLiesInThePrimeTraceField.lean#L74) |
| G8 | A Hecke zero with probe estimates gives a rung zero at 6ρ − 3 | seeded family → Grössencharacter tower | [`grossenLFunction_zero_of_hecke_zero_and_probe_estimates`](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheCubicProbeIsACoupledTowerReachingThreeFifths.lean#L164) |
| G9 | A pole law of the even tensor moments at weight w₀ ⇔ w ≤ w₀ | tensor powers ↔ W | [`exists_momentPoleLaw_iff`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/ThePrimeTraceMomentsOfZetaReadTheWidthWithBaseLossAtMostOne.lean#L223) |
| G10 | The decay exponent of the critical state bounds the right zeros; the seed gives decay of the averaged state | R ↔ P | [`criticalState_not_integrable_of_zero`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheDecayOfTheStateReadsTheZeros.lean#L316), [`criticalState_averaged_decay_beyond_barrier`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheAveragedStateDecaysAtTheRateOfTheZeros.lean#L701) |
| G11 | The critical state has a pole at ρ − 17/2 for every right zero; the confined form has finite index at every ratio | R ↔ U | [`differentiableAt_stateContinuation_iff`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheTransformOfTheStateHasPolesAtTheZeros.lean#L193), [`exists_bound_orthonormal_nonpositive`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheConfinedFormHasFiniteIndexAtEveryRatio.lean#L98) |
| G12 | The order-six unit-layer remainder reads the zeros of ζ_K | P (probe) ↔ W for ζ_K | [`smoothedRemainder_forces_thetaSquare_zero`](../../../formal/GaloisForLFunctions/OrderSixMetaplecticTheory/TheSmoothedRemainderReadsTheZerosOfTheCubeZeta.lean#L316) |
| G13 | Positive finite-field square sums at ζ's zeros converge to M; Re W_Λ = M − D | 𝔽_q calibration ↔ R | [`riemannHypothesis_iff_kummer_positive_limit_actualWeil`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/Intersection/KummerActualZetaComparison.lean#L176) |

G1, G2 and G10 are why P and R are one problem with two kinds of input: a sign with a loss is an exponent, and the decay of the null vector is an exponent. The seed crosses G1, G2 and G10 from P to R; no statement of the corpus crosses them from R to P (O8).

## 10. Pairs that are not faces of one problem

| Pair | Why they differ | Lean |
|---|---|---|
| The exponent walls 13/15, 5/6, 2/3, 3/5 and the sign | the walls bound completion classes of the estimate route; a window sign at one aperture is compatible with zeros of any depth | [`sInf_coupledBarrier_eq_three_fifths`](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/MoebiusSignedGaussPairingsEndAtThreeFifths.lean#L859), [`exists_zetaDensity_positive_window_deep_zeros`](../../../formal/GaloisForLFunctions/SelectiveArithmetic/TheRungSignSurvivesDeepZerosAtZetaDensity.lean#L90) |
| A certificate at a fixed aperture and the sign at every aperture | no positive floor along unbounded apertures | [`not_exists_positive_floor_along`](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/TheApertureFloorMustDecayDoublyExponentially.lean#L110) |
| ZAL and AAL | approaching models with infinitely many zeros off the line | [`approachingModel_eq_zero_iff`](../../../formal/GaloisForLFunctions/InfiniteRankWeilTheory/TheFunctionalEquationAdmitsApproachingRemainders.lean#L312) |
| The width and the heat time | fixed width, heat time → 0 | [`exists_cosDefect_width_heatTime_lt`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheHeatTimeIsTheWidthTimesTheSpacing.lean#L109) |
| The sign of the monodromy group and RH | a proper group forces only a mod-8 law of collision masses | [`eight_dvd_collisionMass`](../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ARealCollisionOfMassNotDivisibleByEightGivesEverySignedPermutation.lean#L174) |
| Positivity of Λ in finite certificates and the width | Fejér ratio < 2: only regions of width O(1/log) | [`fejer_barrier_attained`](../../../formal/GaloisForLFunctions/MultiplicativePositivityGeometry/ExactFejerBarrier.lean#L351) |
| RH over 𝔽_q for cubic characters and RH over ℤ | the 𝔽_q proof is a Stepanov count plus base change; over ℤ base change is the thick-set lag lever and the Stepanov degree is log lcm(1,…,N), whose √N-precision bound is RH | [`riemannHypothesis_cubicCharacter`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheAcidTestPassesForCubicCharacters.lean#L272), [`riemannHypothesis_iff_log_length_fixedPointAux_le`](../../../formal/GaloisForLFunctions/ArithmeticLefschetzStepanovTheory/TheLefschetzNumbersAreStepanovDegrees.lean#L236) |
| Purity and the price of the sign | pure calibration curves pay k/2 | [`stickelbergerPrice_jacobiTriple`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/TheCalibrationCurvesArePureByTheirPairing.lean#L56) |
| Integrality with positive Euler data and purity | the golden datum has the first and not the second | [`goldenDatum_beurling`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheGoldenCurveIsABeurlingSystem.lean#L582) |
| Künneth positivity and purity | Künneth–Adams positivity is point-count positivity | [`kunneth_positivity_tfae`](../../../formal/GaloisForLFunctions/ArithmeticKunnethTheory/KunnethPositivityIsPointCountPositivity.lean#L68) |
| Root coincidences and RH | a coincidence forces Θ ≥ k/(k+1); its exclusion for k ≤ 6 is weaker than RH | [`abscissa_ge_of_zeta_zero_div_nat`](../../../formal/GaloisForLFunctions/ZeroForcingCalculus/EulerDilationAndRootCoincidenceExclusion.lean#L174) |

## 11. Consequences for the choice of work

- A route of group A advances only with the producer; work on a ruler changes the coordinate, not the number. This includes the decay of the critical state.
- A route of group B advances by a certificate at a fixed position or by the sign at every aperture; the first does not transfer (R1–R3), the second is RH. ECS is the group-B face in which the missing input is a single property of one function.
- Groups C and D have receivers and no producer.
- The open steps that are neither RH nor a finite certificate are O1–O4 (estimates), O6 (root coincidences), O8 (doubling from the matrices), O11 (separation beyond finite edits) and O16 (monodromy sign).
