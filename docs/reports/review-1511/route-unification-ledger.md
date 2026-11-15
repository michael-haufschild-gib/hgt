# Review 1511 — route unification ledger

Corpus: commit a7fcf5212f with the working tree (15 November 2026). The ledger records which routes are faces of one problem, by the theorem that identifies them. Every Lean statement cited was read in source. O11 additions were individually checked with `lake --old env lean`; no umbrella build or axiom audit was run for those additions.

Grades are the frontier map's: **[L]** integrated, **[S]** source only, **[K]** individually audited; **(src)** marks a statement read in the Lean source that has no grade of its own on the frontier map. *Reading* marks an interpretation of this report.

Companion reports: [routes and obstacles](route-obstacles.md) (route names and receivers), [obstacles summary](obstacles-summary.md) (open problems O1–O16), [walls ledger](walls-ledger.md) (walls P, R, U).

## 1. Result

The frontier map lists 38 live route formulations and 12 candidates. Under the identifications proved in Lean, and for the routes that have a receiver only under the reading stated in each group, they are faces of three statements about one configuration:

| Problem | Statement | Faces |
|---|---|---|
| **W — the width** | w = sup \|Re ρ − ½\| = 0 | every ruler (group A), every sign criterion (group B), every collision criterion (group D), every uniformity criterion (group E), every physical rate (group F) |
| **AAL — the abscissa law** | no line has a finite positive number of zeros to its right | group C |
| **ZAL — approach to the line** | the zeros approach the line, with landing | the second half of group C |

RH ⇔ W ⇔ ZAL ∧ AAL ([`riemannHypothesis_tfae`](../../../formal/GaloisForLFunctions/InfiniteRankWeilTheory/TheInfiniteRankWeilProof.lean#L64)). The routes differ in the kind of input they accept, not in the problem:

| Family | Input a route accepts | What the identifications show |
|---|---|---|
| P | an estimate with cancellation | every estimate is a bound for w, and every bound for w is every estimate (group A) |
| R | a sign of a quadratic form | a sign with a loss of rate β is the bound w ≤ β; the sign without loss is w = 0 (bridges G1–G3) |
| U | an exclusion or a statement uniform in an order | each finite stage is available; the uniform statement is w = 0, AAL or ZAL (groups C–E) |

Statements strictly weaker than RH that the faces expose: the stages O1–O4, the root coincidences O7, a doubling factor below √2 (O9), the now-proved separation of rational Euler deformations at one prime (O11), the sign of the monodromy group O16.

## 2. Group A — one width, many rulers

**Common problem.** A ruler is a criterion that holds at exponent β exactly when w ≤ β. All rulers read one number; a bound proved in one is a bound in all ([`sub_three_eighths_ruler_jump`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheAbscissaAvoidsAnIntervalBelowSevenEighths.lean#L186) [L]; [EveryRulerCarriesTheSeedAndEveryLever](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean)). No ruler produces a bound.

| Ruler | Coordinate in which it reads w | Route | Lean |
|---|---|---|---|
| Mertens function, producer rate | a polynomial rate of an integer producer exists ⇔ M(n) = O(n^(1−σ)) for some σ > 0; M(n) = O(n^(7/8)) holds | MC | [`exists_hasRate_rpow_iff_mertens`](../../../formal/GaloisForLFunctions/ArithmeticAuxiliaryDynamics/TheRateAndTheMertensScaleCoincide.lean#L452), [`exists_mertens_le_seven_eighths_exact`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheAbscissaAvoidsAnIntervalBelowSevenEighths.lean#L229) |
| Signal of the zeta kernel | Θ ≤ b ⇔ signal O(Z^(b′)), b′ > b | JAS | [TheSignalExponentIsTheZeroAbscissa](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSignalExponentIsTheZeroAbscissa.lean) |
| Squarefree power quotient | pole-free on Re s > β/2 ⇔ Θ ≤ β, for β < 27001/48000 | SQF | [`squarefreePowerQuotient_poleFree_iff_zetaZeroAbscissa_le_sub`](../../../formal/GaloisForLFunctions/ZeroForcingCalculus/EulerDilationAndRootCoincidenceExclusion.lean#L309) |
| Long mollified moments | least slope loss = 2w | WD | [`zetaZeroWidth_le_of_slopeLaw`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestSlopeLossOfTheLongMomentsIsTwiceTheWidth.lean#L68), [`slopeLaw_sub_three_quarters`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheAbscissaAvoidsAnIntervalBelowSevenEighths.lean#L335) |
| Prime traces on logarithmic windows | w ≤ σ ⇔ one-sided bounds −K·p^σ | SRT | [`zetaZeroWidth_le_iff_bddBelow_primeDegrees`](../../../formal/GaloisForLFunctions/SurfaceOfSpecZ/TheWidthIsTheStepanovExponentAtThePrimes.lean#L909) |
| Even prime-trace moments | 2kw ≤ a_k ≤ 1 + 2kw, a_k/(2k) → w | SRT, tensor-power programme | [`tendsto_momentExponent_div`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/ThePrimeTraceMomentsOfZetaReadTheWidthWithBaseLossAtMostOne.lean#L201) |
| Pulse ringdown on the modular surface | rate δ ⇔ no zero with Re ρ > 1 − 2δ | PM | [`zeroFreeStrip_iff_pulse_ringdown`](../../../formal/GaloisForLFunctions/BlackHoleRingdown/TheRingdownRateIsTheZeroFreeStrip.lean#L625) |
| Thermalization of Farey counts | rate y^(1/2+δ−ε) ⇔ the same strip | counting holography | [`zeroFreeStrip_iff_fareyCount_rate`](../../../formal/GaloisForLFunctions/CountingHolography/ThermalizationFasterThanTheSquareRootIsAZeroFreeStrip.lean#L486) |
| Floor of Weil's form in the logarithmic energy | w ≤ β ⇔ floor at rate β | RW | [`isRuler_logEnergyFloor`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWidthIsTheRateOfTheWeilFloorInTheLogarithmicEnergy.lean#L428) |
| Margin of the window matrices | infimum of margin rates = w | ACS | [`isRuler_marginLaw`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesIsARulerAtPolynomialBlockSize.lean#L782), [`sInf_marginLaw_eq_zetaZeroWidth`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesIsARulerAtPolynomialBlockSize.lean#L804) |
| Doubling factor of the margin | infimum of factors = 2^w | ACS | [`zetaZeroWidth_le_logb_of_doublingLaw`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestDoublingFactorOfTheMarginIsTwoToTheWidth.lean#L178), [`doublingLaw_of_zetaZeroWidth_lt`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestDoublingFactorOfTheMarginIsTwoToTheWidth.lean#L184) |
| Return transfer on log² windows | the transfer ⇔ RH | S3 (candidate) | [`homogeneousReturnWindowTransfer_iff_riemannHypothesis`](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheReturnTransferIsTheRiemannHypothesisUnderAStrip.lean#L44) |

**Members by receiver** (a bound at exponent ½ + ε implies RH or is equivalent to it): PBM, RB, SZ, TT, CTF, BAG. *Reading:* each is the endpoint w = 0 of a ruler of the table.

**What one solution gives.** A bound w ≤ β from any source gives, by the table, the Mertens bound, the signal bound, the slope law, the ringdown rate, the Weil floor at rate β and the doubling factor 2^β. The seed gives all of them at β = 8999/24000.

**The producer inside the group.** The only source of a bound is the estimate route. Its open steps O1–O5 are stages of one problem, half-power cancellation (O6), ordered by the exponent they reach: 13/15, 5/6, 2/3, 3/5, k/(2(k−1)), ½ (walls ledger, "The walls in order of exponent").

## 3. Group B — one sign

**Common problem.** Nonnegativity of Weil's form on every test, in one of its coordinates.

| Face | Statement | Routes | Lean |
|---|---|---|---|
| Negative squares | number of negative squares = number of zeros right of the line | all of group B | [`pontryagin_law`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheHodgeDefectCountsTheRightZeros.lean#L490) |
| Windows | RH ⇔ index one of every neutral window | ACS, SC | [`riemannHypothesis_iff_forall_hermNegIndex_neutralWindow_eq_one`](../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheRiemannHypothesisIsOneNegativeSquareOfTheNeutralPartOfEveryWindow.lean#L622) |
| Ground energy | μ(a) = the floor of Weil's form on step packets of the windows inside a | RW, EWU/OWU, ACT | [`stepFloor_iff_le_groundEnergy`](../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheGroundEnergyOfAnApertureIsTheFloorOfWeilsFormOnTheWindowsInsideIt.lean#L500) |
| Onset aperture | onset = ⊤ ⇔ all zeros on the line | RW | [`onsetAperture_eq_top_iff_onLine`](../../../formal/GaloisForLFunctions/WindowVisibilityLaw/OnsetApertureAndPositivityDictionary.lean#L372) |
| Prime lag | RH ⇔ the Weil lag function is positive definite | WL | [ThePrimeLagIsPositiveDefiniteExactlyUnderRH](../../../formal/GaloisForLFunctions/InfiniteRankPurityTheory/ThePrimeLagIsPositiveDefiniteExactlyUnderRH.lean) |
| Half-line form | RH ⇔ λ(R) ≥ 0 at every R | HF | [ArithmeticHawkingPagePhaseStructure](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ArithmeticHawkingPagePhaseStructure.lean) [S] |
| Jump tail | corrected energy + jump tail = Weil's form at a fixed height | HAT-C | [TheJumpTailFloorNeedsTheFullArithmeticNormalization](../../../formal/GaloisForLFunctions/HyperbolicArakelovTheory/TheJumpTailFloorNeedsTheFullArithmeticNormalization.lean) |
| Deformation | RH ⇔ the regularized Gram deforms crossing-free at every horizon | edge Hodge theory | [TheIndexComputedByDeformation](../../../formal/GaloisForLFunctions/EdgeHodgeTheory/TheIndexComputedByDeformation.lean) |
| Reflection Krein form | at most one negative square, zero at a critical zero, one off the line | PM | [`tentReflectionKrein_index`](../../../formal/GaloisForLFunctions/ArithmeticHolographyOfTheModularHorizon/TheReflectionKreinFormCountsTheOffLineResonances.lean#L244) |
| Schur complements | RH ⇔ the Schur complement of every dyadic middle is nonnegative | ACS | [`riemannHypothesis_iff_forall_overlapSchur_nonneg`](../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheLossOfAnOverlapStepIsAdditiveBelowTheBindingEnergyOfTheMiddle.lean#L609) |
| Effectivity | Hodge index ⇔ an effectivity with Riemann–Roch and ampleness | ACS | [`exists_effectivity_iff_hodgeIndex`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HodgeIndexFromEffectivity.lean#L102) |
| Count | a form is the Tate limit of a count ⇔ it is nonnegative | counting holography | [`exists_count_tateLimit_iff`](../../../formal/GaloisForLFunctions/CountingHolography/TheCountDoorOfACurveAndOfZ.lean#L39) |

**Members by receiver only** (a positivity at every aperture, rank or degree implies RH): CHMD, TH, RN, GTA, AIP, ECP, PA, LI, HCF, FU, CFC, RP, and the candidates SEC, CDC/BSH, EWJ, MSC, RFHM, W1C, WBF, IRK. *Reading:* each asks for the sign of the same form on a subfamily of tests.

**What one solution gives.** The sign at every aperture in any face gives RH and with it every face.

**What distinguishes the faces.** The certified range. The faces are certified at different fixed positions (aperture log 2, ratio three, rank 14, order 200, n ≤ 314), and none of the certificates is a consequence of another in Lean.

## 4. Group C — one exclusion

**Common problem.** AAL: no finite nonempty top layer. Its failure has one shape ([`not_abscissaLaw_iff_finite_layer`](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/TheFailureOfTheAbscissaLawIsAFiniteLayer.lean#L33)), and each receiver detects that shape in its own coordinate.

| Face | Statement | Programme or route | Lean |
|---|---|---|---|
| Counting | AAL ⇔ no line right of ½ has a finite number > 1 of zeros to its right | floor-free arithmetic | [`asymptoticAbscissaLaw_iff_encard_rightOf_le_one`](../../../formal/GaloisForLFunctions/FloorFreeArithmetic/NonAttainmentGivesTheAbscissaLaw.lean#L117) |
| Trace classification | RH / empty top line / finite nonempty top line / infinite top line | floor-free arithmetic | [`zetaNormTrace_quadrichotomy`](../../../formal/GaloisForLFunctions/FloorFreeArithmetic/TheSplineTraceClassificationAtTheZeroAbscissa.lean#L437) |
| Non-attainment | AAL from non-attainment on windows of one length per depth | floor-free arithmetic | [`asymptoticAbscissaLaw_of_windowNonAttainment`](../../../formal/GaloisForLFunctions/FloorFreeArithmetic/NonAttainmentGivesTheAbscissaLaw.lean#L54) |
| Phase return | AAL from one bounded phase return at each off-line zero | auxiliary dynamics, BAG | [`asymptoticAbscissaLaw_of_infinite_zeros`](../../../formal/GaloisForLFunctions/ArithmeticAuxiliaryDynamics/TheMissingInputOfTransport.lean#L236) |
| Very smooth degrees | AAL from a lower bound of the spline trace | surface of Spec ℤ | [`asymptoticAbscissaLaw_of_bddBelow_verySmooth`](../../../formal/GaloisForLFunctions/SurfaceOfSpecZ/VerySmoothDegreesNeedAnAttainedTop.lean#L889) |
| Deuring–Heilbronn form | abscissa law ⇔ linear law ∧ asymptotic Deuring–Heilbronn | exceptional layers | [TheDeuringHeilbronnQuestionForZeta](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheDeuringHeilbronnQuestionForZeta.lean) |
| Prime shells, prime towers | shell signs on infinitely many dyadic prime shells ⇒ AAL; an undamped bound on a two-prime cone ⇒ AAL | JAS, SC | frontier map [L] |

**The second half.** ZAL with landing: RH ⇔ ZAL ∧ (finite off-line set ⇒ RH) ∧ landing ([`riemannHypothesis_iff_three_atoms`](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheLandingLawForZeta.lean#L68)). Candidates EGC and APF belong here.

**What one solution gives.** AAL in any face gives all faces. AAL alone gives no bound for Θ; with ZAL it gives RH.

## 5. Group D — one collision

**Common problem.** The zeros of the heat family stay real down to time 0.

| Face | Statement | Route | Lean |
|---|---|---|---|
| Local constant | RH ⇔ Λ_X = 0 for every X | ZCG | [`riemannHypothesis_iff_forall_localNewmanConstant_eq_zero`](../../../formal/GaloisForLFunctions/RHTower/Heat/TheLocalDeBruijnNewmanConstant.lean#L103) |
| Branch times | RH ⇔ no positive real branch time ⇔ conjugation is the identity at each positive nonbranch time | ZCG | frontier map [L]; [ConjugationOfTheZerosIsTheWordOfTheTurnsAroundTheRealBranchTimes](../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ConjugationOfTheZerosIsTheWordOfTheTurnsAroundTheRealBranchTimes.lean) |
| Jensen polynomials | the non-real count N_d increases to the total off-line multiplicity | LA | frontier map [L]; [`jensenNonrealCount_eq_zero_of_le_31922`](../../../formal/GaloisForLFunctions/VerifiedHeightRungs/TheJensenPolynomialsThroughDegree31922AreRealRooted.lean#L21) |
| Cosine shifts | collision-free descent in the shift ⇒ RH | PTR | frontier map [L] |

**Relation to the width.** One-sided: Λ ≤ w²/2 ([`newmanConstant_le_half_sq_zetaZeroWidth`](../../../formal/GaloisForLFunctions/SquareRootThreshold/TheWallsMeasureOneZeroWidth.lean#L331)) and Λ_X ≥ c·d²/log X for an off-line zero of depth d ([`exists_le_localNewmanConstant_of_offLine_zero`](../../../formal/GaloisForLFunctions/RHTower/Heat/TheLocalDeBruijnNewmanConstant.lean#L157)). The heat time is not a ruler: models of fixed width have heat time → 0 ([`exists_cosDefect_width_heatTime_lt`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheHeatTimeIsTheWidthTimesTheSpacing.lean#L109)).

## 6. Group E — one uniformity

**Common problem.** A bound whose constant or exponent does not grow with an order parameter.

| Order parameter | Uniform statement | Route | Lean |
|---|---|---|---|
| Tensor power k | one growth exponent for all even prime-trace moments ⇔ RH | SRT, tensor-power programme | [`riemannHypothesis_iff_moments_primeTraces`](../../../formal/GaloisForLFunctions/SurfaceOfSpecZ/TheTensorPowerTrick.lean#L34) |
| Adams power m | top bound one for all powers ⇔ temperedness | tensor-power programme | [`adamsPoleLaw_iff`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/TemperedIsTheUniformTopBound.lean#L87) |
| Mollifier length θ | long-prefix moments O(T^K) with K independent of θ ⇒ RH | WD | frontier map [L] |
| Gauge moment order | a loss law sublinear in the order excludes every positive depth; gauge moments lose at least linearly | amplification | [`nonpos_of_sublinear_loss`](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/MultiplicativeAmplificationLosesLinearly.lean#L71), [`pow_sum_normSq_le_sum_normSq_powCoeff`](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/MultiplicativeAmplificationLosesLinearly.lean#L102) |
| Period k of a frame | valid sign levers at all large periods ⇒ RH | MC, tensor-power programme | [`riemannHypothesis_of_signLevers`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/TheThreeLinesOfFrames.lean#L94) |
| Rank, degree, index n | positivity at every rank (TH, ECP), degree (LA, HCF), index (LI, PA) | TH, ECP, LA, HCF, LI, PA | frontier map [L] |

*Reading:* groups B and E overlap on TH, ECP, LI, PA, HCF: these routes ask for a sign and for its uniformity in an order.

## 7. Group F — the physical faces

The physical formulations are faces of groups A and B and of no further problem.

| Physical statement | Mathematical face | Group | Lean |
|---|---|---|---|
| Ringdown of a pulse on the modular horizon at rate δ | zero-free strip | A | [`zeroFreeStrip_iff_pulse_ringdown`](../../../formal/GaloisForLFunctions/BlackHoleRingdown/TheRingdownRateIsTheZeroFreeStrip.lean#L625) |
| Thermalization of Farey counts | zero-free strip | A | [`zeroFreeStrip_iff_fareyCount_rate`](../../../formal/GaloisForLFunctions/CountingHolography/ThermalizationFasterThanTheSquareRootIsAZeroFreeStrip.lean#L486) |
| A one-sided bound on the dual side | a rate | A | [`not_oneSided_of_seen`](../../../formal/GaloisForLFunctions/ArithmeticHolographyOfTheModularHorizon/TheDualSideHasNoSign.lean#L867) |
| Vacuum stability of the half-line form (Hawking–Page) | λ(R) ≥ 0 | B | [`offLine_arithmetic_hawking_page_transition`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ArithmeticHawkingPagePhaseStructure.lean#L440) [S] |
| Reflection positivity of the cavity | Krein index | B | [`tentReflectionKrein_index`](../../../formal/GaloisForLFunctions/ArithmeticHolographyOfTheModularHorizon/TheReflectionKreinFormCountsTheOffLineResonances.lean#L244) |
| A count law | nonnegativity of the form | B | [`exists_count_tateLimit_iff`](../../../formal/GaloisForLFunctions/CountingHolography/TheCountDoorOfACurveAndOfZ.lean#L39) |

Causality, passivity, unitarity and KMS positivity are not faces of RH: they hold on the prime-two deformations, on which the rate fails ([`xiDeformed`](../../../formal/GaloisForLFunctions/BlackHoleRingdown/CausalIdentitiesCannotForceQuarterRingdown.lean#L215)).

## 8. Bridges between the problems

| ID | Bridge | From → to | Lean |
|---|---|---|---|
| G1 | A doubling law with factor λ gives the half-plane Re s > ½ + log₂ λ, and conversely | R ↔ P | [`riemannZeta_ne_zero_of_doublingLaw`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L793), [`doublingLaw_of_zetaZeroWidth_lt`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestDoublingFactorOfTheMarginIsTwoToTheWidth.lean#L184) |
| G2 | A floor of Weil's form at rate β in the logarithmic energy ⇔ w ≤ β | R ↔ P | [`isRuler_logEnergyFloor`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWidthIsTheRateOfTheWeilFloorInTheLogarithmicEnergy.lean#L428) |
| G3 | RH ⇔ a constant level law of the margin | R ↔ W | [`riemannHypothesis_iff_exists_const_isLevelLaw`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheLossOfTheMarginIsBoundedOrPolynomial.lean#L61) |
| G4 | The Hodge defect is the number of right zeros; an unbounded defect ⇔ infinitely many off-line zeros | R ↔ U | [`zeta_hodgeDefect_iff`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheHodgeDefectCountsTheRightZeros.lean#L556) |
| G5 | Λ ≤ w²/2 | P → heat | [`newmanConstant_le_half_sq_zetaZeroWidth`](../../../formal/GaloisForLFunctions/SquareRootThreshold/TheWallsMeasureOneZeroWidth.lean#L331) |
| G6 | A failure of AAL gives Θ < 1 | U → P | [`quasiRH_or_asymptoticAbscissaLaw`](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/QuasiRHIsATailLaw.lean#L27) |
| G7 | RH ⇔ the reflection lifts to Gal(E/B) and every weight lies in B | arithmetic of the zeros ↔ W | [`forall_re_eq_half_iff`](../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ALiftOfTheReflectionIsConjugationExactlyWhereTheWeightLiesInThePrimeTraceField.lean#L74) |
| G8 | A zero of a finite-order Hecke L-function with probe estimates gives a zero of a rung at 6ρ − 3 | seeded family → Grössencharacter tower | [`grossenLFunction_zero_of_hecke_zero_and_probe_estimates`](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheCubicProbeIsACoupledTowerReachingThreeFifths.lean#L164) |
| G9 | A pole law of the even tensor moments at weight w₀ ⇔ w ≤ w₀ | tensor powers ↔ W | [`exists_momentPoleLaw_iff`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/ThePrimeTraceMomentsOfZetaReadTheWidthWithBaseLossAtMostOne.lean#L223) |

G1–G3 are the reason the families P and R are one problem with two kinds of input: a sign with a loss is an exponent. The seed crosses G1 and G2 from P to R; no statement of the corpus crosses them from R to P (obstacle O9).

## 9. Pairs that are not faces of one problem

| Pair | Why they differ | Lean |
|---|---|---|
| The exponent walls 13/15, 5/6, 2/3, 3/5 and the sign | the walls bound completion classes of the estimate route; a window sign at one aperture is compatible with zeros of any depth | [`sInf_coupledBarrier_eq_three_fifths`](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/MoebiusSignedGaussPairingsEndAtThreeFifths.lean#L859), [`exists_zetaDensity_positive_window_deep_zeros`](../../../formal/GaloisForLFunctions/SelectiveArithmetic/TheRungSignSurvivesDeepZerosAtZetaDensity.lean#L90) |
| A certificate at a fixed aperture and the sign at every aperture | no positive floor holds along unbounded apertures | [`not_exists_positive_floor_along`](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/TheApertureFloorMustDecayDoublyExponentially.lean#L110) |
| ZAL and AAL | functional equation, reality and order one admit zeros that approach the line with infinitely many off it | [`approachingModel_eq_zero_iff`](../../../formal/GaloisForLFunctions/InfiniteRankWeilTheory/TheFunctionalEquationAdmitsApproachingRemainders.lean#L312) |
| The width and the heat time | fixed width, heat time → 0 | [`exists_cosDefect_width_heatTime_lt`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheHeatTimeIsTheWidthTimesTheSpacing.lean#L109) |
| The sign of the monodromy group and RH | a proper group forces 8 to divide the collision masses and no exclusion | [`eight_dvd_collisionMass`](../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ARealCollisionOfMassNotDivisibleByEightGivesEverySignedPermutation.lean#L174) |
| Purity and the price of the sign | the calibration curves are pure and their Gauss triples cost k/2 | [`stickelbergerPrice_jacobiTriple`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/TheCalibrationCurvesArePureByTheirPairing.lean#L56) [S] |
| Integrality with positive Euler data and purity | the golden datum has the first and not the second | [`goldenDatum_beurling`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheGoldenCurveIsABeurlingSystem.lean#L582) |
| Künneth positivity and purity | all Künneth–Adams positivities ⇔ nonnegative point counts, which is weaker | [`kunneth_positivity_tfae`](../../../formal/GaloisForLFunctions/ArithmeticKunnethTheory/KunnethPositivityIsPointCountPositivity.lean#L68) |
| The cusp channel and the continuous channel of a congruence horizon | exceptional eigenvalues are bounded by 3/16, sharp in weight ½; the zeros are bounded by the seed | [`selberg_status`](../../../formal/GaloisForLFunctions/RHTower/SelbergConjectureStatus.lean#L34) |
| Root coincidences and RH | a coincidence ζ(ρ) = ζ(ρ/k) = 0 forces Θ ≥ k/(k+1); its exclusion for k ≤ 6 is weaker than RH | [`abscissa_ge_of_zeta_zero_div_nat`](../../../formal/GaloisForLFunctions/ZeroForcingCalculus/EulerDilationAndRootCoincidenceExclusion.lean#L174) |

## 10. Consequences for the choice of work

- A route of group A is advanced only by the producer. Work on a ruler changes the coordinate, not the number.
- A route of group B is advanced by a certificate at a fixed position or by the sign at every aperture; the first does not transfer (walls R1–R3), the second is RH.
- Groups C and D have receivers and no producer.
- The estimate route is the single place where an open step is neither RH nor a finite certificate: O1–O4.
