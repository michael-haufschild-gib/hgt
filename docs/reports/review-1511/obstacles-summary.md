# Review 1511 — obstacles summary

Corpus: commit a7fcf5212f with the working tree (15 November 2026). Inputs: the frontier map and the killed-routes ledger, the corpus search tool, and the Lean statements cited below, each read in source. O11 and O2 pole additions were individually checked with `lake --old env lean`; no umbrella build or axiom audit was run for those additions.

Grades are the frontier map's: **[L]** integrated, **[S]** source only (unfinished or unintegrated), **[K]** individually audited. **(src)** marks a statement read in the Lean source that has no grade of its own on the frontier map. *Table* marks a statement taken from a programme table returned by the search tool; it is not a Lean statement. *Reading* marks an interpretation of this report.

Companion reports: [routes and obstacles](route-obstacles.md), [walls ledger](walls-ledger.md), [route unification ledger](route-unification-ledger.md).

## 1. Position

RH is open. Three things are proved and carry every other statement of the frontier.

1. **A seed.** ζ, every Dirichlet L-function and every finite-order Hecke L-function of ℚ(ω) are zero-free on Re s > 20999/24000 [L] ([`riemannZeta_ne_zero_of_sub_seven_eighths_lt_re`](../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/SubSevenEighthsZeroFreeHalfPlane.lean#L147)). The proof is a cubic metaplectic probe; its exponent budget has a vertex in (40535/46328, 20999/24000] [L].
2. **A calculus.** Rulers (criteria that read the width w = sup |Re ρ − ½| exactly), levers (maps T with Θ ≤ b ⇒ Θ ≤ T b) and walls (fixed points a family of levers cannot pass) are theorems; a family of levers covering (½, 20999/24000] gives RH [L] ([`riemannHypothesis_of_covering_levers_sub_seven_eighths`](../../../formal/GaloisForLFunctions/ZeroForcingCalculus/EulerDilationAndRootCoincidenceExclusion.lean#L438)).
3. **Dictionaries.** Negative squares of Weil's form = zeros right of the line ([`pontryagin_law`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheHodgeDefectCountsTheRightZeros.lean#L490)); RH ⇔ ZAL ∧ AAL ([`riemannHypothesis_tfae`](../../../formal/GaloisForLFunctions/InfiniteRankWeilTheory/TheInfiniteRankWeilProof.lean#L64)); the best doubling factor of the window margin is 2^w [L] ([`zetaZeroWidth_le_logb_of_doublingLaw`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestDoublingFactorOfTheMarginIsTwoToTheWidth.lean#L178), [`doublingLaw_of_zetaZeroWidth_lt`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestDoublingFactorOfTheMarginIsTwoToTheWidth.lean#L184)).

The only mechanism in the corpus that produces a bound for the zero abscissa is the estimate route (family P). The sign route (family R) has certificates at fixed apertures and no producer; the tail route (family U) has receivers and no input.

**Tests applied to every question below.** T1: not equivalent to RH (to AAL where AAL is the subject). T2: a definite statement that a proof or a counterexample settles. T3: a Lean statement of the corpus consumes the answer. T4: not a statement at a fixed aperture, height or rank. T5: false on a named model of the corpus, so that a proof has to use the arithmetic. T6: every named input is a Lean statement and none is refuted in Lean. T7: not of a shape the corpus has answered. A question that fails a test is reported with the failure.

## 2.1 Just-work tasks

Tasks solvable with known methods. None of them moves a receiver.

| ID | Task | What exists | What is to do |
|---|---|---|---|
| J1 | Restate at 20999/24000 | Stated at 7/8: [`heckeHalfPlane_seven_eighths`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRayClassFunctionOfTheEisensteinFieldCarriesTheSeed.lean#L181), [`heckeHalfPlane_rat_seven_eighths`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheHeckeFamilyOfTheRationalsCarriesTheSeed.lean#L137), [`heckeXi_cubicTwoHecke_ne_zero`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheArtinFunctionOfTheCubeRootsOfTwoCarriesTheSeed.lean#L147), the Bianchi strip [1/8, 7/8] ([`bianchiZeta_zero_mem_quasiRH_strip`](../../../formal/GaloisForLFunctions/RingdownOfTheCubicCover/UnconditionalScatteringResonanceBounds.lean#L108)); stated at width 3/8: the multiplicity envelope ([`exists_zero_multiplicity_cosine_envelope`](../../../formal/GaloisForLFunctions/SquareRootThreshold/SechMultiplicityEnvelope.lean#L91)), the lag growth rate of WL, the ringdown strips of PM | Substitute the half-plane of [`hecke_ne_zero_of_sub_seven_eighths_lt_re`](../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/SubSevenEighthsZeroFreeHalfPlane.lean#L111), which covers every finite-order Hecke L-function of ℚ(ω) and every Dirichlet L-function |
| J2 | Jensen rung | Real-rooted through degree 31922 from width 3/8 at height 67; the budget is (d−1)·w² ≤ 67² ([`degree_31923_exceeds_height_width_budget`](../../../formal/GaloisForLFunctions/VerifiedHeightRungs/TheJensenPolynomialsThroughDegree31922AreRealRooted.lean#L33)) | With w = 8999/24000 the same inequality admits d ≤ 31929 (4489·(24000/8999)² ≈ 31928.9) |
| J3 | Integrate source-only modules | Graded [S]: the floors at aperture log 2 ([TheEvenWeilFormHasAFloorAtApertureLogTwo](../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheEvenWeilFormHasAFloorAtApertureLogTwo.lean), [TheOddWeilFormHasAFloorAtApertureLogTwo](../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheOddWeilFormHasAFloorAtApertureLogTwo.lean), [TheTwoPrimeWindowHasAPositiveWeilFloorAtEveryBlockSize](../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheTwoPrimeWindowHasAPositiveWeilFloorAtEveryBlockSize.lean)) and ratio three ([TheTwoPrimeWindowAndRatioThreeHoldAtEveryBlockSize](../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheTwoPrimeWindowAndRatioThreeHoldAtEveryBlockSize.lean)); the half-line items of HF ([ArithmeticHawkingPagePhaseStructure](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ArithmeticHawkingPagePhaseStructure.lean) and its companions); the prime-two deformation test ([PrimeTwoDeformedApertureLogTwoTest](../../../formal/GaloisForLFunctions/BlackHoleRingdown/PrimeTwoDeformedApertureLogTwoTest.lean)); the cubic Stepanov modules ([TheCubicStepanovPolynomialIsIndependent](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheCubicStepanovPolynomialIsIndependent.lean), [TheCubicStepanovCount](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheCubicStepanovCount.lean)); [TheCalibrationCurvesArePureByTheirPairing](../../../formal/GaloisForLFunctions/TensorPowerProgramme/TheCalibrationCurvesArePureByTheirPairing.lean); the Kummer constant-field period and principal-divisor saturation; the modular strip 3001/48000 | Finish, wire and source-review each module |
| J4 | Artin completions | Brauer induction and a completion with functional equation for every Artin L-function ([EveryArtinLFunctionHasACompletionWithAFunctionalEquation](../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/EveryArtinLFunctionHasACompletionWithAFunctionalEquation.lean)) | Conductor exponent at a ramified prime and the Gamma factor as invariants of the representation (*table*: question 5 of the absolute-geometry programme) |
| J5 | Tools of the tensor-power programme | Its README lists as "to build": Hecke characters of ℚ(ω) with infinity type as an abelian base; the dual series of the cubic probe (Q6, "not written"); the Stickelberger price of the A₂ coefficients (Q5, "not computed") | The first needs the prime number theorem of each character; nonvanishing on Re w ≥ 1 of the Grössencharacter L-functions is in [GrossencharacterLFunctionsHaveZerosInTheRightHalfStrip](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/GrossencharacterLFunctionsHaveZerosInTheRightHalfStrip.lean). The other two are computations |
| J6 | Order-six Kubota series | *Table* (reciprocity-families programme): "the corpus has the cubic Eisenstein series, its residue and the cubic theta coefficients; it has neither the sextic metaplectic Eisenstein series nor a sextic large sieve" | Continuation and functional equation of the order-six series over ℚ(ω) are classical. The residue in closed form and the remainder uniform in the column are not (O2) |
| J7 | Infinity type inside the probe | The seeded family [`Character`](../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Hecke/HeckeCharactersAndThetaProducts.lean#L613) has the fields modulus, residue character and period, and no infinity type; the theta-to-Gauss conversion [`fixedThetaTwist`](../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Eisenstein/CuspAveragesAndBesselMellin.lean#L417) is stated for an arbitrary multiplicative twist | Extend the family type and the completed rows to angular characters. The estimate for the extended family is O3 |
| J8 | Fixed-aperture certificates | Floors at 1881/5000 [L] and log 2 [S]; index at ratio four ≤ 300000 at every block size [L] ([`hermNegIndex_blockWindow_ratioFour_le`](../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheStepPacketMatricesOfARatioAreDecidedOnCoarseBlocks.lean#L538)) | Each further aperture is a finite certificate. The floor it has to resolve is at most K·exp((11/2)A − π·e^(2(A−2))) at aperture A ≥ 3 [L] ([`not_exists_positive_floor_along`](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/TheApertureFloorMustDecayDoublyExponentially.lean#L110)), so the precision grows doubly exponentially. No fixed aperture gives the uniform step |
| J9 | Finite rungs | Li signs n ≤ 314, PF₂₀₀, theta ranks ≤ 14, character minors through order 200, Jensen degrees (J2) | A larger verified height extends each list |
| J10 | Cubic character sums | [`cubic_stepanov_count`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheCubicStepanovCount.lean#L188) [S]: ℓ·#{x : h(x) ≠ 0, h(x)^N = ε} ≤ (K−1) + 2N·deg h + Q(J−1) | The parameter choice is made in [`cubic_stepanov_bound`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheCubicCurveCountWithoutWeil.lean#L96) (src): 3·#{x : h(x)^N = ε} ≤ s² + (5D+4)s for a field of s² = 3N+1 elements and s ≥ 3D+10. The equidistribution of the three classes and the count of points on y³ = h(x), named in that module's header, are not declarations. The transfer to a signed estimate over ℤ[ω] is not work (O1–O3) |
| J11 | The top-octave statement for ζ | [`doublingLaw_of_sub_three_eighths_lt`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheAbscissaAvoidsAnIntervalBelowSevenEighths.lean#L356) [L] gives doubling laws with factor 2^β, β > 8999/24000; [`topOctave_jump_of_doublingLaw_lt_sqrt_two`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L663) [L] turns any factor below √2 into a state v with Σ_(k=3K+2)^(6K+1) ⟨v, floorGraph(k) v⟩ < −(√K/4000)‖v‖² | Compose the two into one unconditional theorem for the actual windows on a polynomial block schedule, and make the state v explicit. The composition is a consequence of two [L] statements and is not a declaration of the corpus |

## 2.2 Open obstacles

Problems with no known solution. Each entry: the statement, what is proved around it, and why the proved facts do not reach it.

### Family P — producer

**O1. Row count in the binding bins.** The probe's budget is tight in three bins δ ∈ {5/13, 79/204, 16/41} ([`endpointExponent_three_bin_pos_of_lowBoundaryGen_le`](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheTrueVertexBelowSevenEighths.lean#L328) [L]). The published count in the bin 79/204 has exponent ≥ 21766/32589 − 10⁻⁴ against 1 − δ = 125/204 ([`rowCountAt_binding_ge`](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSevenEighthsGeometryIsAVertex.lean#L436)); the vertex is stable for counts within 10⁻⁴ ([`endpointExponent_pos_of_lowBoundary_le_of_rowCount`](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSevenEighthsGeometryIsAVertex.lean#L466)); with the count U^(1−δ) in every bin the balanced geometry reaches 13/15 ([`endpointExponent_balanced`](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSevenEighthsGeometryIsAVertex.lean#L541)). The exponent 1 − δ + ε is derived in Lean from the published count only in the bins δ ≥ 5/6 ([`high_bin_count`](../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Hecke/DetectorRowCounts.lean#L859)). The count comes from the cubic large sieve with cross term (MN)^(2/3) ([`sieveNorm_sharp`](../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/CubicSieve/HeathBrownIteration.lean#L1221)).

**O2. A signed evaluation before Cauchy–Schwarz.** One reflection closes every positive L² row sieve at the boundary 5/6 ([TheMetaplecticVoronoiExponentInvariants](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheMetaplecticVoronoiExponentInvariants.lean) [L]); boundary 3/4 needs a signed saving ≥ 1/12 and boundary ½ needs ≥ 1/3 ([ledger](../rh-killed-routes.md#phase-blind-floor-gram) [L]). Proved: the Gram of two short rows is diagonal up to O(U^(−A)) when N(u₁u₂) ≤ U^(1−ε) ([`norm_gramEntry_le`](../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/TheShortSexticGramIsDiagonal.lean#L123)); the reflected Gram is twisted by the row root numbers and has rank one at sixth-power frequencies ([`gramCoeff_eq`](../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/TheReflectedGramIsTwistedByTheRowRootNumbers.lean#L126), [`gramCoeff_sixthPower`](../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/TheReflectedGramIsTwistedByTheRowRootNumbers.lean#L216)); the root number carries the Möbius sign ([`rowGauss_product`](../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/TheRowRootNumberCarriesTheMoebiusSign.lean#L118)). Open: the first moment of Φ = Gγ₂² over long columns with a remainder uniform in the column (*table*: with the main term and a square-root remainder the floor-bin curve reaches 2/3). No statement of the corpus gives a signed off-diagonal saving in the range N(u₁u₂) ≥ U.

The untwisted squarefree theta series `S₁(w)` now has an explicit nonzero simple pole at `w=2/3` ([`untwistedSquarefreeSeries_holomorphic_simple_pole`](../../../formal/GaloisForLFunctions/SpectralTheoryOfTheCubicCover/TheUntwistedContinuationHasNoMellinPoles.lean#L148) [L]). Opposite translations by `±ω` isolate its unramified square: `D−C_U=(3/2)D₀`; the one-cusp subtraction gives `C_U` one quarter of the full double-pole residue. For `W(y)=exp(−(log y)²/4)/(2√π)`, its actual signed ideal sum now satisfies `Σ_A σ(A)W(N(A)/X)=exp(4/9)R X^(2/3)+O_a(X^a)` for every `5/8<a<2/3`, with `R≠0` ([`gaussianSmoothedUntwistedTheta_main_term`](../../../formal/GaloisForLFunctions/SpectralTheoryOfTheCubicCover/TheUntwistedThetaSeriesHasASmoothedMainTerm.lean) [L]). Self-adjoint vertical control and removal of real spectral poles make the Gaussian contour shift possible. The conductor-phase transfer to row-root moments, sharp cutoffs and column-uniform remainder remain open.

**O3. A rung seed.** The correction of the cubic probe has abscissa (3 + Θ_rung)/6 ∈ [7/12, 2/3] exactly ([`correctionAbscissa_eq`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheCorrectionOfTheCubicProbeCarriesTheAbscissaOfItsRung.lean#L126) [L]); the rung L(w, ψ₆^k ψ) has no zero on Re w ≥ 1 and infinitely many in ½ ≤ Re w < 1 ([`infinite_zeros_grossenLFunction_right_half_strip`](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/GrossencharacterLFunctionsHaveZerosInTheRightHalfStrip.lean#L467)); its Euler factor away from 3 is the 18k-th power of the conjugate normalized cubic Gauss sum times a finite-order twist ([`grossenPrimeTerm_eq_conj_normalizedCubicGauss`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheRungsAreTensorPowersOfTheCubicGaussSums.lean#L48) [L]); no rung is a quotient of products of finite-order Hecke L-functions ([`not_grossenLFunction_mul_prod_eq`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheRungsLieOutsideTheSeededFamily.lean#L420) [L]). Open: any zero-free half-plane Re w > b, b < 1, for a Grössencharacter of nonzero infinity type. The search of this review found none in the corpus.

Angular physical compensation has an exact limitation: it transfers weight `k` from the column
to frequency, hence weight `6k` to the free sixth-power ideal. That free Euler factor is regular
and nonzero at `z=1/6`, with zero residue, although the angular Mellin normalizer remains positive
([`angular_sixthFrequencyWeight`, `continuedAngularSixthFactor_zero_residue`](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/AngularSixthPowerFactor.lean) [K]). This does not factorize the full compensated source or supply a rung estimate.

**O4. A joint completion on the sign line.** Every Möbius-signed Gauss pairing completed factor by factor has coupled boundary ≥ 3/5 ([`not_exists_moebiusGaussPairing_lt_three_fifths`](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/MoebiusSignedGaussPairingsEndAtThreeFifths.lean#L770), [`sInf_coupledBarrier_eq_three_fifths`](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/MoebiusSignedGaussPairingsEndAtThreeFifths.lean#L859) [L]). The sign itself costs k/2 ([`half_mul_period_le_pairingC`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheGaussPairingsArePricedAboveTheSign.lean#L126)), short monomials pay exactly k/2 ([`stickelbergerPrice_eq_half_mul`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheShortMoebiusMonomialsPayExactlyHalf.lean#L97)), and towers on the sign line have values tending to ½ ([`exists_towerValue_signLine_lt`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheShortMoebiusMonomialsPayExactlyHalf.lean#L157)). The wall 3/5 is a wall of the completion class. Open: a completion of a signed monomial of period k ≥ 7 that is not factor by factor, with an estimate. The rank-two test is negative: no cone of absolute convergence of the A₂ series meets the critical slice ([`not_weylCone_interior_strip`](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheRankTwoMultipleDirichletSeriesConvexityHull.lean#L148)).

**O5. A pole law with an independent source.** For flow data and for abelian bases the pole law of the even tensor moments is equivalent to the width ([`exists_poleLaw_iff`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/TheTensorMomentsOfAFlowDatumHaveBaseLossExactlyOne.lean#L510), [`exists_twistPoleLaw_iff`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/AnAbelianBaseIsARuler.lean#L568) [L]); for ζ itself the moment exponents satisfy 2kw ≤ a_k ≤ 1 + 2kw and the pole law at weight w₀ holds iff w ≤ w₀ ([`exists_momentPoleLaw_iff`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/ThePrimeTraceMomentsOfZetaReadTheWidthWithBaseLossAtMostOne.lean#L223) (src)); a polarized base whose Adams squares continue to Re s > 1 is pure, and that continuation for all powers is temperedness ([`norm_eq_one_of_adamsPoleLaw`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/APolarizedBaseWhoseAdamsSquaresContinueIsPure.lean#L93), [`adamsPoleLaw_iff`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/TemperedIsTheUniformTopBound.lean#L87) [L]); a pencil through ζ exists iff RH ([`riemannHypothesis_iff_nonempty_pencil`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/TheAxiomsOfAPencilThroughZeta.lean#L188) [L]). One valid Deligne lever, or valid sign levers at all large periods, give RH ([`riemannHypothesis_of_deligneLever`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/TheThreeLinesOfFrames.lean#L84), [`riemannHypothesis_of_signLevers`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/TheThreeLinesOfFrames.lean#L94) [L]). Open: a source of the pole law that does not contain the zeros. The candidates examined are rulers: the heat family has a Dirichlet series only at time 0 ([`exists_dirichlet_iff`](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/OnlyTheUndeformedKernelHasADirichletSeries.lean#L623)), twist families are abelian, the calibration curves are pure by an identity of two pairings ([`norm_jacobiSum_sq`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/TheCalibrationCurvesArePureByTheirPairing.lean#L47) [S]).

**O6. Half-power cancellation.** The receivers MC, JAS, SQF, PBM, RB, SZ, TT, S3 ask for the exponent ½ + ε of one explicit prime sum. The seed lever has wall 20999/24000 under composition and minima ([`wall_subSevenEighthsLever`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheAbscissaAvoidsAnIntervalBelowSevenEighths.lean#L148) [L]). Every frame whose centre is below 2/3 fails to be a lever on an integer-norm Euler world and on an entire model with the functional equation, and below 1 on a shifted pair ζ(s−a)ζ(s+a) ([`exists_world_not_isLever_frame`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L166), [`exists_shiftedPair_not_isLever_frame`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L312)): a proof has to use Euler product, functional equation and coefficient size together. O1–O5 are the staged form of O6.

**O7. Root coincidences for k = 2, …, 6.** ζ(ρ) = ζ(ρ/k) = 0 forces Θ ≥ k/(k+1) ([`abscissa_ge_of_zeta_zero_div_nat`](../../../formal/GaloisForLFunctions/ZeroForcingCalculus/EulerDilationAndRootCoincidenceExclusion.lean#L174)), which excludes k ≥ 7 ([`riemannZeta_div_nat_ne_zero_of_seven_le`](../../../formal/GaloisForLFunctions/ZeroForcingCalculus/EulerDilationAndRootCoincidenceExclusion.lean#L212) [L]). The thresholds for k = 6, …, 2 are 6/7, 5/6, 4/5, 3/4, 2/3. A halving pair forces Θ ≥ 2/3 ([`two_thirds_le_abscissa_of_halving_pair`](../../../formal/GaloisForLFunctions/ArithmeticHolographyOfTheModularHorizon/HalvingDescentAndShimuraZeros.lean#L40)), and one Hecke eigenform does not see a resonance ρ/2 with ζ(ρ/2) = 0 ([`pairing_half_eq_zero`](../../../formal/GaloisForLFunctions/ArithmeticHolographyOfTheModularHorizon/OneHeckeEigenformIsBlindToHalvingPairs.lean#L716)). A zero ρ/k with k ≥ 2 lies left of the line, so each coincidence is a special configuration of off-line zeros; its exclusion is weaker than RH.

### Family R — sign

**O8. The sign at every aperture.** Proved for all tests: floors at 1881/5000 [L] and log 2 [S]. A window sign at one aperture, at ζ's density, is compatible with infinitely many zeros at any depth ([`exists_zetaDensity_positive_window_deep_zeros`](../../../formal/GaloisForLFunctions/SelectiveArithmetic/TheRungSignSurvivesDeepZerosAtZetaDensity.lean#L90)); the first overlap step fails for the sign twin of the prime 2 ([`exists_firstStep_window_signTwin_lt`](../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheFirstOverlapStepOfWeilsFormFailsForTheSignTwin.lean#L744)) and the Liouville twist fails beyond the trivial aperture log log q + o(1) ([`exists_not_feasible`](../../../formal/GaloisForLFunctions/SelectiveArithmetic/TheLiouvilleTwistFailsBeyondTheTrivialAperture.lean#L573)). The complete tilted-spline matrix is positive definite for overlaps c ≤ (log N)^α, α < 1/8 [L] ([`eventually_tiltedUnitSpline_spectralFloorWeilMatrix_posDef_below_one_eighth`](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheCompleteWeilMatrixIsPositiveDefiniteBelowTheEighthRoot.lean#L37)). Current corpus source also gives positivity on the whole horizon, uniformly for `1 ≤ c ≤ 2K(log N)^(1/8)` at one fixed `K>0` ([`exists_critical_multiple_completeWeilMatrix_posDef`](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheCompleteWeilMatrixIsPositiveAtACriticalMultiple.lean#L145), (src), umbrella-wired). Open: positivity at every critical multiple.

At each positive critical ratio, the nonpolar low-packet collar cost tends to zero ([`tendsto_nonpolar_lowPacket_collar_schur_cost`](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/NonpolarCollarResidualsVanish.lean#L203), (src), umbrella-wired). The remaining polar payment at every ratio already implies RH ([`riemannHypothesis_of_polarPayment_on_growing_windows`](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheLowPacketPaymentAtEveryRatioIsTheRiemannHypothesis.lean#L98), (src), umbrella-wired); the all-ratio step is not routine assembly.

**O9. A doubling factor below √2 from the matrices.** √2 holds for every bounded contact-weight model without a zero-free region ([`doublingLaw_sqrt_two`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L149)); the sub-Euler model, whose weights lie in {0, 1}, equal ζ's through any prescribed cutoff and give the same dyadic middles, admits no smaller factor ([`not_reweightedDoublingLaw_of_lt_sqrt_two_subEulerGluingWeight`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L174)). For ζ a factor 2^β with β > 8999/24000 holds [L]; its proof passes through the zero-free half-plane. Open: a proof from the window matrices (§2.5).

**O10. An effectivity, section or count law that does not contain the sign.** HodgeIndex ⇔ an effectivity with Riemann–Roch and ampleness ([`exists_effectivity_iff_hodgeIndex`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HodgeIndexFromEffectivity.lean#L102)); the exact arithmetic source cone is the positive cone ([`exactArithmeticSourceCone_eq_positiveCone`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ExactArithmeticSourceEffectivity.lean#L97)); the Chebyshev majorant cone has Bézout and ampleness and fails Riemann–Roch ([`arithmeticMajorantSourceCone_not_riemannRoch`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticMajorantsSupplyBezout.lean#L152)); a quadratic form is the Tate limit of a count iff it is nonnegative ([`exists_count_tateLimit_iff`](../../../formal/GaloisForLFunctions/CountingHolography/TheCountDoorOfACurveAndOfZ.lean#L39)), and the integer probes are not integer valued ([`not_integerProbe_integerValued`](../../../formal/GaloisForLFunctions/CountingHolography/TheIntegerProbesAreNotIntegerValued.lean#L321)); Hecke symmetry gives conservation on true and fake data alike ([`hecke_conservation_without_law`](../../../formal/GaloisForLFunctions/CountingHolography/HeckeSuppliesConservationNotTheLaw.lean#L71)). Integrality, functional equation and positive Euler data do not force the sign ([`goldenDatum_beurling`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheGoldenCurveIsABeurlingSystem.lean#L582)). For HF the same obstacle is the exclusion of the finite-W state; stability, outerness and endpoint competition do not exclude it ([ledger](../rh-killed-routes.md#confining-stability-exclusion) [S]).

**O11. Arithmetic separation — resolved for finite products of rational Euler deformations.** The prime-two deformation ξ_α = primeTwoFactor(α)·ξ ([`xiDeformed`](../../../formal/GaloisForLFunctions/BlackHoleRingdown/CausalIdentitiesCannotForceQuarterRingdown.lean#L215)) keeps functional equation, passivity, Herglotz admittance, unitarity on the continuous spectrum and an Euler product, has off-line zeros, and is window-positive up to half-width (log 2)/2 ([`half_log_two_le_onsetAperture_xiDeformedZeroConfig`](../../../formal/GaloisForLFunctions/BlackHoleRingdown/PrimeTwoDeformedApertureLogTwoTest.lean#L185) [S]); every deformation has a finite onset aperture ([`onsetAperture_xiDeformedZeroConfig_lt_top`](../../../formal/GaloisForLFunctions/BlackHoleRingdown/PrimeTwoDeformedApertureLogTwoTest.lean#L196) [S]). A finite arithmetic separator is now proved [K]: ζ has Euler logarithmic coefficient `1/k` at `p^k` ([`eulerLogDirichletCoeff_prime_pow_succ`](../../../formal/GaloisForLFunctions/HTGeometry/CanonicalEulerLog.lean#L38)), whereas every real reciprocal quadratic Euler modification has a negative coefficient at one of `p²,p⁴,p⁶,p⁸` ([`exists_negative_even_eulerLogCoeff`](../../../formal/GaloisForLFunctions/SelbergClass/PositiveFiniteEulerLogarithmicSigns.lean#L47)).

Ordinary coefficient positivity does not supply this separator. Positive, bounded, multiplicative twins match any prescribed finite ζ prefix, retain an entire reflection-symmetric completion, holomorphic contractive scattering and unitarity, and have a zero at any prescribed `1/2<σ<1` ([`exists_positive_passive_twin`](../../../formal/GaloisForLFunctions/BlackHoleRingdown/ThePositiveEulerTwinsArePassive.lean#L360) [K]). Their coefficients satisfy `a(p)²>2a(p²)` and no nonnegative, absolutely convergent logarithmic Dirichlet series represents them on any right half-plane. The named prime-two family already fails ordinary coefficient positivity ([`not_exists_nonnegative_primeTwo_representation`](../../../formal/GaloisForLFunctions/BlackHoleRingdown/ThePositiveEulerTwinsArePassive.lean#L81)).

The separator extends to every reduced rational function of one Euler coordinate: a nontrivial `P(p⁻ˢ)/Q(p⁻ˢ)` cannot have both an entire reflection-symmetric completion `e^(cs)ξ(s)P/Q` and an absolutely convergent logarithmic Dirichlet representation with nonnegative real coefficients ([`not_exists_nontrivial_positive_rational_twin`](../../../formal/GaloisForLFunctions/SelbergClass/RationalEulerTwinsCannotHavePositiveLogarithms.lean#L167) [K]). ξ cannot cancel a complete denominator fibre; one-sided power-sum recurrence and reflection exclude the numerator. The result now covers finite products of reduced rational modifications at distinct primes: every nontrivial edit with an entire reflected completion forces negative logarithmic coefficients at arbitrarily large powers of one edited prime ([`finite_rational_twin_has_negative_prime_power_logs`](../../../formal/GaloisForLFunctions/SelbergClass/FinitePrimeRationalEulerRigidity.lean) [K]). Infinitely many ξ-nonzeros on each Euler fibre and finite intersections between distinct-prime fibres prevent cross-prime denominator cancellation. Mixed rational functions of several Euler coordinates, infinite prime edits and arbitrary rational-in-`s` Beurling modifications remain outside this classification.

### Family U — uniformity

**O12. AAL.** Receivers: window non-attainment at one length per depth ([`asymptoticAbscissaLaw_of_windowNonAttainment`](../../../formal/GaloisForLFunctions/FloorFreeArithmetic/NonAttainmentGivesTheAbscissaLaw.lean#L54)), one bounded phase return at each off-line zero ([`asymptoticAbscissaLaw_of_infinite_zeros`](../../../formal/GaloisForLFunctions/ArithmeticAuxiliaryDynamics/TheMissingInputOfTransport.lean#L236)), a lower bound at very smooth degrees ([`asymptoticAbscissaLaw_of_bddBelow_verySmooth`](../../../formal/GaloisForLFunctions/SurfaceOfSpecZ/VerySmoothDegreesNeedAnAttainedTop.lean#L889)), a 2k-th window moment at depth A/2k ([`abscissaLawAt_of_window_moment`](../../../formal/GaloisForLFunctions/FloorFreeArithmetic/TheOrderOfAMomentIsTheDepthItReaches.lean#L49)). Realizability: every finite datum of depth below ½ is the top layer of an integer-norm Euler system ([`eulerSymmetric_layerConfig`](../../../formal/GaloisForLFunctions/FloorFreeArithmetic/TheZeroConfigurationDoesNotSeeTheEulerProduct.lean#L247); the class has floor ½); unless AAL holds, a meromorphic tempered Euler model with exactly one off-line pair right of Θ exists ([`asymptoticAbscissaLaw_or_exists_meromorphic_tempered_euler_oneOff`](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/TheMeromorphicTemperedEulerFirewall.lean#L1687)); integer-norm edits of the primes with functional-equation defect of mean square T^ε vanish at prescribed points ([`frontier_dichotomy`](../../../formal/GaloisForLFunctions/WorldsOfTheZeroConfiguration/FakeEditsWithSubpolynomialDefectEnergy.lean#L699)). Rigidity: a decaying defect O(|t|^(−1/2+ε)) forces the rational primes ([`beurlingSystem_rigidity_of_decaying_defect`](../../../formal/GaloisForLFunctions/EulerFETransportTheory/DecayingFunctionalEquationsDetermineThePrimes.lean#L579)). No statement uses the exact functional equation and integrality together against a finite layer.

**O13. ZAL and landing.** RH ⇔ ZAL ∧ (finite off-line set ⇒ RH) ∧ landing ([`riemannHypothesis_iff_three_atoms`](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheLandingLawForZeta.lean#L68)). Functional equation, reality and order one do not give ZAL-to-line landing ([`approachingModel_eq_zero_iff`](../../../formal/GaloisForLFunctions/InfiniteRankWeilTheory/TheFunctionalEquationAdmitsApproachingRemainders.lean#L312)); finiteness of the non-real zeros of every H_t, t > 0, does not pass to t = 0 ([`heat_finiteness_does_not_pass`](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheLandingLawForZeta.lean#L191)).

**O14. Reality inside near-coincidence clusters.** An off-line zero of depth d at height X gives Λ_X ≥ c·d²/log X ([`exists_le_localNewmanConstant_of_offLine_zero`](../../../formal/GaloisForLFunctions/RHTower/Heat/TheLocalDeBruijnNewmanConstant.lean#L157)); the start is dominated for t ≥ (6600/9991 + ε)/log X ([`riemannHeat_zeros_real_simple_subWeyl`](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/HeatScaleRepulsion/SubWeylCollisionFreeHorizon.lean#L1166)). *Table* (zero-configuration programme): size domination is impossible below ½/log X; the open step is the sign of an image Hankel determinant, or a Hermite–Biehler half of the heat source, at the Gaussian saddle. Width alone does not bound the heat time from below: cosine models of fixed width have heat time → 0 ([`exists_cosDefect_width_heatTime_lt`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheHeatTimeIsTheWidthTimesTheSpacing.lean#L109)).

**O15. One exponent for all orders.** RH ⇔ the even prime-trace moments have one growth exponent ([`riemannHypothesis_iff_moments_primeTraces`](../../../formal/GaloisForLFunctions/SurfaceOfSpecZ/TheTensorPowerTrick.lean#L34)); the top bound one for all Adams powers is temperedness (O5); a bound routed through gauge moments of order k loses at least linearly in k ([`pow_sum_normSq_le_sum_normSq_powCoeff`](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/MultiplicativeAmplificationLosesLinearly.lean#L102)), and a loss law sublinear in k excludes every positive depth ([`nonpos_of_sublinear_loss`](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/MultiplicativeAmplificationLosesLinearly.lean#L71)); long mollifier moments have slope loss exactly 2w. Each finite order is available; the uniformity is the statement.

**O16. The sign of the forward monodromy group.** G₊ has index ≤ 2 in the signed permutations of finite support, and is proper iff one parity law holds; then 8 divides every real collision mass ([`eight_dvd_collisionMass`](../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ARealCollisionOfMassNotDivisibleByEightGivesEverySignedPermutation.lean#L174) [L]). An isolated double collision off the centre at a forward time gives the full group ([`mem_forwardMonodromy_of_isolated_double_collision`](../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheTurnAroundAnIsolatedDoubleCollisionOffTheCentreIsTheExchangeOfTwoPairs.lean#L162)). Open: which case holds. The answer is not equivalent to RH.

## 2.3 Frankenstein routes

Chains to RH assembled from proved pieces of different programmes, with the missing links named.

**F-A. Seed × lever calculus × frames** (family P).

| Link | Piece | Status |
|---|---|---|
| 1 | Seed Θ ≤ 20999/24000 (metaplectic descent) | [L] |
| 2 | Covering criterion: levers covering (½, 20999/24000] give RH (zero-forcing calculus) | [L] |
| 3 | Frames (c, k) with one-step bound (c + b)/k and tower centre c/(k−1); bound = max(estimate floor, centre) (family continuation, exponent dynamics) | [L] |
| 4 | The three lines: Deligne c = (k−1)/2, sign c = k/2, completion c = 2k/3 − 1 (tensor-power programme) | [L] |
| 5 | Valid levers on (13/15, 20999/24000] | O1 |
| 6 | Valid levers on (2/3, 13/15] | O2 |
| 7 | Valid levers on (3/5, 2/3] | O3 with link 6 |
| 8 | Valid levers on (½, 3/5] | O4, then O5 for all periods |

**F-B. Window gluing × width ruler** (families R and P).

| Link | Piece | Status |
|---|---|---|
| 1 | Index one through ratio 103/50 at every block size (absolute geometry: [`hermNegIndex_neutralWindow_eq_one`](../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheNeutralPartOfAWindowOfRatioTwoHasOneNegativeSquareAtEveryBlockSize.lean#L315)); gap 1/50000 through ratio 10609/5000 | (src); [L] |
| 2 | Gluing through the dyadic middle: index one ⇔ a Schur complement condition; additive loss below the binding energy of the middle (Green calculus: [`hermNegIndex_neutralWindow_add_le_one_of_schurLevel`](../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheLossOfAnOverlapStepIsAdditiveBelowTheBindingEnergyOfTheMiddle.lean#L422)) | (src) |
| 3 | RH from a level function with values in [0,1] whose increments dominate the conditional couplings ([`riemannHypothesis_of_level_function`](../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheLossOfAnOverlapStepIsAdditiveBelowTheBindingEnergyOfTheMiddle.lean#L668)) | (src) |
| 4 | Any doubling factor λ gives the half-plane Re s > ½ + log₂ λ (exponent dynamics: [`riemannZeta_ne_zero_of_doublingLaw`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L793)) | [L] |
| 5 | A factor below √2 from the matrices | O9 |
| 6 | A level function, equivalently summable conditional couplings | O8 |

**F-C. The split RH ⇔ ZAL ∧ AAL** (family U).

| Link | Piece | Status |
|---|---|---|
| 1 | RH ⇔ ZAL ∧ AAL (infinite-rank Weil theory) | [L] |
| 2 | AAL ⇔ no finite nonempty top layer (zero-configuration geometry) | [L] |
| 3 | AAL from window non-attainment, a bounded phase return, very smooth degrees, or shell signs on infinitely many dyadic prime shells (floor-free arithmetic, auxiliary dynamics, surface of Spec ℤ, joint ancestry) | [L] |
| 4 | One of the inputs of link 3 | O12 |
| 5 | ZAL | O13 |

F-A is the only chain in which a link has been closed by a theorem about ζ (link 1). F-B and F-C have complete receivers and no closed arithmetic link.

## 2.4 A question less hard than RH that moves the zero abscissa

**Question.** In the bins δ ∈ {5/13, 79/204, 16/41} of the cubic probe, at full prime amplitude, is the number of rows with a large row sum bounded by U^(c(δ)) with c(79/204) < 21766/32589 − 10⁻⁴?

- **Consequence (T3).** The vertex leaves its interval: [`endpointExponent_pos_of_lowBoundary_le_of_rowCount`](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSevenEighthsGeometryIsAVertex.lean#L466) pins the obstruction to counts within 10⁻⁴ of the published one, and with c(δ) = 1 − δ the budget closes at 13/15 ([`endpointExponent_balanced`](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSevenEighthsGeometryIsAVertex.lean#L541)). Below 13/15 the floor bin blocks the same probe ([`endpointExponent_floor_bin_pos_of_lowBoundary_lt`](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSevenEighthsGeometryIsAVertex.lean#L499)).
- **Tests.** T1 passes: the outcome is a zero-free half-plane between 13/15 and 20999/24000. T2 passes. T4 passes. T6 passes: the inputs are exponent identities of the published estimates. T7 passes: the corpus has the count only for δ ≥ 5/6. T5 is untested: no model of the corpus has a row count.
- **Reading.** The statement has the shape of a density hypothesis for cubic twists. By recollection of the literature, not checked for this report and not in the corpus, the cross term (MN)^(2/3) of the cubic large sieve is optimal for general coefficients; an improvement would have to use the actual coefficients of the probe.

## 2.5 A question for a positivity producer

A positivity producer is a mechanism that outputs a lower bound of Weil's form at a growing aperture from prime data, without zero information. None exists in the corpus at any rate: the rate-½ floor is the trivial one (factor √2), and every better rate is a transfer of the seed through the ruler [`isRuler_logEnergyFloor`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWidthIsTheRateOfTheWeilFloorInTheLogarithmicEnergy.lean#L428).

**Question.** Prove a doubling law with a factor λ < √2 on a polynomial block schedule from the window matrices, without a zero-free region. A doubling law ([`DoublingLaw`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestDoublingFactorOfTheMarginIsTwoToTheWidth.lean#L136)) is a monotone sequence of levels a(K) with a(2K) ≤ λ·a(K) + c at which the neutral windows of ratio 3K + 1 hold at most one bound state.

- **The statement is true.** Factors 2^β, β > 8999/24000, hold [L]. The question is a proof that does not pass through the zero-free half-plane.
- **Consequence (T3).** [`riemannZeta_ne_zero_of_doublingLaw`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L793) turns the law into the half-plane Re s > ½ + log₂ λ, a second proof of a zero-free half-plane left of 1 that is independent of the metaplectic probe; every improvement of λ is an improvement of Θ.
- **What a proof has to establish.** By [`topOctave_jump_of_doublingLaw_lt_sqrt_two`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L663) a factor below √2 forces, for all large K, a state v ≠ 0 on which the fresh prime octave is negative of the full order: Σ_(k=3K+2)^(6K+1) ⟨v, floorGraph(k) v⟩ < −(√K/4000)·‖v‖². The glued matrix without the top octave has two negative squares up to the shift √K/2000 − 40000 ([`eventually_two_le_hermNegIndex_neutralWindow_halfCutoff`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L472)), and the octave has to remove the second one.
- **What is known about the operator.** The floor graphs of the top octave vanish on both half-windows, on the middle and on the middle couplings and act only on the end-to-end block ([TheFloorGraphNormAndTopOctaveBlindnessOfWindowGluing](../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheFloorGraphNormAndTopOctaveBlindnessOfWindowGluing.lean) [L]); each has form norm ≤ 2Λ(k)/√k ([`abs_sum_floorGraph_le`](../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheFloorGraphNormAndTopOctaveBlindnessOfWindowGluing.lean#L97)), so the octave has total size O(√K): the required negativity is a fixed fraction of the trivial bound.
- **Tests.** T1 passes: every factor in (1, √2) is weaker than RH. T2, T4 pass. T5 passes: the sub-Euler model, whose weights lie in {0, 1}, equal ζ's through any prescribed cutoff and give the same dyadic middles, has no factor below √2 ([`not_reweightedDoublingLaw_of_lt_sqrt_two_subEulerGluingWeight`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L174)), so a proof has to use the contacts of the top octave beyond every finite cutoff. T6 passes. T7 passes: the search of this review found no proof of a factor below √2 that avoids the half-plane.
- **First step (work).** J11, with the state v written in terms of the seed.

## 2.6 A question under the premise that positivity, Weil positivity and spectral methods give nothing

Under this premise the estimate route remains. Inside it, positivity appears once more: every Cauchy–Schwarz row sieve is a positive L² form, and the reflection floor 5/6 is the wall of that class (O2).

**Question.** Evaluate, for squarefree rows u of norm ≍ U and a column of norm up to U^(1+η), the first moment Σ_u Φ(u)·(column character)(u), Φ = Gγ₂², with a main term and a remainder O(U^(1/2+ε)) uniform in the column.

- **Consequence (T3).** *Table* (reciprocity-families programme): with main term and square-root remainder the floor-bin curve passes 5/6 and 7/9 and reaches the completion wall 2/3; the stage ladder is 7/8 → 13/15 → 5/6 → 7/9 → 2/3 → 3/5. In Lean the consumer is the reflected Gram ([`gramCoeff_sixthPower`](../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/TheReflectedGramIsTwistedByTheRowRootNumbers.lean#L216)) and the requirement table of the phase-blind floor ([ledger](../rh-killed-routes.md#phase-blind-floor-gram)). The stage values 7/9 and the coherence radius 2/3 carry the table's own tags and are not Lean statements.
- **Tests.** T1, T2, T4 pass. T6: the inputs are Lean statements; the table records as a trap that the Möbius value and the angular character in the root number do not remove the metaplectic main term (the root number is a sextic Gauss sum, [ledger](../rh-killed-routes.md#dependent-sextic-twists) [L]), so the main term is part of the question. T7 passes. T5 is untested.
- **What is missing.** The order-six Kubota series uniformly in the column index (J6 for its classical part). By recollection of the literature, not checked for this report, the Fourier coefficients of metaplectic theta functions of order above three are not known in closed form; if so, the main term is itself open.

## 2.7 RH as the face of a physical phenomenon

**The phenomenon.** Ringdown of the modular horizon at the quarter rate. A compactly supported pulse on the modular surface decays like e^(−(δ−ε)τ) for every pulse iff no zero has Re ρ > 1 − 2δ ([`zeroFreeStrip_iff_pulse_ringdown`](../../../formal/GaloisForLFunctions/BlackHoleRingdown/TheRingdownRateIsTheZeroFreeStrip.lean#L625)); RH is the rate ¼ ([`riemannHypothesis_iff_pulse_ringdown`](../../../formal/GaloisForLFunctions/BlackHoleRingdown/TheRingdownRateIsTheZeroFreeStrip.lean#L650)). The same number is the thermalization rate of smoothed Farey counts ([`zeroFreeStrip_iff_fareyCount_rate`](../../../formal/GaloisForLFunctions/CountingHolography/ThermalizationFasterThanTheSquareRootIsAZeroFreeStrip.lean#L486)) and the horocycle exponent 1 − Θ/2 [L]. The zeros are the resonances of the horizon; the seed is a proved rate 1/16 [L] (3001/48000 [S]).

**What the corpus has falsified.** Every principle of physical type that was proposed as the cause of the rate holds on an object with a slower rate:

| Principle | Object on which it holds and the rate fails |
|---|---|
| Causality, passivity, Herglotz admittance, unitarity, Euler product | the prime-two deformations ξ_α [L]; [ledger](../rh-killed-routes.md#causal-prime-echo-decay) |
| KMS positivity at β = 1 | holds and decides nothing; [ledger](../rh-killed-routes.md#kms-horizon) |
| A half-sided modular inclusion carrying the Hecke clock | impossible: a positive generator commuting with an antiunitary involution vanishes ([`posGen_eq_zero_of_comm_antiunitaryInvol`](../../../formal/GaloisForLFunctions/CountingHolography/HalfSidedModularInclusionsCannotCarryTheHeckeClock.lean#L96)) |
| A sign on the dual side | is itself a rate ([`not_oneSided_of_seen`](../../../formal/GaloisForLFunctions/ArithmeticHolographyOfTheModularHorizon/TheDualSideHasNoSign.lean#L867)) |
| Stability of the vacuum (Hawking–Page) | the off-line saddle is not excluded [S] |
| Hyperbolic geometry alone | compact surfaces with small eigenvalues ([`exists_selbergZeta_small_eigenvalue`](../../../formal/GaloisForLFunctions/CompactHyperbolicSurfaces/EntireSelbergZeta.lean#L264) (src)) |
| Weight ½ | the theta function is an eigenfunction with eigenvalue 3/16 < ¼ ([`selberg_status`](../../../formal/GaloisForLFunctions/RHTower/SelbergConjectureStatus.lean#L34) (src)) |

So the rate is not a consequence of a physical principle in the corpus; physics supplies an exact dictionary. With exact functional equation and integer norms the horizon is alone in its class (O12, rigidity), and a law needs a class.

**A question that puts content on the phenomenon.** Take the class of congruence horizons Γ(N)\ℍ. Is the ringdown rate bounded below uniformly in the level, and what is the constant from proved inputs?

- **Inputs in Lean.** Cusp channel: no exceptional eigenvalue below 3/16 at any level and none below ¼ for levels ≤ 25 ([`selberg_status`](../../../formal/GaloisForLFunctions/RHTower/SelbergConjectureStatus.lean#L34) (src)). Continuous channel: every Dirichlet L-function is zero-free on Re s > 20999/24000 [L] ([`DirichletCharacter.LFunction_ne_zero_of_sub_seven_eighths_lt_re`](../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/SubSevenEighthsZeroFreeHalfPlane.lean#L141)); the scattering pole divisor of the principal congruence constant terms is the same at every level ([CongruencePolePersistence](../../../formal/GaloisForLFunctions/RenormalizedIntersectionTheory/MayerScattering/CongruencePolePersistence.lean) (src), module header).
- **Status.** The level-uniform law assembled from these inputs is not a declaration found by the search of this review. Its proof is work; it would be the first statement of the phenomenon for a class.
- **Falsifiers.** An exceptional eigenvalue at some level, or an off-line zero of a Dirichlet L-function. The quarter rate itself is false on the weight-½ horizon (eigenvalue 3/16) and on the deformations.
- **Tests.** T1, T2, T4, T5, T6 pass. T3 fails: no receiver of the corpus consumes a level-uniform rate. The question organises the physical face; it is not a step toward RH.
- **Reading.** The two channels stop at walls of the same kind. The wall 3/16 is sharp for every argument that is also valid in weight ½, where the theta function exists (module header of [SelbergConjectureStatus](../../../formal/GaloisForLFunctions/RHTower/SelbergConjectureStatus.lean)); the walls of the continuous channel are the coherent main terms of the sextic root numbers (O2). In both the obstruction is the residual spectrum of a metaplectic cover, and the cubic cover is also the source of the seed.

## 2.8 RH as topology or geometry

**The statements.** Three forms are theorems: index one of every neutral window ([`riemannHypothesis_iff_forall_hermNegIndex_neutralWindow_eq_one`](../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheRiemannHypothesisIsOneNegativeSquareOfTheNeutralPartOfEveryWindow.lean#L622)); triviality of the real-turn word of the heat monodromy (frontier map, ZCG [L]); nonnegativity of the Schur complement of every dyadic middle ([`riemannHypothesis_iff_forall_overlapSchur_nonneg`](../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheLossOfAnOverlapStepIsAdditiveBelowTheBindingEnergyOfTheMiddle.lean#L609) (src)).

**What is built.** The gluing calculus is complete: inertia additivity, the additive loss law, the level-function criterion (F-B). The realization problem has sharp obstructions: no coupling model of rank r with 600(r+1) ≤ H binds the two halves at ratio four ([TheBindingOfTheTwoHalvesOfAWindowOfRatioFourHasRankProportionalToTheBlockSize](../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheBindingOfTheTwoHalvesOfAWindowOfRatioFourHasRankProportionalToTheBlockSize.lean)), mixed areas of convex bodies are excluded and self-pairings are forced to be logarithmically negative ([TheCouplingsOfAWindowAreNotMixedAreasAndTheIndexForcesLogarithmicSelfPairings](../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheCouplingsOfAWindowAreNotMixedAreasAndTheIndexForcesLogarithmicSelfPairings.lean)), the arithmetic square has no normal direction of the diagonal in characteristic zero ([TheNormalDirectionOfTheDiagonal](../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheNormalDirectionOfTheDiagonal.lean)).

**Verdict on a question.** No question of topological type was found that passes all tests and bears on RH. Two candidates:

| Candidate | Passes | Fails |
|---|---|---|
| The sign of G₊ (O16): full group or the parity subgroup | T1, T2, T4, T6, T7; consumer: [`eight_dvd_collisionMass`](../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ARealCollisionOfMassNotDivisibleByEightGivesEverySignedPermutation.lean#L174) | the consequence is a mod 8 law for collision masses, not an exclusion |
| A level function for the dyadic recursion: a height L on windows with values in [0,1] whose increments dominate the conditional couplings | T2, T3 ([`riemannHypothesis_of_level_function`](../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheLossOfAnOverlapStepIsAdditiveBelowTheBindingEnergyOfTheMiddle.lean#L668)), T6 | T1 is undecided: the corpus has the implication to RH and no converse |

**The decidable step.** Whether the criterion can hold at all. Its hypothesis is a loss that sums below the binding energy along every path of the dyadic recursion, so it requires the conditional couplings at the levels of the criterion to be summable. An unconditional lower bound for these couplings along one path refutes the criterion and retires the candidate; an upper bound that is summable on the certified ladder to ratio three (four steps, [TheExcessOfAnOverlapStepAndTheFourStepLadderToRatioThree](../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheExcessOfAnOverlapStepAndTheFourStepLadderToRatioThree.lean)) gives the first values of a height. The corpus contains neither bound.

## 2.9 Is a further field needed for RH?

**Admission criteria.** A field is admitted when it has

- **F1** an object that no programme of the corpus defines;
- **F2** a first theorem about the object that is false on a named model of the corpus;
- **F3** a consumer: a receiver or a wall statement in Lean that the theorem moves;
- **F4** a central statement that is neither equivalent to RH nor a ruler of the width;
- **F5** a question that is not on the table of an existing programme.

**The gaps and their owners.**

| Gap | Owning programmes | Object the owners lack | Criterion a separate field fails |
|---|---|---|---|
| Signed estimate before Cauchy–Schwarz (O1, O2) | metaplectic descent, family continuation, reciprocity families | the order-six Kubota series, uniform in the column | F5 |
| Estimates on the tower (O3) | family continuation, exponent dynamics | a Hecke family with infinity type inside the probe | F5 |
| Joint completion at period ≥ 7 (O4) | exponent dynamics, tensor-power programme | a completion that is not a product of pairings | F5 |
| Pole law with a source (O5) | tensor-power programme, Künneth theory, infinite-rank purity | a base with monodromy and ζ as a fibre | F5, F4 (a pencil exists iff RH) |
| Sign at every aperture (O8–O10) | window tower, absolute geometry, Green calculus, floor-tree mixing, Castelnuovo–Severi, counting holography | a count, a section or a height | F5, F4 |
| Finite layer and landing (O12, O13) | floor-free arithmetic, auxiliary dynamics, exceptional layers, worlds, Euler–FE transport, positive duality | one statement using functional equation and Euler product together | F5 |
| Clusters of the heat flow (O14) | zero-configuration geometry, Galois theory of zeros | precision at the Gaussian saddle | F5 |

**Verdict.** No candidate passes F5: every open obstacle of §2.2 is the stated open question of a programme. The corpus does not lack a field; it lacks three objects inside existing questions. The first of them is the largest unbuilt body of mathematics on the estimate route and is written out as a programme.

**Unbuilt programme: order-six metaplectic theory over ℚ(ω).**

| | |
|---|---|
| About | The Dirichlet series of the row root numbers Φ(u) = G(u)γ₂(u)² over ℤ[ω], twisted by the column: continuation, functional equation, residue and a remainder, uniformly in the column. The root number is a sextic Gauss sum ([`rowGauss_product`](../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/TheRowRootNumberCarriesTheMoebiusSign.lean#L118)) and is the phase that a Cauchy–Schwarz sieve discards. |
| Criteria | Success: main term plus remainder O(U^(1/2+ε)) uniform in the column; the floor-bin curve reaches 2/3 (*table*). Kill: a main term of order U^(2/3) that no reweighting of rows removes; 5/6 is then the wall of the probe at order six, and the survivor is the main term in closed form. |
| Questions | (1) The functional equation with explicit dependence on the column. (2) The residue: coefficients of the order-six theta function at the frequencies of the reflected Gram, which has rank one at sixth powers ([`gramCoeff_sixthPower`](../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/TheReflectedGramIsTwistedByTheRowRootNumbers.lean#L216)). (3) A large sieve for the sextic symbol with cross term below (MN)^(2/3). (4) The same statements along the tower k ↦ 6k + 1 (O3). |
| Tools | In the corpus: the cubic Eisenstein series, its residue and the cubic theta coefficients (metaplectic descent), the cubic large sieve ([`sieveNorm_sharp`](../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/CubicSieve/HeathBrownIteration.lean#L1221)), the reflected Gram. Not in the corpus: the six-fold cover, its Eisenstein series, a sextic large sieve (*table*). |
| Objects | Sextic residue symbol on ℤ[ω]; Gauss sums of order six; Φ(u); the Kubota series of order six; its theta function. |
| Language | Rows and columns, bins δ, floor bin, coherence radius, stage ladder (reciprocity families, family continuation). |
| Mechanisms | Reflection by a functional equation in place of Cauchy–Schwarz; the residue as main term; the sign law (the cube of the normalized cubic Gauss sum is the Möbius value times an angular character, [`cubicGauss_normalized_cube`](../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/ThePrimaryCubicGaussSumFixesTheSign.lean#L763)), which holds at odd order only (*table*). |
| Standing | F5 fails: the question belongs to the reciprocity-families programme, which names the object as missing. The classical part is task J6, the open part is O2. |

## 2.10 A field for a proof or a refutation of AAL?

**What a proof has to use.** AAL fails, or its landing companion fails, on five classes of models. Each class keeps a list of properties of ζ and lacks one.

| Class | Keeps | Lacks | Lean |
|---|---|---|---|
| Integer-norm Euler systems | Euler product over natural norms, Dirichlet series, linear partial sums, reflection and conjugation of the configuration; every finite datum of depth below ½ occurs as a top layer | the functional equation of the function | [`EulerSymmetric`](../../../formal/GaloisForLFunctions/FloorFreeArithmetic/TheZeroConfigurationDoesNotSeeTheEulerProduct.lean#L64), [`eulerSymmetric_layerConfig`](../../../formal/GaloisForLFunctions/FloorFreeArithmetic/TheZeroConfigurationDoesNotSeeTheEulerProduct.lean#L247) |
| Meromorphic tempered Euler one-off | Euler product over the rational primes, nonnegative Ramanujan-bounded multiplicative coefficients, polynomial vertical bounds, meromorphy on ℂ, exactly one off-line pair right of Θ | holomorphy in the left strip | [`asymptoticAbscissaLaw_or_exists_meromorphic_tempered_euler_oneOff`](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/TheMeromorphicTemperedEulerFirewall.lean#L1687) (a dichotomy: AAL, or Θ < 1 and the models exist) |
| Integer-norm edits of the primes | Hamburger strip class, continuation past ½, a zero at a prescribed point, functional-equation defect of mean square T^ε | the exact functional equation | [`frontier_dichotomy`](../../../formal/GaloisForLFunctions/WorldsOfTheZeroConfiguration/FakeEditsWithSubpolynomialDefectEnergy.lean#L699) |
| Positive-weighted Beurling systems | positive weights, count Ax + O(x^(4/5)), off-line zeros, defect below any prescribed Φ(t) → ∞ | a bounded defect | [`exists_positiveWeighted_beurling_slow_defect`](../../../formal/GaloisForLFunctions/EulerFETransportTheory/ArbitrarilySlowDefectsOfPositiveWeightedSystems.lean#L569) |
| Approaching remainders (landing) | functional equation, reality, order one | Euler product | [`approachingModel_eq_zero_iff`](../../../formal/GaloisForLFunctions/InfiniteRankWeilTheory/TheFunctionalEquationAdmitsApproachingRemainders.lean#L312) |

On the other side a decaying defect O(t^(−1/2+ε)) forces the rational primes ([`beurlingSystem_rigidity_of_decaying_defect`](../../../formal/GaloisForLFunctions/EulerFETransportTheory/DecayingFunctionalEquationsDetermineThePrimes.lean#L579)). The class in which exact functional equation and Euler product over the rational primes hold together is ζ alone. A proof of AAL is therefore a statement about one object, and criterion F2 for a field of AAL is fivefold: its first theorem has to be false on each class above.

**What a refutation would exhibit.** The failure of AAL is a line with a finite positive number of zeros to its right ([`not_abscissaLaw_iff_finite_layer`](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/TheFailureOfTheAbscissaLawIsAFiniteLayer.lean#L33)). The proved consequences:

- the prime trace attains the level c·e^(bu) on every late window of every length ([`psi_attained_on_every_window_of_not_asymptoticAbscissaLaw`](../../../formal/GaloisForLFunctions/FloorFreeArithmetic/ThePrimeNumberTheoremIsNotAttainedOnWindows.lean#L68)), and the normalized trace approaches a nonzero real trigonometric polynomial ([`zetaNormTrace_quadrichotomy`](../../../formal/GaloisForLFunctions/FloorFreeArithmetic/TheSplineTraceClassificationAtTheZeroAbscissa.lean#L437));
- the layer can be removed by a two-sided edit of the primes with count Ax + O(x^β) ([`exists_isEdit_layer_removed`](../../../formal/GaloisForLFunctions/WorldsOfTheZeroConfiguration/AFiniteLayerCanBeEditedAway.lean#L48)), so no count at a power rate sees it;
- at a pure off-line quartet height the square of the reflection product lies in the prime-trace field and is positive at every prime, whereas at a critical height it is negative at some prime ([`isolated_quartet_radicand_square_pos`](../../../formal/GaloisForLFunctions/ZeroForcingCalculus/GaloisClosureAndMixedTracesOfAnIsolatedQuartet.lean#L288)).

None of these contradicts a proved statement about ζ.

**Receivers and owners.** The receivers of O12 belong to floor-free arithmetic, auxiliary dynamics, the surface of Spec ℤ and the exceptional-layer theory; the model classes to the worlds programme, positive duality and Euler–FE transport.

**Verdict.** No field passes: F5 fails for every mechanism, and no object is missing. What is missing is one theorem: a consequence of a finite top layer that uses the exact functional equation and the Euler product together and is false for ζ by a proved statement. The search of this review found no such statement and no candidate for it.

## 2.11 A field under the premise that positivity and spectral methods give nothing

**What the premise leaves.** Mechanisms of the corpus that use no sign of a quadratic form and no spectrum:

| Mechanism | Programmes | Reach | Wall |
|---|---|---|---|
| Exact identities: levers, Euler dilation, zero transfer ρ ↦ 6ρ − 3 | zero-forcing calculus, exponent dynamics, family continuation | covering criterion; ζ(ρ/k) ≠ 0 for k ≥ 7; [`grossenLFunction_zero_of_hecke_zero_and_probe_estimates`](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheCubicProbeIsACoupledTowerReachingThreeFifths.lean#L164) | wall 20999/24000 of the seed lever; a lever with centre below 2/3 fails on an Euler world |
| Signed estimates of metaplectic sums | metaplectic descent, family continuation, reciprocity families | the seed | O1, O2 |
| p-adic prices of Gauss monomials | exponent dynamics, tensor-power programme | price exactly k/2 on short signed monomials | the wall ½ of the sign line is attained at no finite period; the completion is missing (O4) |
| Auxiliary polynomials | exponent dynamics (finite fields) | [`cubic_stepanov_count`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheCubicStepanovCount.lean#L188) [S]; [`cubic_stepanov_bound`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheCubicCurveCountWithoutWeil.lean#L96) (src): 3·#{h(x)^N = ε} ≤ s² + (5D+4)s | the modules contain no transfer to an estimate over ℤ[ω] |
| Rigidity in the Hamburger class | Euler–FE transport | a decaying defect forces the rational primes | uniqueness carries no information on zeros |
| Monodromy of the heat family | Galois theory of zeros, zero-configuration geometry | G₊ has index ≤ 2 in the signed permutations of finite support | O16; the arithmetic group is not a heat monodromy on a whole fibre |

The tensor-power argument uses only the positivity of even powers of real traces, which costs nothing; its open input is the pole law (O5).

**Verdict.** Under the premise the route is the estimate route, and the field question reduces to §2.9: the unbuilt object is the order-six theory, and it is owned. No further field passes F5. The auxiliary-polynomial method is the one mechanism of the list without a statement over a number ring; a field built on it fails F3: no receiver of the corpus consumes a vanishing-order count.

## 2.12 A field under the premise that RH is topology or geometry

**The faces and what each proves.**

| Face | Programmes | Theorem | What fixes no value |
|---|---|---|---|
| Index of the windows | absolute geometry, Green calculus, floor-tree mixing | RH ⇔ index one of every neutral window; additive loss law; RH from a level function | the index beyond ratio 10609/5000 [L], three [S] |
| Index by deformation | edge Hodge theory | RH ⇔ the regularized Weil Gram deforms crossing-free at every horizon ([TheIndexComputedByDeformation](../../../formal/GaloisForLFunctions/EdgeHodgeTheory/TheIndexComputedByDeformation.lean) (src)) | the existence of the path |
| Intersection theory | Castelnuovo–Severi | Hodge index ⇔ Riemann–Roch with ampleness; exact source cone = positive cone | a section law |
| Counts | counting holography | Tate limit of a count ⇔ nonnegative form | a count over ℤ |
| Heights | hyperbolic Arakelov theory | RH ⇔ a jump-tail floor at every fixed height ([TheJumpTailFloorNeedsTheFullArithmeticNormalization](../../../formal/GaloisForLFunctions/HyperbolicArakelovTheory/TheJumpTailFloorNeedsTheFullArithmeticNormalization.lean) (src)) | the floor |
| Monodromy | Galois theory of zeros | G₊ of index ≤ 2; conjugation is the word of the turns around the real branch times | the sign of G₊ (O16) |
| The square of Spec ℤ | absolute geometry | the ghost ring is the cofree ring with Frobenius lifts; the Frobenius graphs meet in the primes with length Λ(n) | a normal direction of the diagonal: conormal classes are torsion ([TheNormalDirectionOfTheDiagonal](../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheNormalDirectionOfTheDiagonal.lean)) |

**Reading.** Every topological form in the corpus is an equivalence. A topological theorem that fixes the value of an index needs an invariance under which the index is constant and a point where it is computed. Along the three deformations of the corpus the index is not constant without RH: along the aperture it jumps at the onset of an off-line zero; along the heat time the non-real zeros are finite for t > 0 and the finiteness does not pass to t = 0 ([`heat_finiteness_does_not_pass`](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheLandingLawForZeta.lean#L191)); along the ratio of a window the loss is additive and its sum is the statement. Morse = Maslov identifies two indices and fixes neither (*table*, absolute geometry, construction VII).

**Verdict.** No field passes F5, and each geometric candidate fails F4 as well. The one question of this face with a decidable first step is the level function of §2.8, owned by the Green calculus.

## 2.13 A programme to construct 𝔽₁

The programme exists: the absolute geometry of Spec ℤ. Its sheet, from its question table (*table*) and the Lean statements read:

| | |
|---|---|
| About | A geometry in which Spec ℤ has a product with itself and the Castelnuovo–Severi inequality on it is a theorem. "What is missing is one property of the square that is an inequality: a positive class, a path, a height or a count whose positivity is not the statement to be proved." |
| Objects | Neutral windows (R, R+J] and their index; floor trees of the primes and floor graphs; contacts; the ghost ring 𝒢 = W(ℤ) ([TheArithmeticSquareIsCofree](../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheArithmeticSquareIsCofree.lean)); graph ideals J(m,n) with log #(ℤ/J(1,n)) = Λ(n) ([TheFrobeniusGraphsMeetInThePrimes](../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheFrobeniusGraphsMeetInThePrimes.lean)); the archimedean fibre with weight lines χ_z ([TheArchimedeanFibreOfTheSquare](../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheArchimedeanFibreOfTheSquare.lean)); one ring containing tower, pole plane and jets ([TheTowerThePolePlaneAndTheJetsFormOneRing](../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheTowerThePolePlaneAndTheJetsFormOneRing.lean)). |
| Language | Window, block size, ratio, bound state, binding energy, level, margin, contact, packet, counterterm. |
| Mechanisms | Index = number of right zeros ([TheHodgeIndexOfANumberRingCountsTheZerosOfItsZetaFunction](../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheHodgeIndexOfANumberRingCountsTheZerosOfItsZetaFunction.lean)); zeros as weights of the contacts under scaling ([`contactScale_eq`](../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheZerosAreTheWeightsOfTheContactsUnderScaling.lean#L42)); the sign is carried by the contacts ([TheSignIsCarriedByTheContacts](../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheSignIsCarriedByTheContacts.lean)); Bézout fixes the constant of the counterterm ([BezoutDeterminesTheConstantOfTheCounterterm](../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/BezoutDeterminesTheConstantOfTheCounterterm.lean)); functional equation as transposition F_kV_k = k on a weight line. |
| Tools | Coarse-block decision of step-packet matrices; exact LDLᵀ certificates; gluing through response matrices and Schur complements ([`hermNegIndex_gluedMatrix_schur`](../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TwoCoupledWindowsAreBracketedByLoweredAndRaisedPotentialsAndGluedThroughResponseMatrices.lean#L622)); Brauer induction for Artin Euler products ([EveryArtinEulerProductHasAMeromorphicContinuationAndASignedIndexLaw](../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/EveryArtinEulerProductHasAMeromorphicContinuationAndASignedIndexLaw.lean)). |

**Criteria for a construction.** A candidate square is admitted if (a) it reproduces the certified windows: index one through ratio 103/50 at every block size ([`hermNegIndex_neutralWindow_eq_one`](../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheNeutralPartOfAWindowOfRatioTwoHasOneNegativeSquareAtEveryBlockSize.lean#L315)), gap 1/50000 through ratio 10609/5000 [L]; (b) it is false for the sign twin of the prime 2 ([`exists_firstStep_window_signTwin_lt`](../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheFirstOverlapStepOfWeilsFormFailsForTheSignTwin.lean#L744)); (c) its inequality is a property of the object and not Weil's form restated; (d) it meets the proved obstructions:

| Obstruction | Statement |
|---|---|
| Rank | a coupling model of rank r with 600(r+1) ≤ H has index ≥ 2 at ratio four: the binding rank grows with the block size ([TheBindingOfTheTwoHalvesOfAWindowOfRatioFourHasRankProportionalToTheBlockSize](../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheBindingOfTheTwoHalvesOfAWindowOfRatioFourHasRankProportionalToTheBlockSize.lean)) |
| Convexity | a completion of the couplings with at most one negative square forces diagonal terms of total size ≥ m log m − 2m on one of two separated runs of m blocks: mixed areas of convex bodies are excluded and self-pairings are negative of logarithmic depth ([TheCouplingsOfAWindowAreNotMixedAreasAndTheIndexForcesLogarithmicSelfPairings](../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheCouplingsOfAWindowAreNotMixedAreasAndTheIndexForcesLogarithmicSelfPairings.lean)) |
| Normal direction | conormal classes of the diagonal are torsion; one cotangent line at each prime, none in characteristic zero |
| Counts | every count on the object is linear in the divisor; the pairing needs a quadratic one (*table*, question 2) |

**Questions** (*table*).

| # | Question | Status |
|---|---|---|
| 1 | First selective sign: one bound state of (R, 3R], then (R, 4R], at every block size, from the floor trees of 2 and 3 at their true weights | Ratio three [S]; ratio four: index ≤ 300000 [L] ([`hermNegIndex_blockWindow_ratioFour_le`](../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheStepPacketMatricesOfARatioAreDecidedOnCoarseBlocks.lean#L538)) |
| 2 | A count quadratic in the divisor with the pairing as its Tate limit | Open |
| 3 | Bézout from a property of the object | Equivalent to RH |
| 4 | Realization of the certified windows | Convex bodies excluded; classes of negative self-pairing of logarithmic depth forced; the surface is open |
| 5 | Reciprocity law | Proved; conductor exponent and Gamma factor as invariants are task J4 |
| 6 | Charge of the critical state | Open: whether μ(a) = μ₀(a) occurs |

**Steps and what a failure teaches.**

1. Ratio three as an integrated theorem (J3), then index one at ratio four (J8). A failure at ratio four is a second bound state of an explicit window: a counterexample to RH.
2. A surface for the dyadic windows whose classes have self-pairing −log m + O(1) and whose doubling map realizes the gluing. A failure is a third obstruction of the type of the table and narrows the class of surfaces.
3. A count on that surface (question 2). A failure is the statement that the pairing is not a count on it; by the count door ([`exists_count_tateLimit_iff`](../../../formal/GaloisForLFunctions/CountingHolography/TheCountDoorOfACurveAndOfZ.lean#L39)) a count exists exactly when the form is nonnegative, so the count has to come from the object.
4. The inequality. This step is RH; the programme reaches it only if step 3 delivers an inequality that is not the sign.

## 2.14 A programme to close ACS

**What closing means.** On the scaling surface the Hodge index is equivalent to an effectivity with Riemann–Roch and ampleness ([`exists_effectivity_iff_hodgeIndex`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HodgeIndexFromEffectivity.lean#L102)), and the Hodge defect counts the right zeros ([`zeta_hodgeDefect_iff`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheHodgeDefectCountsTheRightZeros.lean#L556)). Closing ACS is RH. The programme is to construct sections: an arithmetic Riemann–Roch whose effectivity is defined without the sign.

| | |
|---|---|
| Objects | The scaling surface and its divisor classes D_a with the pole class; the positive cone; source cones (exact arithmetic source, Chebyshev majorant); the Frobenius span; calibration curves over finite fields (Kummer, Hermitian). |
| Language | Effectivity, Riemann–Roch axiom, Bézout axiom, ampleness, Hodge defect, blind ideal, source cone. |
| Mechanisms | The positive cone satisfies Riemann–Roch ([`positiveCone_riemannRoch`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/RiemannRochForZAndTheReflectedPrimePolarLedger.lean#L120)); the exact arithmetic source cone is the positive cone ([`exactArithmeticSourceCone_eq_positiveCone`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ExactArithmeticSourceEffectivity.lean#L97)); Hodge index on the span ⇔ unitary ([`hodgeIndexOnSpan_iff_unitary`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/FrobeniusSpanHodgeIndexIsRH.lean#L31)), so in Weil's proof the index theorem comes from the ambient surface and not from the span. |
| Tools | Finite-field calibration: Cartier nilpotence on the Kummer cover [L], Hermitian tangent factor (X−a)^Q(a^(Q²)−X) [L] ([`hermitianTangent_intersection`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/FiniteField/HermitianTangentFactor.lean#L28)), constant-field period [S]. |
| Tests | A candidate effectivity has to fail on the golden datum (integral, positive Euler data, functional equation, not pure: [`goldenDatum_beurling`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheGoldenCurveIsABeurlingSystem.lean#L582)) and on the Chebyshev majorant cone, which has Bézout and ampleness and fails Riemann–Roch ([`arithmeticMajorantSourceCone_not_riemannRoch`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticMajorantsSupplyBezout.lean#L152)). |

**Open questions** (*table*): (1) Riemann–Roch for ℤ on the finitely many low-frequency directions at every degree, by an effectivity not defined through the sign; (2) a section law: a source-defined cone whose Riemann–Roch follows from counting or vanishing; (3) full-source complete-cell positivity; (4) a degree floor below rate ½ from an effectivity input; (5) one fixed test across a wall; (6) a one-prime Lefschetz bound on cycles of width ≤ 3/10, "the whole content" of the Hodge index; (7) the clustering branch of the visibility alternative; (8) positivity beyond the maximal blind ideal; (9) sine moments of the zero-side Gram and the coalescent surplus; (10) a substitute for ℤ[F]: a parallelogram relation among Hecke graphs.

**Steps.**

1. **Calibration by sections (work).** Over a finite field the bound for a cubic curve is proved in the corpus by a section: a nonzero auxiliary polynomial exists because unknowns outnumber conditions, and it vanishes to high order at the points counted ([`cubic_stepanov_count`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheCubicStepanovCount.lean#L188) [S]). This is the model of "Riemann–Roch follows from counting or vanishing" (question 2). Finish it and write it in the language of the effectivity axioms.
2. **The low-frequency directions (question 1).** A finite problem at each degree. A failure is a class of positive self-intersection such that neither it nor its negative is effective. Riemann–Roch on the open positive cone is equivalent to the Hodge index ([`openPositiveCone_riemannRoch_iff_hodgeIndex`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/RiemannRochForZAndTheReflectedPrimePolarLedger.lean#L151)), so such a class witnesses a failure of the Hodge index.
3. **A section law over ℤ (question 2).** Open; the dimension count needs finite-dimensional spaces of sections, which over ℤ are question 10 (a correspondence ring with a theorem of the square).
4. **The one-prime Lefschetz bound (question 6).** Equivalent to the Hodge index on its cycles; it is the last step and is RH on that range.

**Reading.** Steps 1 and 2 are work. Step 3 is the place where the route needs an object that does not exist; it is the same object as question 2 of §2.13.

## 2.15 A programme to close ZCG

Zero-configuration geometry contains no statement about the sign of Weil's form; its route is the heat deformation.

| | |
|---|---|
| About | The contraction supplied by the archimedean factor, carried to ζ along the heat flow H_t. RH ⇔ the local de Bruijn–Newman constant vanishes at every height ([`riemannHypothesis_iff_forall_localNewmanConstant_eq_zero`](../../../formal/GaloisForLFunctions/RHTower/Heat/TheLocalDeBruijnNewmanConstant.lean#L103)). |
| Objects | Heat family; collisions and branch times; local constant Λ_X; forward monodromy group G₊; near-coincidence clusters; abscissa laws. |
| Language | Horizon, collision, cluster, camera, pincer, turn, lasso. |
| Mechanisms | Zeros leave the real axis only through a collision; an off-line zero of depth d at height X gives Λ_X ≥ c·d²/log X ([`exists_le_localNewmanConstant_of_offLine_zero`](../../../formal/GaloisForLFunctions/RHTower/Heat/TheLocalDeBruijnNewmanConstant.lean#L157)); the flow is arithmetic only at time 0 ([`exists_dirichlet_iff`](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/OnlyTheUndeformedKernelHasADirichletSeries.lean#L623)). |
| Tools | Sub-Weyl size bounds ([`riemannHeat_zeros_real_simple_subWeyl`](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/HeatScaleRepulsion/SubWeylCollisionFreeHorizon.lean#L1166)); the global bound Λ ≤ w²/2 ([`newmanConstant_le_half_sq_zetaZeroWidth`](../../../formal/GaloisForLFunctions/SquareRootThreshold/TheWallsMeasureOneZeroWidth.lean#L331)), with the seed Λ ≤ 80982001/1152000000 [L]; the turn calculus of the monodromy. |

**Steps 1–5 (in Lean).** The start is dominated for t ≥ (6600/9991 + ε)/log X; RH ⇔ Λ_X = 0 for all X; exit only through collision; the pincer; the camera fixes the start outside clusters of size X^(−M) (*table*, with the statements above read in source).

**Step 6 (open, O14)** in two forms (*table*): (a) reality inside near-coincidence clusters, the sign of an image Hankel determinant; (b) a Hermite–Biehler half of the heat source dominating its reflection for t ∈ (0, ½/log X], which "is reality of ζ itself".

**What is proved about the step.**

| Statement | Consequence |
|---|---|
| Size domination is impossible below ½/log X (*table*: the Gaussian saddle lies inside the strip; the pair model collides) | the step is a statement of precision, not of size |
| Domination holds for every finite real carrier above its horizon (*table*) | it does not select ζ |
| Cosine models of fixed width have heat time → 0 ([`exists_cosDefect_width_heatTime_lt`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheHeatTimeIsTheWidthTimesTheSpacing.lean#L109)) | the width alone gives no lower bound for the heat time |
| A failure of AAL gives Θ < 1 ([`quasiRH_or_asymptoticAbscissaLaw`](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/QuasiRHIsATailLaw.lean#L27)) | with the seed proved, the dichotomy carries no information on AAL |

**Programme.**

1. Local form of the seed: a bound for Λ_X from the width that improves on the sub-Weyl start. The search of this review found none; the global bound is in Lean.
2. Step 6(a) on clusters of two zeros: the sign of a 2 × 2 image Hankel determinant in terms of the prime sum at the saddle. A failure is an explicit cluster shape that square-root cancellation of the prime sum has to exclude, which is the content of form (b).
3. The sign of G₊ (O16): decidable, and independent of RH.

**Reading.** *Table*: "the residual is a precision problem: square-root-type cancellation of the prime sum inside the strip, at the Gaussian saddle of the heat source". Step 6 is O6 in the coordinates of the heat flow. The programme closes only through family P.

## 2.16 A programme to close RH through the tensor-power programme

Source: the programme README and its Lean modules.

**The argument.** Deligne's proof has four steps: pointwise Frobenius data; positivity of even tensor powers at no cost; a pole law uniform in the power; the limit. Over ℤ the first, second and fourth are in the corpus. The third is the programme.

| | |
|---|---|
| Objects | Euler datum over a base; depth and width; tensor-power moments D_2k; pole law; edge; polarization pair and conjugation pair; flow datum; abelian base; Adams power; pencil through ζ ([`PencilThroughZeta`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/TheAxiomsOfAPencilThroughZeta.lean#L50)). |
| Language | Ruler, lever, wall; frame (c, k), price, half unit; top bound; arithmetic fibre; geometry (a monodromy acting on the zeros of the members). |
| Mechanisms | Positivity of even powers and Rankin domination; the ruler law 2kW ≤ a_k ≤ 2kW + a₀; two pairings at the edge (purity is the coincidence of conjugation pair and polarization pair); frames as tensor powers with a price; coinvariants are everything on a flow datum; the top bound one is temperedness. |
| Tools | Frame and tower calculus; Stickelberger prices; the prime-trace receiver; amortization over families; SL₂ invariants and the golden countermodel; the heat monodromy; the cubic probe with its correction and rungs. |

**The three lines of frames** ([TheThreeLinesOfFrames](../../../formal/GaloisForLFunctions/TensorPowerProgramme/TheThreeLinesOfFrames.lean) [L]).

| Line | Price at period k | One step from the top bound 1 | Tower centre |
|---|---|---|---|
| Deligne | (k−1)/2 | ½ + 1/(2k) | ½ |
| Sign | k/2 | ½ + 1/k | k/(2(k−1)) |
| Completion | 2k/3 − 1 | 2/3 | 2/3 − 1/(3(k−1)) |

The completion line meets the sign line at k = 6, the frame (3, 6) of the cubic probe and the wall 3/5.

**Questions.**

| # | Question | Status |
|---|---|---|
| Q1 | Calibration: the inputs of the pole law | The pole law is the continuation of the constituents; positivity turns it into convergence ([`norm_eq_one_of_adamsPoleLaw`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/APolarizedBaseWhoseAdamsSquaresContinueIsPure.lean#L93)). The calibration curves are pure by an identity of the two pairings, ‖J(χ,φ)‖² = q, and their Gauss triples cost k/2 ([`norm_jacobiSum_sq`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/TheCalibrationCurvesArePureByTheirPairing.lean#L47), [`stickelbergerPrice_jacobiTriple`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/TheCalibrationCurvesArePureByTheirPairing.lean#L56) [S]): purity does not remove the sign cost. Monodromy enters only for families without complex multiplication, where the trace formula supplies the constituents (README) |
| Q2 | Price ledger | Proved [L] |
| Q3 | Diagnosis over Spec ℤ | Finite configurations: base loss exactly one, pole law ⇔ width ([`exists_poleLaw_iff`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/TheTensorMomentsOfAFlowDatumHaveBaseLossExactlyOne.lean#L510) [L]). ζ itself: 2kw ≤ a_k ≤ 1 + 2kw and the pole law at weight w₀ holds iff w ≤ w₀ ([`exists_momentPoleLaw_iff`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/ThePrimeTraceMomentsOfZetaReadTheWidthWithBaseLossAtMostOne.lean#L223) (src)) |
| Q4 | A pencil | Heat: arithmetic only at time 0. Twists and Kummer families: abelian, rulers ([`exists_twistPoleLaw_iff`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/AnAbelianBaseIsARuler.lean#L568)). The axiom list is RH ([`riemannHypothesis_iff_nonempty_pencil`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/TheAxiomsOfAPencilThroughZeta.lean#L188)) |
| Q5 | A sign-line completion at period k ≥ 7 | Open (O4) |
| Q6 | Exact transport: continuation of the probe to the centre of (3, 6) by identities | Open; the dual series of the probe is not written (J5) |
| Q7 | Uniformity | The top bound one for all Adams powers is temperedness ([`adamsPoleLaw_iff`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/TemperedIsTheUniformTopBound.lean#L87) [L]). Open: conductor growth of order-k completions |
| Q8 | Assembly | Proved for levers ([`riemannHypothesis_of_deligneLever`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/TheThreeLinesOfFrames.lean#L84), [`riemannHypothesis_of_signLevers`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/TheThreeLinesOfFrames.lean#L94) [L]) |
| Q9 | Refutation: finite monodromy of every Euler–FE family through ζ; an intrinsic floor of every transport | Pencils exist iff RH, so no theorem about the existence of pencils refutes the route; a refutation has to concern the sources of the pole law (README). In the abelian class the source is the conclusion; Euler–FE deformations in the Hamburger class are rigid. Open: sources beyond abelian ones, intrinsic floors of transports |

**The three missing objects** (README): **N1** a pencil with a pole law whose source does not know the parameters; **N2** a joint completion on the sign line at period ≥ 7; **N3** an exact transport without estimate floor, uniform in the period.

**Programme to close.**

| Stage | Statement | Kind | A failure proves |
|---|---|---|---|
| 1 | Tools J5: Hecke characters with infinity type as an abelian base; the dual series of the probe; the price of the A₂ coefficients | work | — |
| 2 | N2 at k = 7: one valid sign lever of period 7 gives Θ ≤ 7/12 | open (O4) | a cost theorem: completion costs more than k/2 at period 7, and the wall 3/5 is the wall of the Gauss family and not only of the completion class |
| 3 | N2 at all large k, with constants uniform in k (Q7) | open | conductor growth of order-k completions: an intrinsic floor above ½ (Q9) |
| 4 | N1: a base with nonabelian monodromy, ζ as a fibre at a prime point, constituents that are L-functions of other objects | open (O5) | finite or abelian monodromy on the zeros for every Euler–FE family through ζ (Q9); with rigidity ([`beurlingSystem_rigidity_of_decaying_defect`](../../../formal/GaloisForLFunctions/EulerFETransportTheory/DecayingFunctionalEquationsDetermineThePrimes.lean#L579)) this is the statement that ζ lies in no family |
| 5 | Assembly by Q8 | proved | — |

**Reading.** Stage 4 alone suffices and stage 3 alone suffices. Stage 2 is the first place where the programme can produce an exponent, and it presupposes estimates down to 7/12, which are O1–O3. Without those the tensor-power programme is a classification of what a proof has to supply; with them it is the last two steps of the estimate route (O4, O5). The pole law for ζ is a ruler at every weight, so no argument that produces the pole law from the moments of ζ alone can succeed: the source has to be a second object.

## 2.17 The one question

**Question.** Do the estimates of the cubic probe hold on the Grössencharacter tower k₀ = 0, k_(r+1) = 6k_r + 1 of ℚ(ω), at the exponent proved for finite-order characters? The outcome asked for is that L(w, ψ₆^k ψ) is zero-free on Re w > 20999/24000 for every rung k of the tower and every finite-order ψ.

**Why this question.**

- **It is the seed on the family on which the probe is a self-map.** A zero ρ of a finite-order Hecke L-function with probe estimates below Re ρ forces a zero of the rung at 6ρ − 3 ([`grossenLFunction_zero_of_hecke_zero_and_probe_estimates`](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheCubicProbeIsACoupledTowerReachingThreeFifths.lean#L164)); feeding rung coefficients into the probe gives a correction that vanishes iff the rung of level 6k + 1 vanishes (module header, item 4). The threshold map θ ↦ (3 + θ)/6 contracts to 3/5 from the trivial bound 1, so on the tower the half-plane is max(estimate floor, 3/5): the estimate is the only input.
- **Consequence (T3).** The correction of the probe has abscissa (3 + Θ_rung)/6 exactly ([`correctionAbscissa_eq`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheCorrectionOfTheCubicProbeCarriesTheAbscissaOfItsRung.lean#L126)). With Θ_rung ≤ 20999/24000 the completion wall drops from 2/3 to 92999/144000, and the steps 5/6, 7/9, 2/3 of the signed evaluation (O2) have a target below 2/3.
- **It is outside the reach of identities.** No rung is a product or quotient of finite-order Hecke L-functions ([`not_grossenLFunction_mul_prod_eq`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheRungsLieOutsideTheSeededFamily.lean#L420) [L]); the Euler factor of a rung is a power of the normalized cubic Gauss sum ([`grossenPrimeTerm_eq_conj_normalizedCubicGauss`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheRungsAreTensorPowersOfTheCubicGaussSums.lean#L48) [L]); the seeded family type has no infinity type (J7).

**Tests.**

| Test | Result |
|---|---|
| T1 | Passes. The statement is a zero-free half-plane at 20999/24000 for a family; it does not imply RH or AAL, and it does not move Θ of ζ by itself |
| T2 | Passes |
| T3 | Passes: [`correctionAbscissa_le_iff`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheCorrectionOfTheCubicProbeCarriesTheAbscissaOfItsRung.lean#L147), the coupled tower |
| T4 | Passes: a statement for all heights and all rungs |
| T5 | Untested: the corpus has no model of a rung. The known facts about the true rungs are nonvanishing on Re w ≥ 1 and infinitely many zeros in ½ ≤ Re w < 1 |
| T6 | Passes |
| T7 | Passes: the search of this review found no zero-free half-plane left of 1 for an L-function of nonzero infinity type |

**Why it is less hard than the alternatives.** It asks for an exponent that is proved, on a family the proof does not cover. The questions of §2.4–2.6 ask for exponents that no method has reached. The questions of families R and U (O8–O13) have no producer and are equivalent to RH or to AAL in every form the corpus has tested.

**Risk.** The proof of the seed runs through rows of finite-order characters and a compensation stated for the finite-order family ([`compensationSubsetCoefficient`](../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/PhysicalRows.lean#L648)). The theta-to-Gauss conversion is stated for an arbitrary multiplicative twist ([`fixedThetaTwist`](../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Eisenstein/CuspAveragesAndBesselMellin.lean#L417)). Whether the row count and the budget survive an angular twist is not decided by any statement of the corpus; a failure would be a wall theorem locating the infinity type in the budget.

## 2.18 The most likely route to a proof, as a research programme

**The guess.** RH is proved by excluding one function. Weil's form on the half-line u < 0, confined by the weight e^(−8u), has a critical state exactly when RH fails ([HF](../rh-current-frontier-map.md#hf)); the state is unique up to sign and solves one linear equation. The route writes that equation in the coordinates of the zeros, adds exact properties of the state stage by stage, and ends when the properties contradict the arithmetic of ζ. Every stage is a reduction "no function with the properties P₁, …, P_k exists ⇒ RH", and the premise weakens from stage to stage. The parts of the route that are in Lean are its base.

**Why this route.** *Reading.*

| Route | In Lean | Where it stops | Open statements before RH |
|---|---|---|---|
| Estimates (family P) | seed 20999/24000, levers, walls | 3/5 for every factor-by-factor completion ([`sInf_coupledBarrier_eq_three_fifths`](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/MoebiusSignedGaussPairingsEndAtThreeFifths.lean#L859)); ½ at no finite period ([`exists_towerValue_signLine_lt`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheShortMoebiusMonomialsPayExactlyHalf.lean#L157)) | O1–O5; O4 and O5 concern objects that do not exist |
| Tensor powers (§2.16) | rulers, pencils, lines of frames | a wall above ½ for ζ is the failure of RH ([`half_lt_wall_validLevers_zeta_iff`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/AWallAboveOneHalfIsAWorldOffTheLine.lean#L224) (src)) | those of the estimate route; no producer of its own |
| Exclusion of the critical state (this section) | dichotomy, weak equation, uniqueness, zero-free transform, decay, phase structure | the state is not excluded | one: stage 5 |

At the state every relation is an identity, so no exponent is lost between stages. One statement is open, and it concerns a single function that the corpus has made explicit.

**The object.** Tests are real functions F supported on u < 0; ℒF(w) = ∫ F(u)·e^(wu) du; z = ρ − ½ runs over the nontrivial zeros with multiplicity. The bare form is Weil's form, bare(F) = archimedean part − prime part + 2·ℒF(½)·ℒF(−½). The full form at ratio R is bare(F) + a(R)·W₈(F), with W₈(F) = ∫ F²e^(−8u) and a(R) = a(1)/R > 0 ([`criticalHalfLineFullEnergy_eq_bare_add_confinement`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ArithmeticHawkingPagePhaseStructure.lean#L50)); λ(R) is its infimum over tests of unit norm. The threshold W₀ = inf_A windowThreshold(A) is the infimum of c·W₈(H)/(−bare(H)) over window tests of negative form ([`windowThreshold`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalThresholdOfAWindow.lean#L52)): a(W₀) is the sharp constant in bare ≥ −C·W₈ (*reading* of the definition).

| Property | Lean statement | Grade |
|---|---|---|
| RH ⇔ windowThreshold(A) = ⊤ for every A. RH, or W₀ is finite and a state F of unit norm exists at ratio W₀ | [`riemannHypothesis_iff_windowThreshold_eq_top`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalThresholdOfAWindow.lean#L88), [`riemannHypothesis_or_exists_criticalHalfLineGroundState`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/HalfLinePolarThresholdAndGroundStateOrthogonality.lean#L339) | [L] |
| The state has full form zero, and its full mixed form with every test of the domain vanishes (weak equation) | [`criticalHalfLineMixedEnergy_groundState_eq_zero`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalHalfLineStateSatisfiesTheWeakEquation.lean#L136), [`riemannHypothesis_or_exists_weak_criticalHalfLineGroundState`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalHalfLineStateSatisfiesTheWeakEquation.lean#L170) | (src) |
| The state is unique up to sign | [`criticalHalfLineGroundState_unique_up_to_sign`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalHalfLineStateIsUniqueUpToSign.lean#L67) | (src); for the minimizer at every R [L] |
| ℒF(w) ≠ 0 on Re w ≥ 0 | [`criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineStateHasNoBoundaryLaplaceZero.lean#L126) | (src); at every R [S] |
| \|F(u)\| ≤ C·e^(βu) for ½ < β < 15/2, and ∫ F²e^(−bu) < ∞ for b < 15 | [`criticalHalfLineGroundState_exponential_bounds`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ConfiningMinimizerExponentialBarriers.lean#L243) | [L] |
| F has positive mass on every interval (−d, 0) | [`criticalHalfLineGroundState_endpoint_mass_pos`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineStateHasNoTerminalSupportGap.lean#L194) | (src) |
| The full mixed form of two translates F(· + s), F(· + t), s, t ≥ 0, is a·(1 − e^(−8·min(s,t))) times their pairing in L²(e^(−8u)) | [`criticalHalfLineMixedEnergy_ground_translates`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/CriticalCausalEnergyKernel.lean#L93) | (src) |
| λ(1/t) is strictly concave | [`confiningHalfLineGroundEnergy_strict_jensen`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ConfiningHalfLineGroundEnergyCurvature.lean#L45) | [L] |
| RH ⇔ λ(R) ≥ 0 for every R ⇔ bare ≥ 0 on the domain. Off RH: λ > 0 below W₀, λ(W₀) = 0, λ < 0 above W₀ | [`riemannHypothesis_thermodynamic_equivalences`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ArithmeticHawkingPagePhaseStructure.lean#L352), [`offLine_arithmetic_hawking_page_transition`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ArithmeticHawkingPagePhaseStructure.lean#L440) | [S] |
| W₀ ≥ c·e^(6A) for every A up to the onset aperture of ζ | [`exp_six_mul_le_poleOrthogonalCriticalThreshold`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/PrimitiveCriticalThresholdEqualsWindowThreshold.lean#L222) | (src) |

**What does not exclude the state.**

- Stability, outerness and cyclicity of ℒF, the transverse gap and the endpoint competition: all hold in the phase off RH ([ledger](../rh-killed-routes.md#confining-stability-exclusion) [S]).
- Holomorphic multipliers: none dominates the polar term uniformly ([ledger](../rh-killed-routes.md#universal-holomorphic-polar-multiplier)).
- A state of one sign. The prime part favours one sign and the pole part penalizes it; past the plastic threshold the even sector is frustrated in every sign gauge ([`even_frustrated_in_every_sign_gauge`](../../../formal/GaloisForLFunctions/FrustratedArithmeticDirichletForms/FrustrationCannotBeSwitchedAway.lean#L209) (src)), and the criticality programme records that no positive supersolution exists (*table*). Stage 3 states the same for the state itself.
- The functional equation, an Euler product and positive coefficients together: the positive twins of O11 have all three and a zero off the line; the prime-two deformations have the first two. The separator of the corpus is the nonnegative Euler logarithm (O11 [K]).

**The step: the state in the coordinates of the zeros.** *Reading*; not a Lean statement, and the corpus search returns no statement of this shape. The exponentials e_p(u) = e^(pu) on u < 0 lie in the domain ([`CriticalHalfLineEnergyDomain`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalHalfLineFormHasItsActualDomain.lean#L23)) for p > 4. With the zero side of the form, bare(F, G) = Σ_z ℒF(z)·ℒG(−z), the weak equation tested on e_p reads

> (★)  a·ℒF(w) = −Σ_z ℒF(z)/(w + 8 − z),  Re w > −4,  a = a(W₀).

- **(a) Continuation.** ℒF is meromorphic on ℂ. Its poles are the points z − 8, with residue −ℒF(z)/a, nonzero at every zero with Re z ≥ 0. The product ξ(w + 17/2)·ℒF(w) is entire.
- **(b) A sum over the zeros.** F(u) = −a⁻¹·e^(8u)·Σ_z ℒF(z)·e^(−zu) on u < 0, as distributions. On u > 0 the same series is the prime side seen from beyond the wall: the archimedean part of F, minus Σ_{n > e^u} Λ(n)·n^(−½)·F(u − log n), plus the pole terms. The main term of the prime sum cancels the pole term ℒF(−½)·e^(u/2); what remains is the remainder of the prime number theorem averaged by F.
- **(c) Decay law.** ∫ F²e^(−bu) diverges for b > 17 − 2Θ, because a zero with Re z > 0 gives a pole of ℒF on Re w = Re z − 8. Convergence for every b < 17 − 2Θ needs a bound for the series (★) on vertical lines. Lean has b < 15, the value at Θ = 1; with the seed the target is b < 183001/12000. The decay exponent of the state is a ruler for Θ.
- **(d) Sign law.** F has one sign on no ray (−∞, −T). By Landau's theorem the transform of a function of one sign is singular at the real point of its abscissa; the poles z − 8 are not real, because ζ has no zero on (0, 1) ([`riemannZeta_ne_zero_of_ofReal_mem_Ioo`](../../../formal/GaloisForLFunctions/RHTower/FractionalPartZeta.lean#L430) (src)).
- **(e) Eigenvector.** The vector c = (ℒF(z))_z satisfies (a + K)c = 0 for the Cauchy matrix K(z′, z) = 1/(8 + z′ − z) of the zeros. For the pairing β(c, d) = Σ_z c_z·d_(−z) one has β(c, Kc) = W₈ ≥ 0 and β(Kc, Kc) = bare. So K is symmetric and nonnegative for an indefinite pairing whose negative squares are the zeros right of the line ([`pontryagin_law`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheHodgeDefectCountsTheRightZeros.lean#L490) (src)). With every zero on the line, β is a sum of squares and a + K has no null vector. For a finite configuration, symmetric under z ↦ −z and z ↦ z̄, with κ points right of the line, K has exactly κ negative eigenvalues: the confined form has κ critical ratios, and W₀ is the smallest.
- **(f) Kernel.** On exponentials the full form is (D(p) + D(q))/(p + q) + a/(p + q − 8), with D(p) = ξ′/ξ(½ + p) = Σ_z (1/(p − z) + 1/z) ([`logDeriv_xi_eq_partialFraction`](../../../formal/GaloisForLFunctions/RHTower/XiExplicitFormulaLogDeriv.lean#L54) (src)). The first term is the kernel of the criterion Re ξ′/ξ ≥ 0 on Re s > ½, which is RH ([`riemannHypothesis_iff_re_logDeriv_xi_nonneg`](../../../formal/GaloisForLFunctions/RHTower/XiLogDerivReCriterion.lean#L75), [`twoChannelKernel_eq_eulerKernel`](../../../formal/GaloisForLFunctions/RHTower/XiWeilTwoChannelResolvent.lean#L665) (src)). The Euler product enters through D(p) = 1/(p − ½) + 1/(p + ½) + Γ-term − Σ Λ(n)·n^(−½−p).

**Stages.**

| Stage | Statement | Kind | Lean start or consumer | Arithmetic used |
|---|---|---|---|---|
| 0 | The properties of the table above | proved | — | — |
| 1 | The kernel (f) on exponentials; the zero side of the bare form on the domain | work, classical type | start: [`logDeriv_xi_eq_partialFraction`](../../../formal/GaloisForLFunctions/RHTower/XiExplicitFormulaLogDeriv.lean#L54), [`twoChannelKernel_eq_eulerKernel`](../../../formal/GaloisForLFunctions/RHTower/XiWeilTwoChannelResolvent.lean#L665) | none: holds for every tempered symmetric configuration |
| 2 | (★) with (a) and (b) | work | consumer: [`riemannHypothesis_or_exists_weak_criticalHalfLineGroundState`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalHalfLineStateSatisfiesTheWeakEquation.lean#L170) | none |
| 3 | Decay law (c) and sign law (d) | work; the convergent half of (c) needs a bound on vertical lines | start: [`abscissa_landau_eq`](../../../formal/GaloisForLFunctions/RHTower/FiniteOffLineLandau.lean#L449), [`criticalHalfLineGroundState_exponential_bounds`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ConfiningMinimizerExponentialBarriers.lean#L243), the seed ([`riemannZeta_ne_zero_of_sub_seven_eighths_lt_re`](../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/SubSevenEighthsZeroFreeHalfPlane.lean#L147) [L]) | none |
| 4 | Index law (e): exactly κ critical ratios for a finite configuration; for ζ, a finite index of the confined form at every ratio | finite case: work; ζ: open | consumer: [`pontryagin_law`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheHodgeDefectCountsTheRightZeros.lean#L490) | none |
| 5 | Rigidity: for the zeros of ζ and every a > 0, (★) has no solution F ≠ 0 in the domain | open; no mechanism in the corpus | consumer: [`riemannHypothesis_or_exists_criticalHalfLineGroundState`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/HalfLinePolarThresholdAndGroundStateOrthogonality.lean#L339) | required |

**Where mathematics is missing.** Stage 5, and only there. Given stages 1 and 2 it is RH; it fails T1 and is reported with that failure. Three facts fix its shape.

- *It is not a statement about zeros alone.* Stages 1–4 hold for every tempered configuration with the symmetries of the zeros. The prime-two deformations have a finite onset aperture ([`onsetAperture_xiDeformedZeroConfig_lt_top`](../../../formal/GaloisForLFunctions/BlackHoleRingdown/PrimeTwoDeformedApertureLogTwoTest.lean#L196) [S]), so a proof of stage 5 has to use a property they lack. The corpus has one: the coefficients of the Euler logarithm of ζ are nonnegative (O11).
- *The primes are visible on one side only.* They do not occur in (★). They occur in the rows of the weak equation ([`IsHalfLineEnergyMinimizer.weakEquation_rows`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ConfiningMinimizerExponentialBarriers.lean#L36) (src)) and in (b): one series Σ_z ℒF(z)·e^(−zu) equals −a·e^(−8u)·F(u) left of the wall and an average of the remainder of the prime number theorem right of it. A proof of stage 5 shows that these two descriptions of one series are incompatible.
- *The soft properties are spent.* Every item of the list "what does not exclude the state" is a theorem or a ledger entry.

Entry points, none established: (i) the wall, the behaviour of F at u → 0⁻ against the series at u → 0⁺ (the frontier lists the collar-energy transfer as open); (ii) the collar −log 2 < u < 0, where no forward prime translate enters the equation; (iii) the charges ℒF(±½): the classification [`polarPaymentCriticalThreshold_windowThreshold_classification`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/HalfLinePolarThresholdAndGroundStateOrthogonality.lean#L786) (src) leaves the case of equal thresholds with every state orthogonal to the polar source; (iv) the difference equation: by (★), a·ℒF(w − 8) + ξ′/ξ(½ + w)·ℒF(w) has no pole at the zeros.

**Failures and what they prove.**

| Stage that fails | Theorem that results | What it teaches |
|---|---|---|
| 1 | The zero side diverges on a test of the domain | (★) holds on exponentials only; the route continues with the kernel (f) in place of the domain |
| 3 | The state decays more slowly than 17/2 − Θ | The decay reads the growth of the series (★) on vertical lines, a statement on the local count of zeros off the line, and not the width alone |
| 4 | The confined form has infinitely many negative directions at one finite ratio | Critical ratios of infinitely many zeros off the line accumulate; a statement of the type of AAL (O12) |
| 5 | A state exists: RH is false, with W₀ and the decay exponent as invariants of the failure. Or: the properties of stages 0–4 are realized together on a configuration of O11 | The missing property is arithmetic and lies outside the list of stages 0–4 |

**Order of work.** Stage 1 on exponentials first: it is a finite list of identities with Lean starts. Then (★) for the state, the sign law, the decay law; the finite index law in parallel. Stage 5 through the wall (i), with (b) as the working identity.

**What the other families contribute to this route.** Family P: the seed moves the target of the decay law from 15 to 183001/12000, and every exponent of O1–O3 moves it further; a width σ is a floor of the form at rate 2σ in the aperture ([`exists_fullZeroForm_ge_neg_of_zetaZeroWidth_le_pos`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/AllParityCriticalDeficitAndEndpointSobolevLaws.lean#L604) (src)), and every weight exponent p > 1 pays every window ([`weilQuad_ge_neg_exponentialMass`](../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheAliasingWeightPaysEveryWindow.lean#L260) (src)), so the exponent 8 is a choice of the corpus. Family R: positivity at a fixed aperture is a lower bound for W₀ ([`exp_six_mul_le_poleOrthogonalCriticalThreshold`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/PrimitiveCriticalThresholdEqualsWindowThreshold.lean#L222)) and never W₀ = ∞ (O8). Family U: as u → −∞ the series (b) is carried by the zeros nearest Re s = Θ; whether Θ is attained, the subject of AAL, is the difference between an almost periodic leading term and none (*reading*).

**Tests.** Stages 1–4: T1, T2, T3, T4 and T7 pass; T5 fails for each, because the statements hold on every configuration, so they are work and not obstacles; T6 fails for the convergent half of (c), whose bound on vertical lines is not a Lean statement. Stage 5: T2, T3, T4, T5 and T7 pass; T1 fails (given stages 1 and 2 it is RH); T6 fails (no input is named). No stage that passes every test implies RH. The route reduces RH to one equation for one function and makes the properties of that function theorems; its last step is a guess at where the missing mathematics sits, not a known argument.

## 3. Picks

| Purpose | Question | Section |
|---|---|---|
| The one question | Probe estimates on the Grössencharacter tower | 2.17 |
| Moves the abscissa of ζ | Row count in the binding bins | 2.4 |
| Positivity producer | A doubling factor below √2 from the window matrices | 2.5 |
| Without positivity | First moment of the row root numbers on long columns | 2.6 |
| Physical face | Level-uniform ringdown on congruence horizons | 2.7 |
| Geometric face | Summability of the conditional couplings along the dyadic recursion | 2.8 |
| A further field | None passes; unbuilt object: the order-six metaplectic theory | 2.9–2.12 |
