# Review 1511 — routes and their hard obstacles

Corpus: commit a7fcf5212f with the working tree (15 November 2026). Inputs: the frontier map and the killed-routes ledger, the corpus search tool, and the Lean statements cited below, each read in source. O11 additions were individually checked with `lake --old env lean`; no umbrella build or axiom audit was run for those additions.

Grades are the frontier map's: **[L]** integrated, **[S]** source only (unfinished or unintegrated), **[K]** individually audited. A fact marked **(src)** was read in the Lean source and has no grade of its own on the frontier map. A statement marked *table* comes from a programme table returned by the search tool and is not a Lean statement.

Companion reports: [obstacles summary](obstacles-summary.md) (tasks J1–J11, open problems O1–O16, questions and programmes), [walls ledger](walls-ledger.md) (P, R, U walls), [route unification ledger](route-unification-ledger.md).

## 1. Status

RH is open. The frontier map lists 38 live route formulations and 12 candidates. Every live route has a proved receiver (a statement that implies RH) and an open source estimate.

What is proved without hypothesis:

- **A zero-free half-plane.** ζ, every Dirichlet L-function and every finite-order Hecke L-function of ℚ(ω) have no zero on Re s > 20999/24000 [L] ([`riemannZeta_ne_zero_of_sub_seven_eighths_lt_re`](../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/SubSevenEighthsZeroFreeHalfPlane.lean#L147), [`hecke_ne_zero_of_sub_seven_eighths_lt_re`](../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/SubSevenEighthsZeroFreeHalfPlane.lean#L111), [`hecke_beta_le_sub_seven_eighths`](../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/SubSevenEighthsZeroFreeHalfPlane.lean#L34)). Width: w = sup |Re ρ − ½| ≤ 8999/24000 ([`zetaZeroWidth_le_sub_three_eighths`](../../../formal/GaloisForLFunctions/ZeroForcingCalculus/EulerDilationAndRootCoincidenceExclusion.lean#L60)).
- **A calculus that carries this bound everywhere.** Every width ruler of the corpus reads the same number ([`sub_three_eighths_ruler_jump`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheAbscissaAvoidsAnIntervalBelowSevenEighths.lean#L186) [L]); a family of levers that covers (½, 20999/24000] gives RH ([`riemannHypothesis_of_covering_levers_sub_seven_eighths`](../../../formal/GaloisForLFunctions/ZeroForcingCalculus/EulerDilationAndRootCoincidenceExclusion.lean#L438) [L]).
- **The sign of Weil's form on small windows.** Floor 1/50000 at aperture 1881/5000 [L]; floor 10⁻¹³ at aperture log 2 [S] ([`weilFloor_apertureLogTwo`](../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheTwoPrimeWindowHasAPositiveWeilFloorAtEveryBlockSize.lean#L48)); index one of the neutral window through ratio 103/50 ([`hermNegIndex_neutralWindow_eq_one`](../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheNeutralPartOfAWindowOfRatioTwoHasOneNegativeSquareAtEveryBlockSize.lean#L315)), with gap 1/50000 through ratio 10609/5000 [L], and through ratio three [S].
- **Exact dictionaries.** The number of negative squares of Weil's form equals the number of zeros right of the line ([`pontryagin_law`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheHodgeDefectCountsTheRightZeros.lean#L490)); RH ⇔ zeros approach the line (ZAL) ∧ the asymptotic abscissa law (AAL) ([`riemannHypothesis_tfae`](../../../formal/GaloisForLFunctions/InfiniteRankWeilTheory/TheInfiniteRankWeilProof.lean#L64)); failure of AAL ⇔ a finite nonempty set of zeros beyond some depth ([TheFailureOfTheAbscissaLawIsAFiniteLayer](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/TheFailureOfTheAbscissaLawIsAFiniteLayer.lean)).

What no route has: a mechanism that lowers the exponent below the vertex of the cubic probe, a mechanism that produces the sign of Weil's form at a growing aperture, and a mechanism that excludes a finite top layer of zeros. These are the three core families of the [walls ledger](walls-ledger.md).

## 2. The three families

| Family | What a route in it must prove | What is proved | Where it stops |
|---|---|---|---|
| **P — producer** (estimates with cancellation) | a bound on a prime sum at exponent ½ + ε, or a lever below the seed | Θ ≤ 20999/24000 [L] | the vertex of the probe's exponent budget lies in (40535/46328, 20999/24000] ([`endpointExponent_three_bin_pos_of_lowBoundaryGen_le`](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheTrueVertexBelowSevenEighths.lean#L328) [L]) |
| **R — sign** (index of Weil's form) | nonnegativity at every aperture, equivalently index one of every neutral window ([`riemannHypothesis_iff_forall_hermNegIndex_neutralWindow_eq_one`](../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheRiemannHypothesisIsOneNegativeSquareOfTheNeutralPartOfEveryWindow.lean#L622)) | all tests: apertures ≤ log 2, ratios ≤ 3 | for all tests the sign is proved at fixed apertures only; the floors with a rate (log-energy floor, margin law, doubling law) are transfers of the P seed; pure gluing has doubling factor √2 ([`doublingLaw_sqrt_two`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L149) [L]) |
| **U — uniformity** (tail, collisions, all orders) | exclusion of a finite top layer; reality at every height, degree or period | finite heights, degrees and ranks | every finite layer occurs in a model with every property used except the exact functional equation together with integrality ([`asymptoticAbscissaLaw_or_exists_meromorphic_tempered_euler_oneOff`](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/TheMeromorphicTemperedEulerFirewall.lean#L1687), [`frontier_dichotomy`](../../../formal/GaloisForLFunctions/WorldsOfTheZeroConfiguration/FakeEditsWithSubpolynomialDefectEnergy.lean#L699)) |

## 3. Obstacle register

**(a) Just work** — solvable with known methods; details in [obstacles summary §2.1](obstacles-summary.md#21-just-work-tasks).

| ID | Task |
|---|---|
| J1 | Restate at 20999/24000 the results written at 7/8, 3/8 or 1/16 |
| J2 | Jensen rung d ≤ 31929 from width 8999/24000 at height 67 |
| J3 | Integrate the source-only modules graded [S] |
| J4 | Conductor exponent and Gamma factor of an Artin completion as invariants of the representation |
| J5 | Tools the tensor-power programme lists as "to build" |
| J6 | The order-six Kubota series: continuation and functional equation |
| J7 | A Hecke family of ℚ(ω) with an infinity-type parameter inside the probe |
| J8 | Fixed-aperture certificates beyond log 2 (ratio four, the fourth ladder excess) |
| J9 | Further finite rungs from a larger verified height |
| J10 | The elementary bound for cubic character sums from the Stepanov count |
| J11 | The top-octave statement for ζ as one theorem, composed from two integrated statements |

**(b) Obstacles** — O11 is resolved for reciprocal quadratics; the others remain open. Details in [obstacles summary §2.2](obstacles-summary.md#22-open-obstacles).

| ID | Family | Problem |
|---|---|---|
| O1 | P | Row count U^(1−δ+ε) in the binding bins of the cubic probe |
| O2 | P | A signed evaluation before Cauchy–Schwarz: the first moment of the row root numbers on long columns |
| O3 | P | A zero-free half-plane for one Grössencharacter L-function of nonzero infinity type, uniform in the level |
| O4 | P | A joint completion of a Möbius-signed monomial of period k ≥ 7 at the price k/2 |
| O5 | P/U | A pole law with a source that does not know the zeros (a pencil through ζ, one Deligne lever), or sign levers at all large periods |
| O6 | P | Half-power cancellation of the actual Möbius or Liouville coefficients |
| O7 | P | Exclusion of root coincidences ζ(ρ) = ζ(ρ/k) = 0 for k = 2, …, 6 |
| O8 | R | The sign of Weil's form at every aperture |
| O9 | R | A doubling factor below √2 proved from the window matrices |
| O10 | R | An effectivity, section or count law whose definition does not contain the sign |
| O11 | R | **Resolved for reciprocal quadratics:** a negative Euler logarithmic coefficient occurs at `p²,p⁴,p⁶` or `p⁸`, while ζ's four values are positive ([`exists_negative_even_eulerLogCoeff`](../../../formal/GaloisForLFunctions/SelbergClass/PositiveFiniteEulerLogarithmicSigns.lean#L47) [K]) |
| O12 | U | AAL: no finite nonempty top layer |
| O13 | U | Zeros approach the line; landing uniform as σ ↓ ½ |
| O14 | U | Reality of the heat flow inside near-coincidence clusters for t < ½/log X |
| O15 | U | One exponent for all orders (period, degree, rank, mollifier length) |
| O16 | U | The sign of the forward monodromy group of the heat flow |

## 4. Live routes

Each row: the receiver (proved), the hard obstacle, and its split into (a) and (b).

### 4.1 Family P — cancellation and estimates

| Route | Receiver and what is established | (a) Just work | (b) Open problem |
|---|---|---|---|
| **MC** Möbius cancellation at half power | Half-power cancellation ⇒ RH. Θ ≤ 20999/24000 and M(N) = O(N^(7/8)) [L] ([`exists_mertens_le_seven_eighths_exact`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheAbscissaAvoidsAnIntervalBelowSevenEighths.lean#L229)); Möbius-signed squarefree-ideal sums O(Q^ε X^a) for a > 20999/24000, uniform over ray class characters of ℚ(ω) [L] ([`exists_uniform_signed_squarefree_bound`](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/UniformSmoothedHeckeMobiusBounds.lean#L166)); logarithmic two-point Chowla [L] | J1 | O6, staged as O1–O5 |
| **JAS** joint ancestry | Level-one dressed positivity ⇔ RH; Θ ≤ b ⇔ signal of the zeta kernel O(Z^(b′)) for b′ > b [L] ([TheSignalExponentIsTheZeroAbscissa](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSignalExponentIsTheZeroAbscissa.lean)); signal bound O(Q^ε Z^a), a > 20999/24000 [L], derived from the seed; shell signs on infinitely many dyadic prime shells ⇒ AAL [L] | J1 | signal cancellation at every b > ½ (O6); dressed positivity (O8) |
| **SQF** weighted squarefree count | One-sided O(t^(−1/4−ε)) ⇔ RH. ((s−1)ζ(s))^m/ζ(2s) pole-free on Re s > β/2 ⇔ Θ ≤ β for ½ ≤ β < 27001/48000 [L] ([`squarefreePowerQuotient_poleFree_iff_zetaZeroAbscissa_le_sub`](../../../formal/GaloisForLFunctions/ZeroForcingCalculus/EulerDilationAndRootCoincidenceExclusion.lean#L309)); ζ(ρ/k) ≠ 0 for k ≥ 7 [L] ([`riemannZeta_div_nat_ne_zero_of_seven_le`](../../../formal/GaloisForLFunctions/ZeroForcingCalculus/EulerDilationAndRootCoincidenceExclusion.lean#L212)) | — | quarter-power bound for one sign (O6); k = 2, …, 6 (O7) |
| **WD** Ward orientation, long mollifiers | Cofinal long-prefix moments O_θ(T^K) with K independent of θ ⇒ RH. Least slope loss = 2w [L] ([`zetaZeroWidth_le_of_slopeLaw`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestSlopeLossOfTheLongMomentsIsTwiceTheWidth.lean#L68)); slope 8999/12000 [L] ([`slopeLaw_sub_three_quarters`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheAbscissaAvoidsAnIntervalBelowSevenEighths.lean#L335)) | — | zero-loss length doubling, K independent of θ (O15) |
| **CTF** chronological tail, Báez-Duarte | Rows reaching every tolerance ⇔ RH; a real mollifier of length T^θ has mean square ≥ (1 + 1/(8+6θ))T [L] ([`necessary_length_uniform`](../../../formal/GaloisForLFunctions/ArithmeticProduction/TheNecessaryLengthOfAMollifier.lean#L702)) | — | vanishing-error rows, the BSY sign, near-unit budgets (O6, O15) |
| **PBM** regularized log-ζ abscissa | Partial sums of (Λ(n)−1)/log n at exponent ½ + ε ⇔ RH | — | O6 |
| **RB** Robin, Nicolas | Eventual Robin inequality on colossally abundant integers ⇔ RH | — | O6 |
| **SZ** Suzuki screw | Bounded Ward residual A_N ⇔ RH; \|A_N\| ≤ C√N·exp(−c·vkScale) [L] | — | bounded unnormalized residual (O6) |
| **TT** theta tail, heat–Cassini | Bounded D_t + Q_t/2 for each 0 < t < ½ ⇔ RH; uniform bound on a shrinking band [L] | — | a fixed positive t (O6, O15) |
| **PM** physical model (scattering, ringdown) | Quarter-rate decay ⇔ RH ([`riemannHypothesis_iff_pulse_ringdown`](../../../formal/GaloisForLFunctions/BlackHoleRingdown/TheRingdownRateIsTheZeroFreeStrip.lean#L650)); rate δ ⇔ zero-free strip of depth 2δ ([`zeroFreeStrip_iff_pulse_ringdown`](../../../formal/GaloisForLFunctions/BlackHoleRingdown/TheRingdownRateIsTheZeroFreeStrip.lean#L625)); horocycle exponent 1 − Θ/2 [L]; strip 1/16 [L], 3001/48000 [S] | J1, J3 | a rate beyond the seed (O6); a Krein or reflection sign (O8) |
| **BAG** deterministic self-return | Power-many separated returns of ζ to itself ⇒ exclusion of a zero; graded count fewer than T^c returns, c > (30/13)(1−σ) [L] | — | lower bounds for ζ-target returns; a bounded phase return (O12) |

### 4.2 Family R — the sign of Weil's form

| Route | Receiver and what is established | (a) Just work | (b) Open problem |
|---|---|---|---|
| **RW** restricted Weil ground energy | μ(a) ≥ 0 at every aperture ⇔ RH. Floors as in §1; μ(a) = the floor of Weil's form on step packets of the windows inside a [L] ([`stepFloor_iff_le_groundEnergy`](../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheGroundEnergyOfAnApertureIsTheFloorOfWeilsFormOnTheWindowsInsideIt.lean#L500)); width ≤ β ⇔ W(u,u) ≥ −C(1+a)e^(2βa)(E_log(u) + ‖u‖²) [L] ([`isRuler_logEnergyFloor`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWidthIsTheRateOfTheWeilFloorInTheLogarithmicEnergy.lean#L428)), rate 8999/24000 [L] ([`logEnergyFloor_sub_three_eighths`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheAbscissaAvoidsAnIntervalBelowSevenEighths.lean#L341)) | J3, J8 | O8; the rate-zero floor |
| **WL** Weil lag function | Bounded endpoint energy ⇔ RH; every finite Gram of the prime lag PSD ⇔ RH [K]; lag growth rate ≤ 3/8 [L] | J1 | O8 |
| **HF** positive Hodge form | λ(R) ≥ 0 at every R ⇔ RH; λ(R) attained with a unique minimizer [L]; outer, cyclic minimizer and transverse gap at every R [S]; off RH a unique transition at R = W₀ [S] ([`offLine_arithmetic_hawking_page_transition`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ArithmeticHawkingPagePhaseStructure.lean#L440)) | J3 | exclusion of the finite-W state (O10) |
| **HAT-C** arithmetic-clock Green energy | Corrected energy + jump tail = Weil's form at any fixed height [K]; a lower bound by minus the jump tail at all apertures ⇔ RH [K] | — | O8 |
| **CHMD** causal hyperbolic–modular duality | One-sided bounded prime wave ⇒ RH | — | O8 |
| **TH** theta moment positivity | All-rank Hankel positivity ⇒ RH; ranks ≤ 14 positive for 0 < a ≤ ½ [L] | J9 | signed adaptive heads at every aperture and degree (O8, O15) |
| **RN** theta renewal | Exclusion of joint energy and cross-flux nodes ⇒ RH | — | O8 |
| **EWU / OWU** even and odd weight uniqueness | Even (odd) positivity at every aperture ⇒ RH; even floor 10⁻¹³ and odd floor 10⁻¹⁰ at log 2 [S] ([`weilQuad_ge_even_at_aperture_log_two`](../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheEvenWeilFormHasAFloorAtApertureLogTwo.lean#L4149), [`weilQuad_ge_odd_at_aperture_log_two`](../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheOddWeilFormHasAFloorAtApertureLogTwo.lean#L3966)); an even test with W < 10⁻⁹‖F‖² [S] | J3, J8 | the sign beyond log 2 at every prime-power entry (O8) |
| **GTA** transverse Schur charge | Arbitrarily small cofinal quartic charge ⇒ RH | — | O8 |
| **ACT** arithmetic criticality | One shift paying every even profile ⇒ RH; {2,3,4} kicks below 991/1000 of the Lévy energy [L] | J8 | retained-variance payment beyond log 2 (O8) |
| **AIP** arithmetic incidence positivity | Subexponential signed cost of the reflected prime–polar ledger ⇒ RH | — | O8 |
| **SC** Stokes, Witt–Krein | Glued index ≤ 1 ⇒ RH; sublinear tensor loss ⇒ RH; Gaussian-damped coupling bounded ⇔ RH [L] | — | O8, O15 |
| **ACS** arithmetic Castelnuovo–Severi | Index one of every neutral window ⇔ RH. Gap 1/50000 through ratio 10609/5000 [L]; ratio three and below four [S] ([`greenForm_two_prime_window`](../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheTwoPrimeWindowAndRatioThreeHoldAtEveryBlockSize.lean#L61)); best doubling factor 2^w [L] ([`zetaZeroWidth_le_logb_of_doublingLaw`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestDoublingFactorOfTheMarginIsTwoToTheWidth.lean#L178)); RH ⇔ a constant level law of the margin [L] ([`riemannHypothesis_iff_exists_const_isLevelLaw`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheLossOfTheMarginIsBoundedOrPolynomial.lean#L61)); HodgeIndex ⇔ an effectivity with Riemann–Roch and ampleness [L] ([`exists_effectivity_iff_hodgeIndex`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HodgeIndexFromEffectivity.lean#L102)) | J3, J4, J8 | O8, O9, O10 |
| **ECP** endpoint character positivity | PSD character Grams at every rank ⇔ RH; minors through order 200 [L] | J9 | mixed Young shapes at arbitrary rank (O8, O15) |
| **PA** prime–archimedean passivity | Hausdorff-row signs for all (k, r) ⇔ RH; signs for r ≥ min(C₀(k+1)², S(k)) [L] | J9 | the remaining entries, uniformly in k (O8, O15) |
| **LI** paired Li balances | Primitive bounded below ⇔ RH; Li signs n ≤ 314 [L] | J9 | a sign uniform in n (O15) |
| **HCF** Gaussian heat trace | Both prime-log grids positive at every degree ⇒ RH | J9 | all degrees (O8, O15) |
| **SRT** prime-side lag localization | Width ≤ σ ⇔ the cubic prime trace ≥ −K·p^σ on cofinal windows of radius 32 log(T+2) with ≤ C·e^(δT) omissions [L]; RH ⇔ one growth exponent for all even prime-trace moments ([`riemannHypothesis_iff_moments_primeTraces`](../../../formal/GaloisForLFunctions/SurfaceOfSpecZ/TheTensorPowerTrick.lean#L34)); a pencil through ζ exists ⇔ RH [L] ([`riemannHypothesis_iff_nonempty_pencil`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/TheAxiomsOfAPencilThroughZeta.lean#L188)) | — | the bound at σ = 0 from arithmetic (O6); O5, O15 |
| **FU, CFC, RP** history criteria | One-sided bounds of a signed prime history across advancing clocks ⇒ RH; exact history criteria [L] | — | estimates on advancing histories (O8, O15) |

### 4.3 Family U — zero geometry, tail and uniformity

| Route | Receiver and what is established | (a) Just work | (b) Open problem |
|---|---|---|---|
| **ZCG** zero-configuration geometry, heat descent | No positive real branch time ⇔ RH; RH ⇔ Λ_X = 0 for every X ([`riemannHypothesis_iff_forall_localNewmanConstant_eq_zero`](../../../formal/GaloisForLFunctions/RHTower/Heat/TheLocalDeBruijnNewmanConstant.lean#L103)); zeros of H_t with \|Re z\| ≥ 2π·e^((6600/9991+ε)/t) real and simple ([`riemannHeat_zeros_real_simple_subWeyl`](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/HeatScaleRepulsion/SubWeylCollisionFreeHorizon.lean#L1166)); Λ ≤ 80982001/1152000000 [L]; forward monodromy of index ≤ 2 in the signed permutations [L] | — | O14; O16; O12 with O13 for the alternative path |
| **LA** Jensen line anchor | Real-rooted Jensen polynomials at unbounded degree ⇔ RH; real-rooted through degree 31922 [L] ([`jensenNonrealCount_eq_zero_of_le_31922`](../../../formal/GaloisForLFunctions/VerifiedHeightRungs/TheJensenPolynomialsThroughDegree31922AreRealRooted.lean#L21)); N_d ≤ 300√(d log d) at large d [L] | J2, J9 | unbounded degree (O15) |
| **PTR** cosine-source zero loss | Collision-free descent in the shift h ⇒ RH; strict Laguerre inequality for h ≥ ½ and in the Vinogradov–Korobov region [L] | — | every height below the classical region (O14) |
| **TG** topological sub-unit gate | Trace norm of the anchored cubic defect below one on every formation rectangle ⇒ RH | — | the trace-norm bound (O6) |
| **XN** Newton invariant discs | Line-centred self-map discs covering every zero ⇒ RH | — | interior minima of the margin (O8) |

Scope guards recorded with the routes: RH ⇔ zeros approach the line ∧ (finite off-line set ⇒ RH) ∧ landing ([`riemannHypothesis_iff_three_atoms`](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheLandingLawForZeta.lean#L68)); Θ < 1 or AAL ([`quasiRH_or_asymptoticAbscissaLaw`](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/QuasiRHIsATailLaw.lean#L27)), and Θ < 1 is proved, so this disjunction gives no information on AAL.

## 5. Route candidates

A candidate has a detector or receiver and no source-to-receiver step.

| Candidate | What exists [L] | Missing step | Class (reading of this report) |
|---|---|---|---|
| **SEC** prime–Gamma seam | Factorial-Fock boundedness ⇔ Re s = ½ at every strip parameter | a ζ-selective bound from the Sonin source | O8 |
| **CDC/BSH** repair consistency | Marked prices agree ⇔ Re s = ½ | arithmetic descent on the actual zero fibres | O8 |
| **S3** prime returns to one window | The transfer to bounded prime traces on log² windows is equivalent to RH [L] ([`homogeneousReturnWindowTransfer_iff_riemannHypothesis`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L254)) | the transfer itself | O6 |
| **APF** arithmetic paired Fredholm | Source-first cycles; trace reconstruction on real labels | full-divisor exhaustion | O12 |
| **EGC** pole-safe contour | Explicit contour constants; count error ≤ 32ε²·log T/T | height-fibre isolation and an outer landing | O13 |
| **EWJ** Euler/Wold jets | All-depth reporter; strong prefix convergence | endpoint admission outside the blind plane | O8 |
| **FEL** theta likelihood | Probability and entropy accounting | a predeclared history that forces the BSY sign | O6 |
| **IRK** rotation-algebra trace | Integral idempotent traces; a finite free resolution of the Meyer–Ξ packet | a projective or index realization faithful to the source | O10 |
| **MSC** Möbius–Sonin transport | L² admission of the critical discrepancy | a Sonin or Weil sign | O8 |
| **RFHM** support grade | Full support, phase and grade admission | a source-defined orientation law | O8 |
| **W1C** Clifford–Dirac, Lee–Yang | A finite ferromagnetic receiver; index-one approximants suffice | couplings converging on one real interval, or a positive reflection form with self-adjoint generator | O8, O10 |
| **WBF** source certificates | Gram determinants recover coefficient magnitudes | an arithmetic certificate stream with phase orientation | O8 |

## 6. Support programmes with an open item on a route

| Programme | Result that bears on a route | Open item | Class |
|---|---|---|---|
| Metaplectic descent, family continuation, exponent dynamics, reciprocity families | the seed and its transfers; the stage walls 13/15, 5/6, 2/3, 3/5 (walls ledger P3–P12) | O1–O4 | P |
| Tensor-power programme | a pole law is equivalent to the width for flow data and abelian bases ([`exists_poleLaw_iff`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/TheTensorMomentsOfAFlowDatumHaveBaseLossExactlyOne.lean#L510), [`exists_twistPoleLaw_iff`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/AnAbelianBaseIsARuler.lean#L568)); one Deligne lever or sign levers at all large periods give RH ([`riemannHypothesis_of_deligneLever`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/TheThreeLinesOfFrames.lean#L84), [`riemannHypothesis_of_signLevers`](../../../formal/GaloisForLFunctions/TensorPowerProgramme/TheThreeLinesOfFrames.lean#L94)) | O4, O5 | P/U |
| Green calculus of the window, floor-tree mixing, absolute geometry | index one through ratio three; gluing through the dyadic middle ([`riemannHypothesis_iff_forall_overlap_contraction`](../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/AWindowGluesItsTwoOverlappingPartsThroughItsDyadicMiddle.lean#L519)); top-octave blindness | O9, O10 | R |
| Selective arithmetic | a window sign at one aperture excludes nothing ([`exists_zetaDensity_positive_window_deep_zeros`](../../../formal/GaloisForLFunctions/SelectiveArithmetic/TheRungSignSurvivesDeepZerosAtZetaDensity.lean#L90)) | a sign with a cluster exclusion | R |
| Counting and scattering holography, modular horizon, ringdown | rate ⇔ strip; the count door ([`exists_count_tateLimit_iff`](../../../formal/GaloisForLFunctions/CountingHolography/TheCountDoorOfACurveAndOfZ.lean#L39)) | O10; O11 resolved for reciprocal quadratics | R |
| Floor-free arithmetic, auxiliary dynamics, exceptional layers, worlds, Euler–FE transport | non-attainment and phase-return receivers of AAL; realizability of finite layers | O12 | U |
| Galois theory of zeros, nodal geometry, finite free probability | monodromy of the heat flow; collision laws | O14, O16 | U |
| Verified height rungs, aperture floors | finite rungs; no positive floor of Weil's form holds along unbounded apertures: μ(A) ≤ K·exp((11/2)A − π·e^(2(A−2))) for A ≥ 3 [L] ([`not_exists_positive_floor_along`](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/TheApertureFloorMustDecayDoublyExponentially.lean#L110)) | none that transfers | U |
