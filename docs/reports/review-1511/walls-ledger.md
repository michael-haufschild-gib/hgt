# RH wall ledger

Three families organize the closure problems. They are classes of research obligations, not three equivalent propositions; a route can meet several.

| Family | Question | Typical failure |
|---|---|---|
| **P — production** | Can an arithmetic argument move the zero width `w = Θ − ½`, i.e. prove a bound the seed does not already give? | A ruler of `w` is improved in form only; absolute values, averaging or completion erase the saving or the target. |
| **U — uniform exclusion** | Does control cover every stage (aperture, ratio, block size, degree, height, heat time) and every finite or shallow exceptional configuration? | A finite-stage theorem with no limit; a finite top layer or shallow tail survives. |
| **R — faithful realization and selection** | Does a constructed object carry the exact arithmetic source of `ζ`, with Euler product, functional equation and integrality used together? | The object is a fake (Euler world, cosh model, prime edit, deformation) on which the claimed mechanism holds and the conclusion fails. |

Statuses: **Open** — no proof in the Lean corpus; **Excluded** — a proved obstruction for a stated construction class; **Available** — a proved input. Statements are read in Lean source at checkpoint `cf08f8dfc5` with the working tree of 15 Nov 2026; items marked [W] are untracked working-tree modules, [S] are tagged unintegrated by the frontier map. No build, compile or axiom audit underlies these labels. Evidence: [working log](../../../logs/review-1511-working-log.md); route detail: [route report](route-obstacles.md).

## Organizing principle

**Measuring is not moving.** A ruler of `w` is a family `P β` with `w ≤ β ⇔ P β`. Its readings are exactly the bounds of `w`; two rulers agree reading by reading; a map on exponents improves every reading of one ruler iff it improves every bound of `w`, so a lever proved on one ruler is a lever on all [MEASURING] [LEVERTRANSPORT]. An assembly of rulers is a ruler. Every P-wall is therefore one question — produce a lever or a seed for `w` — seen on different rulers; every U-wall either reduces to a ruler at rate zero or to one of the three atoms ZAL, `FiniteOffLine → RH`, Landing [THREEATOMS].

## Available inputs

| Input | Exact extent | Boundary |
|---|---|---|
| **Seed** | `ζ(s) ≠ 0` for `Re s > 7/8`; every Dirichlet `L(s,χ)` of every modulus; the Hecke family of `ℚ(ω)`; hence `1/8 ≤ Re ρ ≤ 7/8` [MMD] [MMD_DIR] [MMD_HECKE] [MMD_STRIP] | The only seed. It is false for two-sided edits of the rational primes with count `Ax + O(x^{14/15})`: their zeros right of `7/8` lie on any prescribed line `Re s = σ ∈ (7/8, 14/15)` [EDIT]. The seed uses arithmetic of the rational primes beyond their count. |
| **Seed on every ruler** | `Λ ≤ 9/128`; slice heat threshold `≤ 3/64`; `M(n) = O(n^β)` for `β > 7/8`; Möbius prefix at one height, unit window, long moments, signal and two-end state at rate `3/8`; joint-ancestry abscissa gap law; return transfer ⇔ RH with no premise [NEWMAN] [HEATTHR] [MERTENS78] [RETURNRH] [RULERS] | Readings of the same bound `w ≤ 3/8`. |
| **Exact rulers of `w`** | Zero abscissa; Möbius polynomial at one height; one unit window of `ζM_X`; zeros of `M_X`; signal of the zeta kernel; two-end antisymmetric state [RULERS]; Weil floor in the logarithmic energy [LOGENERGY]; neutral-window margin law at block sizes `K¹⁰ ≤ ρ(K) ≤ K^A`, with infimum of rates equal to `w` [MARGINRULER] [MARGINSINF] [W]; doubling law of the margin, best factor `2^w` [DOUBLING] [W]; abscissa of the cubic-probe correction `= (3 + Θ_rung)/6` [RUNG] [W]; long Möbius moments with common `K` [WD-LONG]; Weil-lag endpoint dictionaries [WL]; prime-log windows [SRT]; regularized prime series [PBM] | A ruler reads `w`; it produces nothing. |
| **Unconditional margin depth** | Every neutral window of ratio `3K+1` and block size `R` has at most one eigenvalue below `−C(1+log K)²K^{3/8}(1+log R)`; at `R ≤ K^A` the shift `C K^{3/8+ε}` suffices [MARGIN38] [MARGINPOLY] | The factor `1 + log R` is the clustering of off-line zeros at the resolved height (wall U9). |
| **Jensen rung** | No nonreal root through degree `31922` [JENSEN] | Finite degree. |
| **Two-prime window** | Even floor `10⁻¹³`, odd `10⁻¹⁰` on `[−log 2, log 2]`; an explicit even test has quotient `< 10⁻⁹` [EVENLOG2] [ODDLOG2] [UPPERLOG2] [FLOORLOG2] [S] | No floor at a larger aperture in Lean. |
| **Overlap ladder** | Ratio `≤ 3` for `Q ≥ 2`, `< 4` for `Q ≥ 3` at every block size; `levelAt Q k = 0` for `k ≤ 3, Q ≥ 2` and `k ≤ 4, Q ≥ 3` [OVERLAP] [LOGLADDER] [FOURTH] | `Q = 2` fourth step (ratio `≈ 3.20989`) open [FOURTHRED]. |
| **Full-space critical arithmetic** | Tilted spline: `c⁻⁷` floor for every exponent `< 1/8`; one critical multiple; certified complement interval [SUBCRITICAL] [CRITICAL-SMALL] [COMPLEMENT] | Positivity at every bounded multiple of the critical overlap is RH [CRITMULT]. |
| **Index law** | Some neutral window has `r` negative squares iff `r ≤ 1 + #(right zeros)` [INDEXLAW]; real packet index = number of distinct right zeros [INDEX] | Counts zeros; excludes none. |
| **Critical half-line structure** | RH, or a unique-up-to-sign, outer, cyclic critical state with Laplace transform zero-free on the closed right half-plane [HF] [HF-OUTER] [HF-CYCLIC] [HF-BOUNDARY] | Excluding the actual state. |
| **Heat and monodromy** | Finite arithmetic actions are heat monodromies on continued windows [HEAT-FINITE]; a forward collision off the centre exists at arbitrarily large forward time [OFFCENTRE] | Whole-fibre identification excluded [HEAT-NOGO]; sign of `G₊` open (U6). |
| **Zero fields** | Finite Galois layers; orbit degree = residue-field degree; quartet, width and ordinate criteria; conjugation central iff all ordinate values lie in `B` [PRIME-FIBRES] [ORBIT] [QUARTET] [CONJCENTRAL] [INVOLUTIONS] | No arithmetic restriction on the position of conjugation (R4). |
| **AdS dictionary** | Strip width `δ ∈ (0, 1/4]` of the two-boundary correlator ⇔ zeros in `Re ρ ≤ 1 − 2δ`; `δ = 1/16` unconditional [ADS] | Strip is a ruler of `w`. |
| **Exceptional layers** | AAL fails exactly at a finite nonempty top layer [AAL-LAYER]; growing filters reach polynomially many cofactors [COFACTORS] [NEARDIAG] | Prime-weighted cofactor cancellation (P6). |
| **Census and density** | Simple critical proportion `≥ 0.67250071` [CENSUS]; density exponent `30/13` [DENSITY] | Proportions and densities leave every finite configuration. |

## P — production

| Wall | Status and exact obstruction | Surviving target | Routes |
|---|---|---|---|
| **P1 Critical cancellation** | **Open.** Every growth route is a ruler or receiver of `w` at exponent zero (Möbius Hilbert form, signal, Weil lag, long moments, regularized prime series, Robin, squarefree count). The seed is transmitted to each; none moves it [RULERS] [MC] [WL] [WD-LONG] [PBM]. | A signed estimate on a literal μ/Λ observable beyond the seed, i.e. a lever (P8) or a second seed. | MC, WL, FU, CFC, RP, SQF, TT, CHMD, LI, PBM, RB, WD, JAS, AIP, SZ |
| **P2 Gauss completion** | **Excluded class.** Every Möbius-signed Gauss/Jacobi pairing has uncoupled boundary `≥ 2/3` and coupled centre `≥ 3/5`, attained only at `(3, 6)` [GAUSS] [GAUSS_UNC] [GAUSS_INF]. Towers mixing pairings stay `≥ 3/5` [MIXED]; closing the Gauss levers under composition and minimum keeps the wall at `3/5` [WALLGEN]. | A source outside the Gauss-monomial class with an independent reflection. | MC, JAS, producer |
| **P3 Truncated family continuation** | **Open signed problem; excluded absolute repair.** Truncations `L ≥ 3` keep correction zeros in `7/12 ≤ Re s < 2/3`; the absolute sixth-power tail costs `≥ cZ^{2/3}` [TRUNCATION]. The continued correction vanishes exactly at zeros of a weight-one sextic Grössencharacter `L`-function [CORRZERO]; its abscissa is `(3 + Θ_rung)/6`, so the frame is a ruler between two abscissas and `7/8` for the rung is `31/48` for the correction [RUNG] [RUNG3148] [W]; the coupled tower reaches `3/5` only under per-level signal estimates [GROSSENTOWER]. | Target-preserving signed cancellation across continued rows. | producer, MC, JAS |
| **P4 Phase/target loss** | **Excluded averaging.** The six-phase mean kills the `ρ⁻¹` target mode [AVERAGE]; ordinary genealogy determinants are coefficient-blind [WBF]. | Nonprincipal extraction keeping the target. | MC, JAS, WBF, APF |
| **P5 Complete signed payment** | **Open; a ruler in log-energy normalization.** The Weil floor `W(u,u) ≥ −C(1+a)e^{2βa}(E(u) + ∫|u|²)` on all smooth sources holds iff `w ≤ β`; at `β = 0` it is RH [LOGENERGY] [LOGENERGY0]. Whole-space threshold = polar threshold [POLAR]; the absolute edge cost crosses one in `(½log 5, ½log 6]` [EDGE]. | Signed payment of prime, pole, Gamma and variance terms at every aperture — equivalently `w = 0` on this ruler. | RW, HF, EWU, OWU, ACT, AIP, HAT-C, SZ, RN, SC, ACS |
| **P6 Restricted cofactor cancellation** | **Open.** Filter and unweighted near-diagonal errors are controlled; the prime-weighted restricted cofactor aggregate is not [COFACTORS] [NEARDIAG]. | Beat the isolated top residue with both continuum corrections retained. | AAL, BAG, ZCG |
| **P7 Higher source constraints** | **Open.** Hermite/Hausdorff flags, quartic charge decay, endpoint-character sign [TH] [PA] [GTA] [ECP]. Formal jet independence gives no inequality [JETS]. | A higher-order source estimate. | TH, PA, GTA, ECP, HCF |
| **P8 Lever existence** | **Open; three excluded classes.** No lever `Θ ≤ b ⇒ Θ ≤ T(b) < b` is proved for `ζ`. A lever valid on all integer-norm Euler worlds (linear count, no functional equation) cannot bite on `(½, 2/3)`, since these worlds realize every abscissa there with any smaller tail abscissa [EULERWORLD] [TWOTHIRDSWORLD]; a lever valid on all cosh models (order one, functional equation, no Dirichlet series) bites nowhere [COSH]; a frame with centre `< 2/3` is a lever in neither family [FRAMEWORLD]. | A lever, or a gap law for `Θ`, whose proof uses the Dirichlet series and the functional equation of `ζ` together. | all ruler routes |

## U — uniform exclusion

| Wall | Status and exact obstruction | Surviving target | Routes |
|---|---|---|---|
| **U1 All stages** | **Open; partly reduced to P.** Fixed degree `31922`, aperture `log 2`, ladder depth four, one critical multiple are finite stages [JENSEN] [FLOORLOG2] [FOURTH] [CRITICAL-SMALL]. The margin and log-energy stages are rulers: their uniform statement is `w = 0` [MARGINRULER] [LOGENERGY]; a doubling law of the margin with factor `λ` is the half-plane `w ≤ log₂ λ`, and the best factor is `2^w` [DOUBLINGHP] [DOUBLING] [W]. A zero of depth `1/a` can hide from aperture `a` above height `e^{4a}` in configurations of logarithmic density [HIDDEN]. | Either a stage map with contraction on a ruler (a lever), or an atom. | LA, HCF, TH, RW, SRT, HF, ACS |
| **U2 Long-moment quantifiers** | **Open.** One `K` for unbounded `θ`; `C_θ` may vary [WD-LONG]. | A stage map in `θ` with loss below the seed slope. | WD, MC |
| **U3 Finite stratum** | **Open.** Real packet index = number of distinct right zeros; `FiniteOffLine → RH` iff that index is `0` or `∞` [INDEX]. | Rule out a finite positive index for the actual source. | AAL, ACS, ZCG, BAG, PM, W1C |
| **U4 Landing and tail** | **Open.** RH ⇔ ZAL ∧ `FiniteOffLine → RH` ∧ Landing [THREEATOMS]; Landing ⇔ a Hadamard threshold bounded as `σ ↓ ½` [LANDING-TFAE]. | Prove the atoms separately. | AAL, ZCG, BAG, SRT, JAS, SC |
| **U5 Critical state** | **Open.** The possible critical state is unique, outer, cyclic, Laplace zero-free [HF] [HF-OUTER] [HF-CYCLIC] [HF-BOUNDARY]; source-tilted confinement selects an endpoint with no endpoint sign [ENDPOINT]. | An arithmetic property incompatible with the state. | HF, RW, ACS |
| **U6 Heat time zero and monodromy sign** | **Open.** Uniform injective nonreal continuation forces finite off-line support [HEAT-UNIFORM]. A proper `G₊` forces `8 | N(t)` at every real `t > 0` [HEAT-EIGHT]; one isolated double collision off the centre gives `G₊ = W` [DOUBLECOLL]; a forward multiple zero off the centre exists [OFFCENTRE] (order two and isolation not proved). | Decide `G₊`; quantitative source-selective control as `t ↓ 0`. | ZCG, LA, PTR |
| **U7 Uniform margin** | **Excluded targets; exact reading.** The bare dilation process has no gap [TREE-GAP]; under RH long-window continuum margins tend to zero [MARGIN-DECAY]. Bounded margin on all neutral windows ⇔ RH [ACS]; the margin exponent at polynomial block size equals `w` [MARGINSINF] [W]. | A fixed-`Q` gap on bound windows [GAP], or a doubling factor `< √2` derived from the gluing data (a half-plane) [DOUBLINGHP] [W]. | ACS, RW, HF, SRT |
| **U8 Detection versus exclusion** | **Open.** Cox detection nonuniform near residual zero [COX]; Fock, dark-history and Newton criteria keep global inputs [SEC] [CDC] [XN]. | Uniform control with a residual gap. | SEC, CDC, XN |
| **U9 Clustering at the resolved height** | **Open.** The margin converse holds for every block size with the factor `1 + log R`, and without it only at block sizes polynomial in the ratio [MARGINDEPTH] [MARGINPOLY]; the mass-normalized Weil floor is a half ruler because a unit window may carry `C log T` off-line zeros [LOGENERGY] [SAMPLING]. | A bound on off-line zeros per unit window at depth `≥ δ`, uniform in height. | ACS, RW, SRT, HF |

## R — faithful realization and selection

| Wall | Status and exact obstruction | Surviving target | Routes |
|---|---|---|---|
| **R1 Global arithmetic geometry** | **Open.** Contact conductors exist; nonnegative diagonals fail; admissible diagonals carry logarithmic negative self-pairings; `VF` carries a divisibility mask [CONTACT] [CONTACT-EX] [DIAGONAL] [WITT]. | A global intersection theory with the actual diagonal and an index theorem. | ACS, F₁, HF, PM |
| **R2 Finite-rank absolute gluing** | **Excluded class.** At ratio four and `600(r+1) ≤ H` every rank-`r` lowered model has `≥ 2` negative squares [RANK-WALL]; no contact-sign-blind bound proves the first overlap step [DIPOLE]. | Signed, growing-rank coupling. | ACS, RW, HF |
| **R3 Arithmetic/heat identification** | **Excluded comparisons.** No whole-fibre intertwiner [HEAT-NOGO]. | Finite-window data with controlled losses. | ZCG, LA, Galois |
| **R4 Galois purity** | **Open.** `Re ρ = ½` iff `p^{2Re ρ} ∈ B` and some automorphism sends `ρ ↦ 1 − ρ` [REFLECTION]; an orbit leaves its quartet only through another off-line quartet of the same ordinate [LEAVEQUART]; square relations among height radicands involve an even number of critical heights [SQREL]. | An arithmetic restriction on the position of conjugation. | ZCG, LA, Galois |
| **R5 Physical axioms** | **Excluded inference.** Prime-2 deformations keep causality, Euler product, completed FE, passivity, axis unitarity and the pole dictionary, with decay thresholds `→ 0` [ADS-NOGO]. | A principle that selects the integral unit-multiplicity gates and controls decay. | PM |
| **R6 Local versus global** | **Open; counterexamples to automatic promotion.** Cyclic-local splitting without global splitting [LOCAL-GLOBAL]; finite resolutions [IRK]; the rational Steinberg quotient is two square-zero sectors [STEINBERG]. | Global obstruction vanishing for the actual source. | IRK, MSC, ACS |
| **R7 Reversible sewing** | **Excluded class.** All-prime reversible sewing kills nonempty support [RFHM]. | Nonreversible or larger carrier. | RFHM, JAS |
| **R8 Global roots and parity** | **Excluded global target; open regional construction.** `ξ` has critical zeros of odd order above every height [PARITY]; regional root criteria are RH-equivalent [ROOTS]. | Regional divisibility from arithmetic. | topology, ZCG |
| **R9 Faithful approximation and recurrence** | **Open.** Index-one approximants [W1C]; target recurrence [BAG]; return transfer ⇔ RH [S3] [RETURNRH]. | Approximants or returns not inheriting `ξ`'s defect. | W1C, CTF, BAG |
| **R10 Joint structure (worlds)** | **Excluded classes.** Euler worlds (no FE) realize every abscissa in `(½, 2/3)` [EULERWORLD]; cosh models (no Dirichlet series) realize every abscissa [COSH]; prime edits with a count rate violate the seed [EDIT]; in world I an edit removes a finite top layer and gains a zero-free half-plane [WORLDI]; fake edits carry zeros with subpolynomial mean-square FE defect [WZCROW]. A decaying pointwise FE defect with unit multiplicities forces the rational primes [RIGIDITY]; positive real weights admit arbitrarily slow defects with off-line zeros [SLOWDEFECT]. | Mechanisms that use the Euler product, the exact functional equation and integrality together. | all |

## What counts as crossing a wall

A quantitative theorem must state source, signs, domain, constants and quantifier order. A construction must prove its arithmetic matching first. A no-go must state its class and its positive survivor. Three false closures are excluded by these rules: improving a ruler without a lever; solving each finite stage without a valid limit; proving the conclusion for an object that a world or fake also satisfies. Research topics and assemblies are in the [summary](obstacles-summary.md); the face structure of the routes is in the [unification ledger](route-unification-ledger.md).

<!-- source references -->
[AAL-LAYER]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/TheFailureOfTheAbscissaLawIsAFiniteLayer.lean#L33
[ACS]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/AUniformLowerBoundOnTheMarginOfTheWindowMatricesForcesTheRiemannHypothesis.lean#L505
[ADS]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/TheEternalAdSPrimeMarkedDictionary.lean#L884
[ADS-NOGO]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/CausalIdentitiesCannotForceQuarterRingdown.lean#L1600
[AVERAGE]: ../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/TheAverageRowIsBlindToTheTarget.lean#L148
[BAG]: ../../../formal/GaloisForLFunctions/RHTower/ZetaDiscRecurrenceOnEveryClosedDiscOfTheStrip.lean#L294
[CDC]: ../../../formal/GaloisForLFunctions/RHTower/XiSourceHistoryPriceEscape.lean#L140
[CENSUS]: ../../../formal/GaloisForLFunctions/IncommensurableGaborPinching/CriticalLineZeroProportion.lean#L1042
[COFACTORS]: ../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheGrowingFilterReachesPolynomiallyManyCofactors.lean#L1
[COMPLEMENT]: ../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheCriticalComplementOnTheCertifiedRatioInterval.lean#L81
[CONJCENTRAL]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ConjugationIsCentralAtAZeroIffItsOrdinateValueLiesInThePrimeTraceField.lean#L279
[CONTACT]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheConductorOfTwoGraphsIsTheirContact.lean#L22
[CONTACT-EX]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheFirstTwoPrimeContactIdeals.lean#L14
[CORRZERO]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/GrossencharacterLFunctionsHaveZerosInTheRightHalfStrip.lean#L621
[COSH]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L138
[COX]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/Probability/CoxDetectionBoundary.lean#L65
[CRITICAL-SMALL]: ../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheCompleteWeilMatrixIsPositiveAtACriticalMultiple.lean#L145
[CRITMULT]: ../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/ReceiverRate/TheCriticalOverlapIsLogLogTimesLogSquared.lean#L503
[DENSITY]: ../../../formal/GaloisForLFunctions/RHTower/PrimeShortIntervalsSeventeenThirtiethsUnconditional.lean#L25
[DIAGONAL]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheCouplingsOfAWindowAreNotMixedAreasAndTheIndexForcesLogarithmicSelfPairings.lean#L268
[DIPOLE]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheDipoleOfWeilsGreenMatrixCarriesTheFirstOverlapStep.lean#L364
[DOUBLECOLL]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheTurnAroundAnIsolatedDoubleCollisionOffTheCentreIsTheExchangeOfTwoPairs.lean#L162
[DOUBLING]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestDoublingFactorOfTheMarginIsTwoToTheWidth.lean#L217
[DOUBLINGHP]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestDoublingFactorOfTheMarginIsTwoToTheWidth.lean#L178
[ECP]: ../../../formal/GaloisForLFunctions/RHTower/Representation/EndpointCharacterCriterion.lean#L62
[EDGE]: ../../../formal/GaloisForLFunctions/FrustratedArithmeticDirichletForms/TheEdgeLawCrossesOneBetweenLogFiveAndLogSix.lean#L295
[EDIT]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L175
[ENDPOINT]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ConfiningSourceEndpointSelection.lean#L1
[EULERWORLD]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L77
[EVENLOG2]: ../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheEvenWeilFormHasAFloorAtApertureLogTwo.lean#L4126
[FLOORLOG2]: ../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheTwoPrimeWindowHasAPositiveWeilFloorAtEveryBlockSize.lean#L48
[FOURTH]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheTwoPrimeWindowAndRatioThreeHoldAtEveryBlockSize.lean#L285
[FOURTHRED]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheTwoPrimeWindowAndRatioThreeHoldAtEveryBlockSize.lean#L310
[FRAMEWORLD]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L155
[GAP]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheBoundRangeEndsOnlyWhereTheGapOfTheBoundWindowsCloses.lean#L308
[GAUSS]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/MoebiusSignedGaussPairingsEndAtThreeFifths.lean#L595
[GAUSS_INF]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/MoebiusSignedGaussPairingsEndAtThreeFifths.lean#L859
[GAUSS_UNC]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/MoebiusSignedGaussPairingsEndAtThreeFifths.lean#L586
[GROSSENTOWER]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheCubicProbeIsACoupledTowerReachingThreeFifths.lean#L1577
[GTA]: ../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaSchurQuarticSpectralDecayEquivalence.lean#L293
[HEAT-EIGHT]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ARealCollisionOfMassNotDivisibleByEightGivesEverySignedPermutation.lean#L165
[HEAT-FINITE]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheArithmeticGroupActsOnContinuedWindowsOfZerosAsHeatMonodromy.lean#L81
[HEAT-NOGO]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheArithmeticGroupIsAHeatMonodromyOnFiniteWindowsButNotOnAFibre.lean#L62
[HEAT-UNIFORM]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/AUniformSpecializationOfTheOffLineZerosForcesThemToBeFinite.lean#L29
[HEATTHR]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L162
[HF]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalHalfLineStateIsUniqueUpToSign.lean#L96
[HF-BOUNDARY]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineStateHasNoBoundaryLaplaceZero.lean#L149
[HF-CYCLIC]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineStateIsCyclic.lean#L59
[HF-OUTER]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineLaplaceMultiplierIsOuter.lean#L45
[HIDDEN]: ../../../formal/GaloisForLFunctions/WindowVisibilityLaw/ShallowClusterExclusionAndTaperedCrystalBarrier.lean#L1179
[INDEX]: ../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheFiniteStratumIsThePacketIndexDichotomy.lean#L85
[INDEXLAW]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheIndexOfTheNeutralPartIsOnePlusTheNumberOfZerosRightOfTheLine.lean#L166
[INVOLUTIONS]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheGroupActsOnAZeroThroughTheTwoInvolutionsIffItsWidthValueLiesInThePrimeTraceField.lean
[IRK]: ../../../formal/GaloisForLFunctions/RHTower/Deninger/DeningerMeyerPrimeRotationResolution.lean#L25
[JENSEN]: ../../../formal/GaloisForLFunctions/VerifiedHeightRungs/TheJensenPolynomialsThroughDegree31922AreRealRooted.lean#L21
[JETS]: ../../../formal/GaloisForLFunctions/SelbergClass/DirichletSeries/PrimeDensityArithmeticJets.lean#L121
[LANDING-TFAE]: ../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheLandingLawForZeta.lean#L145
[LEAVEQUART]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/AnOrbitLeavesItsQuartetOnlyThroughAnotherOffLineQuartetOfTheSameOrdinate.lean#L43
[LEVERTRANSPORT]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L85
[LOCAL-GLOBAL]: ../../../formal/GaloisForLFunctions/RepresentationLifting/PrimePlaneLocalSplitting.lean#L1
[LOGENERGY]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWidthIsTheRateOfTheWeilFloorInTheLogarithmicEnergy.lean#L428
[LOGENERGY0]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWidthIsTheRateOfTheWeilFloorInTheLogarithmicEnergy.lean#L441
[LOGLADDER]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheTwoPrimeWindowAndRatioThreeHoldAtEveryBlockSize.lean#L322
[MARGIN-DECAY]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/UnderTheRiemannHypothesisTheMarginOfALongWindowTendsToZero.lean#L442
[MARGIN38]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesSinksAtTheRateOfTheWidth.lean#L800
[MARGINDEPTH]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesSinksAtTheRateOfTheWidth.lean#L789
[MARGINPOLY]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesSinksAtTheRateOfTheWidth.lean#L810
[MARGINRULER]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesIsARulerAtPolynomialBlockSize.lean#L719
[MARGINSINF]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesIsARulerAtPolynomialBlockSize.lean#L741
[MC]: ../../../formal/GaloisForLFunctions/RHTower/MobiusHilbertFormEquivalence.lean#L219
[MEASURING]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L79
[MERTENS78]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L169
[MIXED]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/MixedTowersOfLeversStayAboveTheBestCentre.lean#L419
[MMD]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/QuasiRiemannHypothesis.lean#L631
[MMD_DIR]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/QuasiRiemannHypothesis.lean#L637
[MMD_HECKE]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/QuasiRiemannHypothesis.lean#L602
[MMD_STRIP]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/QuasiRiemannHypothesis.lean#L674
[NEARDIAG]: ../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheNearDiagonalCofactorsHaveASummableRow.lean#L162
[NEWMAN]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L155
[ODDLOG2]: ../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheOddWeilFormHasAFloorAtApertureLogTwo.lean#L3943
[OFFCENTRE]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ACollisionAwayFromTheCentreExistsAtAForwardTime.lean#L625
[ORBIT]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheDegreeOfTheResidueFieldOfAZeroIsTheSizeOfItsOrbit.lean#L50
[OVERLAP]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheTwoPrimeWindowAndRatioThreeHoldAtEveryBlockSize.lean#L273
[PA]: ../../../formal/GaloisForLFunctions/RHTower/PrimeArchEndpointCalibratedHausdorffRH.lean#L92
[PARITY]: ../../../formal/GaloisForLFunctions/RHTower/GlobalParityWall.lean#L1
[PBM]: ../../../formal/GaloisForLFunctions/RHTower/RegularizedLogZetaAbscissa.lean#L402
[POLAR]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/WholeSpaceCriticalThresholdEqualsPolarThreshold.lean#L256
[PRIME-FIBRES]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheFibreFieldsOverThePrimeTracesAreFiniteGaloisAndGenerateTheSpectralField.lean#L1
[QUARTET]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheOrbitOfAZeroLiesInItsQuartetIffItsWidthAndOrdinateValuesSolveAQuadraticOverThePrimeTraceField.lean#L281
[RANK-WALL]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheBindingOfTheTwoHalvesOfAWindowOfRatioFourHasRankProportionalToTheBlockSize.lean#L929
[REFLECTION]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ALiftOfTheReflectionIsConjugationExactlyWhereTheWeightLiesInThePrimeTraceField.lean#L55
[RETURNRH]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L254
[RFHM]: ../../../formal/GaloisForLFunctions/RHTower/JointAncestryAllPrimeReversibleRFHMSewingNoGo.lean#L37
[RIGIDITY]: ../../../formal/GaloisForLFunctions/EulerFETransportTheory/DecayingFunctionalEquationsDetermineThePrimes.lean#L486
[ROOTS]: ../../../formal/GaloisForLFunctions/RHTower/XiHeightAdaptiveFiniteLadderClosure.lean#L234
[RULERS]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L55
[RUNG]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheCorrectionOfTheCubicProbeCarriesTheAbscissaOfItsRung.lean#L126
[RUNG3148]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheCorrectionOfTheCubicProbeCarriesTheAbscissaOfItsRung.lean#L167
[S3]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheReturnTransferIsTheRiemannHypothesisUnderAStrip.lean#L44
[SAMPLING]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TransformsSampledOnLogarithmicallyDensePoints.lean
[SEC]: ../../../formal/GaloisForLFunctions/RHTower/TimeOneGammaJetFockRHCriterion.lean#L461
[SLOWDEFECT]: ../../../formal/GaloisForLFunctions/EulerFETransportTheory/ArbitrarilySlowDefectsOfPositiveWeightedSystems.lean#L569
[SQREL]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ASquareRelationAmongHeightRadicandsHasAnEvenNumberOfCriticalHeights.lean#L33
[SRT]: ../../../formal/GaloisForLFunctions/SurfaceOfSpecZ/ScaleLocality/PrimeLogarithmicWindows.lean#L145
[STEINBERG]: ../../../formal/GaloisForLFunctions/RHTower/Deninger/DeningerPrimeSteinbergObstruction.lean
[SUBCRITICAL]: ../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheCompleteWeilMatrixIsPositiveDefiniteBelowTheEighthRoot.lean#L166
[TH]: ../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaHermiteTraceFlag.lean#L250
[THREEATOMS]: ../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheLandingLawForZeta.lean#L68
[TREE-GAP]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/TheDilationProcessHasNoGap.lean#L174
[TRUNCATION]: ../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/FamilyContinuationRestoresTheGaussWallsUnderTruncation.lean#L1101
[TWOTHIRDSWORLD]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L92
[UPPERLOG2]: ../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheEvenWeilFormHasAFloorAtApertureLogTwo.lean#L5411
[W1C]: ../../../formal/GaloisForLFunctions/InfiniteRankPurityTheory/TheIndexIsSemicontinuous.lean#L96
[WALLGEN]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/MixedTowersOfLeversStayAboveTheBestCentre.lean#L525
[WBF]: ../../../formal/GaloisForLFunctions/HTGeometry/PaperGenealogyFredholmRecovery.lean#L50
[WD-LONG]: ../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/LongMoebiusSecondMomentRigidity.lean#L659
[WITT]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/Witt/RaynaudOperatorBoundary.lean#L19
[WL]: ../../../formal/GaloisForLFunctions/BiScaleUncertainty/WeilLagCriticalDeficitEndpointAndLimitLaw.lean#L868
[WORLDI]: ../../../formal/GaloisForLFunctions/WorldsOfTheZeroConfiguration/AFiniteLayerCanBeEditedAway.lean#L136
[WZCROW]: ../../../formal/GaloisForLFunctions/WorldsOfTheZeroConfiguration/TheWorldOneScenarioTable.lean#L72
[XN]: ../../../formal/GaloisForLFunctions/RHTower/XiNewtonDiscSourceMargin.lean#L219
