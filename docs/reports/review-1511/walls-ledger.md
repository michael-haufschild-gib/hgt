# RH wall ledger

Three families organize the closure problems; a fourth layer, selection, cuts across them. They are classes of research obligations, not equivalent propositions; a route can meet several.

| Family | Question | Typical failure |
|---|---|---|
| **P — production** | Can an arithmetic argument move the zero width `w = Θ − ½`, i.e. prove a bound the seed does not give? | A ruler of `w` is improved in form only; norms, averaging or completion erase the saving or the target. |
| **U — uniform exclusion** | Does control reach every stage (aperture, ratio, block size, degree, height, heat time, mollifier length) and every finite or shallow exceptional configuration? | A finite-stage theorem with no limit; a finite top layer or a shallow tail survives. |
| **R — faithful realization and selection** | Does the constructed object carry the arithmetic source of `ζ` — Euler product, exact functional equation, unit Euler parameters, integral primes — used together? | The mechanism also holds for a world or a deformation that has off-line zeros. |

Statuses: **Open** — no proof in the corpus; **Excluded** — a proved obstruction for a stated construction class; **Available** — a proved input. Statements read in Lean source at `3699ff3a33` with the working tree of 15 Nov 2026; [S] = tagged unintegrated by the frontier map, [W] = untracked working-tree file, [D] = deduction of this ledger. No build, compile or axiom audit underlies these labels. Evidence: [fact log](../../../logs/review-1511-frontier-facts.md); routes: [route report](route-obstacles.md).

## Organizing principles

**Measuring is not moving.** A ruler of `w` is a family `P β` with `w ≤ β ⇔ P β`. Two rulers agree reading by reading, and a map on exponents improves every reading of one ruler iff it improves every bound of `w` [MEASURING] [LEVERTRANSPORT]. Every P-wall is the single question of producing a lever or a seed for `w`, seen on a different ruler; every U-wall reduces either to a ruler at rate zero or to one of the atoms ZAL, `FiniteOffLine → RH`, Landing [THREEATOMS].

**Joint use.** A lever that bites must fail on every world that lacks one structure of `ζ`: Euler worlds lack the functional equation [EULERWORLD] [TWOTHIRDSWORLD], cosh models the Dirichlet series [COSH], prime edits the arithmetic of the rational primes beyond their count [EDIT], shifted pairs the Ramanujan bound [PAIRSNOBITE] [PAIRS] [TEMPERED]. Prime-2 deformations keep Euler product, functional equation, passivity and axis unitarity with a non-tempered gate at 2 [P2FACTOR] [ADS-NOGO]; compact Selberg zeta functions have off-line zeros exactly at their non-tempered spectrum [SMALLEIG]; a local Euler column has its zeros on the line iff it is tempered [EULERCOLUMN]. [D] Every Euler–FE countermodel in the corpus is non-tempered at some place, so the open target is a mechanism that uses the unit size of the Euler parameters together with the other three structures.

## Available inputs

| Input | Exact extent | Boundary |
|---|---|---|
| **Seed** | `ζ(s) ≠ 0` for `Re s > 7/8`; every Dirichlet `L(s,χ)`; every finite-order Hecke `L`-function and every ray class `L`-function of `ℚ(ω)`; `1/8 ≤ Re ρ ≤ 7/8` [SEEDZETA] [MMD_DIR] [HECKESEED] [RAYSEED] [S] [MMD_STRIP]; the degree-two Artin character of `ℚ(∛2)` [ARTINSEED] [S]. Written in source, hypothesis-free: the same families zero-free on `Re s > 20999/24000`, zeros of `ζ` in `[3001/24000, 20999/24000]` [SUBSEED] [SUBDIR] [SUBSTRIP] [S] | False for two-sided prime edits with count `Ax + O(x^{14/15})` [EDIT] and for shifted pairs with `a > 3/8` [PAIRSABS]. |
| **Seed on every ruler** | `w ≤ 8999/24000` written [WIDTHSUB] [S]; `Λ ≤ 9/128`; heat threshold `≤ 3/64`; `M(n) = O(n^β)`, `β > 7/8`; prefixes, unit window, long moments, signal, two-end state at rate `3/8`; slope loss `3/4`; doubling factors above `2^{3/8}`; ancestry gap law; return transfer ⇔ RH [NEWMAN] [HEATTHR] [MERTENS78] [RULERS] [SLOPE34] [DOUBLING38] [RETURNRH] | Readings of `w ≤ 3/8`. |
| **Exact rulers of `w`** | Zero abscissa, Möbius prefix at one height, unit window, zeros of `M_X`, signal, two-end state [RULERS] [WD] [SIGNAL-WIDTH]; Weil floor in the logarithmic energy [LOGENERGY]; margin at polynomial block size [MARGINRULER] [MARGINSINF]; doubling factor (best `2^w`) [DOUBLING]; slope loss of the long moments (least `2w`) [SLOPE]; squarefree quotient on `[½, 9/16)` [SQFRULER]; cubic-probe correction `(3 + Θ_rung)/6` [RUNG]; WL, WD-long, SRT, PBM dictionaries [WL] [WD-LONG] [SRT] [PBM]; AdS strip [ADS] | A ruler reads `w`; it produces nothing. |
| **Margin depth** | Every window of ratio `3K+1` has at most one eigenvalue below `−C(1+log K)²K^{3/8}(1+log R)` [MARGIN38]; `C K^{3/8+ε}` at polynomial block size [MARGINPOLY]; an `O(√K)` shift removes every negative square of every bounded-weight window [SHIFTKILL] [S] | The factor `1 + log R` is clustering at the resolved height (U9). |
| **Jensen rung** | Real-rooted through degree `31922` [JENSEN]; `N_d ≤ 300√(d log d)` for `log d ≥ 6.1·10⁶` [JENSENBOUND] | Finite degree. |
| **Two-prime window** | Floors `10⁻¹³` (even), `10⁻¹⁰` (odd) on `[−log 2, log 2]` [EVENLOG2] [ODDLOG2] [FLOORLOG2] [S]; ladder `≤ 3` (`Q ≥ 2`), `< 4` (`Q ≥ 3`) [LOGLADDER] [S] | A prime-2 deformation with off-line zeros also passes `log 2` [P2LOG2] [S]; `Q = 2` fourth step open [FOURTHRED] [S]. |
| **Full-space critical arithmetic** | `c⁻⁷` floor below `1/8`; one critical multiple [SUBCRITICAL] [CRITICAL-SMALL] | Every bounded multiple is RH [CRITMULT]. |
| **Index law** | `r ≤ 1 + κ` negative squares attained [INDEXLAW]; packet index `= κ` [INDEX] | Counts zeros; excludes none. |
| **Half-line thermodynamics** | RH ⇔ bare energy `≥ 0` ⇔ Legendre intercept `≥ 0` [HPEQUIV] [S]; off RH: Hawking–Page transition at `W₀` [HPTRANS] [S]; state unique, outer, cyclic, Laplace zero-free, Hessian-stable [HF] [HF-OUTER] [HF-CYCLIC] [HF-BOUNDARY] [SADDLE] [S] | The sign of the bare energy. |
| **Heat and monodromy** | Finite arithmetic actions are heat monodromies [HEAT-FINITE]; off-centre forward collision [OFFCENTRE]; unit gap of `N(t)` near `0` ⇔ RH direction [HEATUNIT] | Whole fibres excluded [HEAT-NOGO]; sign of `G₊` open. |
| **Zero fields** | Finite Galois layers; orbit degree; quartet, width, ordinate criteria; conjugation central iff ordinate values in `B` [PRIME-FIBRES] [ORBIT] [QUARTET] [CONJCENTRAL]; isolated off-line quartet: radicand negative at every prime, partial-flip criterion, Klein action at a shared critical ordinate [REGIMEA] [PARTIALFLIP] [KLEIN] | No restriction on the position of conjugation. |
| **Exceptional layers** | Finite top layer [AAL-LAYER]; finite oscillation off AAL, non-attainment receivers [FINOSC] [NONATTAIN] [UNITGAPAAL]; cofactors [COFACTORS] [NEARDIAG] | Prime-weighted cofactor cancellation (P6). |
| **Census** | Simple critical `≥ 0.67250071` [CENSUS]; positive odd-multiplicity proportion [ODDPROP]; five-runs [FIVERUN]; density `30/13` [DENSITY] | Proportions leave every finite configuration. |

## P — production

| Wall | Status and exact obstruction | Surviving target | Routes |
|---|---|---|---|
| **P1 Critical cancellation** | **Open.** Every growth route is a ruler or receiver of `w` [RULERS] [MC] [WL] [WD-LONG] [PBM] [SLOPE]. | A signed estimate on a literal `μ/Λ` observable beyond the seed (P8, P9). | MC, WL, FU, CFC, RP, SQF, TT, CHMD, LI, PBM, RB, WD, JAS, AIP, SZ |
| **P2 Gauss completion** | **Excluded class.** Completed Möbius-signed Gauss pairings: uncoupled boundary `≥ 2/3`, coupled `≥ 3/5` [GAUSS] [GAUSS_UNC]; mixed towers, composites, minima `≥ 3/5` [MIXED] [WALLGEN]. The wall is the meeting point of the completion cost `c ≥ 2k/3 − 1` [PRICE] and the sign line `c = k/2`: the Möbius sign costs `½` at some place, short monomials pay exactly `k/2`, and towers on the sign line have values in `(½, K/(2(K−1))]` [SIGNCOST] [SIGNPRICE] [SIGNLINE] [SIGNWALL] [PRICEABOVE]. | A joint completion priced on the sign line at period `k ≥ 7`. | MC, JAS, producer |
| **P3 Truncated family continuation** | **Open signed problem; excluded absolute repair.** Truncations `L ≥ 3` keep correction zeros in `7/12 ≤ Re s < 2/3`; absolute sixth-power tails cost `≥ cZ^{2/3}` [TRUNCATION]; correction zeros = rung zeros at `6s − 3`, `Θ_corr = (3 + Θ_rung)/6` [CORRZERO] [RUNG] [RUNG3148]; the coupled tower reaches `3/5` only with per-level estimates [GROSSENTOWER]. | Target-preserving signed cancellation across continued rows. | producer, MC, JAS |
| **P4 Phase/target loss** | **Excluded averaging; survivor.** The six-phase mean kills the target mode [AVERAGE]; nonprincipal filters recover it, the minimum-energy filter is unique with explicit cost, and finite Euler products are reconstructed [TARGETFILTER] [ROWTARGET] [MINFILTER] [S]; each completed row cancels to square-root size on one modulus after the target is removed [ROWCANCEL] [S]. | Cancellation across rows (long weighted rows). | MC, JAS, WBF |
| **P5 Complete signed payment** | **Open; a ruler.** Log-energy floor at rate `β` ⇔ `w ≤ β`; rate `0` ⇔ RH [LOGENERGY] [LOGENERGY0]. | `w = 0` on this ruler. | RW, HF, EWU, OWU, ACT, AIP, HAT-C, SZ, RN, SC, ACS |
| **P6 Restricted cofactor cancellation** | **Open.** Filters and near-diagonal rows are controlled; the prime-weighted restricted aggregate is not [COFACTORS] [NEARDIAG]. | Beat the isolated top residue. | AAL, BAG, ZCG |
| **P7 Higher source constraints** | **Open.** Flags, quartic charge, character Grams [TH] [PA] [GTA] [ECP]; formal jet independence gives no inequality [JETS]. | A higher-order source estimate. | TH, PA, GTA, ECP, HCF |
| **P8 Lever existence** | **Open; five excluded classes.** No lever proved for `ζ`. Valid on Euler worlds ⇒ no bite below `2/3` [TWOTHIRDSWORLD]; on cosh models ⇒ no bite [COSH]; on shifted pairs ⇒ no bite in `[Θ, Θ + ½)` [PAIRSNOBITE] [PAIRS]; frames with centre `< 2/3` fail on some world [FRAMEWORLD]; the seed fails on edits [EDIT]. | A lever whose proof uses Dirichlet series, functional equation and unit Euler parameters together. | all W-routes |
| **P9 Estimate ladder** | **Open; one excluded class.** The published budget is a vertex at `7/8` [VERTEXPOS]; the rescaled geometry closes at `20999/24000` [SUBPROBE] [SUBSEED] [S], and the true vertex of this estimate system lies in `(40535/46328, 20999/24000]` [TRUEVERTEX] [FARKAS] [S]; design floor `13/15`, reached with the count `U^{1−δ}` in every bin [VERTEXFLOOR] [BALANCED]; Cauchy–Schwarz floor `5/6`, a pre-Cauchy–Schwarz saving `s` gives `5/6 − s` [SAVING] [LOWBARRIER]; low estimates through the twists return the zero, the high-side count moves by `< 10⁻⁴` with the zero top [TWISTRETURN] [ROWCOUNTAT] — bootstrapping the probe gives no lever [D]. Excluded: rank-two `A₂` multiple Dirichlet series (convexity, Perron, Kubota pole, squared rows) [A2CHAIN] [A2REJECT] [A2DOUBLE]. | The count `U^{1−δ}`; a pre-Cauchy–Schwarz saving. | producer, all W-routes |
| **P10 Window producer** | **Excluded in gluing form.** Every bounded-weight model has the doubling factor `√2` [SQRT2] [S]; a sub-Euler model equal to the true window up to any certified cutoff, on every dyadic middle and on both half-windows has best factor exactly `√2` [SUBEULER] [S]; contacts `k ≥ 3K+2` act only on the end-to-end block [TOPLOCAL] [S]; a factor below `√2` forces a fresh-octave form `< −(√K/4000)‖v‖²` [TOPOCTAVE] [S]. | The fresh-octave form, a prime sum over `(3K, 6K]` — a reading of `w` [D]. | ACS, RW, HF |
| **P11 Identity forcing** | **Excluded class.** An off-line zero forces exactly its quartet [QUARTETFORCE]; Witt monomials keep the order of `ζ` at `Re ρ > ½` [WITTORD]; Brauer relations cancel `ζ` [BRAUERCANCEL]; shifted convolutions keep a margin `≥ 9/16` [SHIFTMARGIN]; a coincidence `ζ(ρ) = ζ(ρ/k) = 0` forces `Θ ≥ k/(k+1)` [ROOTCOINC] [S], halving pairs `Θ ≥ 2/3` [HALVING]; with the written seed no coincidence occurs for `k ≥ 7` [K7] [S]; `ζ(2s)/ζ(s)` is a ruler [EULERDOUBLING] [S]. Survivor: the squarefree ruler on `[½, 9/16)` [SQFRULER], `[½, 27001/48000)` with the written seed [SQFRULER2] [S]. | A forcing law without coincidence, outside rational Euler identities. | SQF, ZCG, Galois |

## U — uniform exclusion

| Wall | Status and exact obstruction | Surviving target | Routes |
|---|---|---|---|
| **U1 All stages** | **Open.** Degree `31922`, aperture `log 2`, ladder depth four, one critical multiple are finite stages [JENSEN] [FLOORLOG2] [FOURTH] [CRITICAL-SMALL]. A finite aperture does not separate `ζ` from prime-2 deformations: every deformation keeps the floor at `½log 2`, and those near `α = ½` stay positive at `log 2` [P2NYQ] [P2LOG2] [S]; each has finite onset aperture [P2ONSET] [S]. A zero of depth `1/a` can hide from aperture `a` above height `e^{4a}` [HIDDEN]. | A stage map with contraction on a ruler, or an atom. | LA, HCF, TH, RW, SRT, HF, ACS, EWU, OWU |
| **U2 Long-moment quantifiers** | **Exact ruler.** Least slope loss of `θ ↦ 2θ` is `2w`; loss `3/4` holds [SLOPE] [SLOPE34]; one `K` for unbounded `θ` [WD-LONG]. | Loss `< 3/4` (a better seed); loss `0` (RH). | WD, MC |
| **U3 Finite stratum** | **Open.** Packet index = number of right zeros; `FiniteOffLine → RH` iff that index is `0` or `∞` [INDEX]. The only Euler–FE world with a finite off-line set is archimedean non-tempered [SMALLEIG]. | Exclude finite positive `κ` for `ζ`. | AAL, ACS, ZCG, BAG, PM, W1C |
| **U4 Landing and tail** | **Open.** RH ⇔ ZAL ∧ `FiniteOffLine → RH` ∧ Landing [THREEATOMS]; Landing ⇔ bounded Hadamard threshold as `σ ↓ ½` [LANDING-TFAE]; off AAL the prime error is a finite oscillation attained on every late window [FINOSC]; AAL ⇔ every line has `≤ 1` or infinitely many zeros to its right [UNITGAPAAL]. | The atoms separately; window non-attainment [NONATTAIN]. | AAL, ZCG, BAG, SRT, JAS, SC |
| **U5 Critical state** | **Exact; exclusion open.** RH ⇔ bare energy `≥ 0` [HPEQUIV] [S]; off RH a unique Hawking–Page point `W₀` [HPTRANS] [S]. Excluded as exclusion mechanisms: stability, outerness, cyclicity, transverse gap, zero-pressure endpoint competition [SADDLE] [TRANSGAP] [OUTERALL] [WEAKEND] [S]. | An arithmetic property of the bare energy that prime-2 deformations lack. | HF, RW, ACS |
| **U6 Heat time zero and monodromy** | **Open.** Uniform injective continuation forces finite off-line support [HEAT-UNIFORM]; proper `G₊` forces `8 | N(t)` [HEAT-EIGHT]; one isolated off-centre double collision gives `G₊ = W` [DOUBLECOLL]. Excluded: a heat ruler in the width alone [HEATSPACING]. | Decide `G₊`; a heat law using the zero density. | ZCG, LA, PTR |
| **U7 Uniform margin** | **Exact reading.** Bounded margin ⇔ RH [ACS]; doubling factor one ⇔ RH [DOUBLINGONE]; levels are bounded or the margin law fails at a positive rate [LOSSDICHOT]; dilation process has no gap [TREE-GAP]; under RH long-window margins tend to zero [MARGIN-DECAY]. | A gap on bound windows [GAP]. | ACS, RW, HF, SRT |
| **U8 Detection versus exclusion** | **Open.** Cox detection nonuniform [COX]; Fock, dark-history, Newton criteria keep global inputs [SEC] [CDC] [XN]. | Uniform control with a residual gap. | SEC, CDC, XN |
| **U9 Clustering at the resolved height** | **Open.** Margin converse with `1 + log R` at all block sizes, exact only at polynomial block size [MARGINDEPTH] [MARGINPOLY]; mass-normalized floor is a half ruler because a unit window may carry `C log T` zeros [SAMPLING]. | A height-uniform bound on deep off-line zeros per unit window. | ACS, RW, SRT, HF |

## R — faithful realization and selection

| Wall | Status and exact obstruction | Surviving target | Routes |
|---|---|---|---|
| **R1 Global arithmetic geometry** | **Open.** Contact conductors, negative diagonals, logarithmic self-pairings, Witt mask [CONTACT] [CONTACT-EX] [DIAGONAL] [WITT]; Kummer calibration has the Hasse–Weil maximal count [KUMMERMAX] [S]. | Intersection theory with the actual diagonal and an index theorem. | ACS, F₁, HF, PM |
| **R2 Finite-rank gluing** | **Excluded class.** Rank-`r` lowered models at ratio four have index `≥ 2` for `600(r+1) ≤ H` [RANK-WALL]; no contact-sign-blind bound proves the first step [DIPOLE]. | Growing-rank signed coupling. | ACS, RW, HF |
| **R3 Arithmetic/heat identification** | **Excluded comparisons.** No whole-fibre intertwiner [HEAT-NOGO]. | Finite windows with controlled losses. | ZCG, LA, Galois |
| **R4 Galois purity** | **Open.** `Re ρ = ½` iff `p^{2Re ρ} ∈ B` and an automorphism realizes the reflection [REFLECTION]; orbits leave quartets only through same-ordinate off-line quartets [LEAVEQUART]; square relations carry an even number of critical heights [SQREL]; isolated quartets: negative radicand, partial-flip criterion [REGIMEA] [PARTIALFLIP]. | A relation in `B` restricting conjugation. | ZCG, LA, Galois |
| **R5 Physical axioms** | **Excluded inference.** Causal, Euler, FE, passive, axis-unitary prime-2 deformations have decay thresholds `→ 0` [ADS-NOGO] and pass the certified aperture [P2LOG2] [S]. | A principle that sees the non-tempered gate. | PM |
| **R6 Local versus global** | **Open; counterexamples to promotion.** Cyclic-local splitting without global splitting [LOCAL-GLOBAL]; finite resolutions [IRK]; regulator kernel and cyclic classes [REGULATOR] [CYCLICSOURCE]. | Global descent for the actual source. | IRK, MSC, ACS |
| **R7 Reversible sewing** | **Excluded class** [RFHM]. | Nonreversible carrier. | RFHM, JAS |
| **R8 Global roots and parity** | **Excluded global target.** `ξ` has critical zeros of odd order above every height [PARITY]; regional root criteria are RH [ROOTS]. | Regional divisibility. | topology, ZCG |
| **R9 Faithful approximation** | **Open.** Index-one approximants [W1C]; index-one realization [INDEXONE]; target recurrence [BAG]; return transfer ⇔ RH [RETURNRH]. | Approximants not inheriting the defect. | W1C, CTF, BAG |
| **R10 Worlds** | **Excluded classes.** Euler worlds [EULERWORLD], cosh models [COSH], prime edits [EDIT], shifted pairs [PAIRSABS], world-I edits [WORLDI]; fake-edit FE defects do not decay [EDITDEFECT], and a decaying defect with unit multiplicities forces the rational primes [RIGIDITY]; positive real weights allow slow defects [SLOWDEFECT]. | Mechanisms using all structures of `ζ`. | all |
| **R11 Temperedness** | **Open target; every corpus countermodel violates it [D].** Shifted pairs (finite places) [TEMPERED], prime-2 deformations (place 2) [P2FACTOR], compact Selberg zeta (archimedean place) [SMALLEIG]; a single Euler column is pure iff tempered [EULERCOLUMN]. | A zero-location statement whose proof uses unit Euler parameters. | all |

## What counts as crossing a wall

A quantitative theorem states source, signs, domain, constants and quantifier order. A construction proves its arithmetic matching first. A no-go states its class and its positive survivor. Three false closures are excluded: improving a ruler without a lever; solving each finite stage without a valid limit; proving the conclusion for an object that a world, a deformation or a non-tempered countermodel also satisfies. Research topics and assemblies: [summary](obstacles-summary.md); faces: [unification ledger](route-unification-ledger.md).

<!-- source references -->
[A2CHAIN]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheRankTwoMultipleDirichletSeriesConvexityHull.lean#L504
[A2DOUBLE]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheRankTwoMultipleDirichletSeriesConvexityHull.lean#L779
[A2REJECT]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheRankTwoMultipleDirichletSeriesConvexityHull.lean#L696
[AAL-LAYER]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/TheFailureOfTheAbscissaLawIsAFiniteLayer.lean#L33
[ACS]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/AUniformLowerBoundOnTheMarginOfTheWindowMatricesForcesTheRiemannHypothesis.lean#L505
[ADS]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/TheEternalAdSPrimeMarkedDictionary.lean#L884
[ADS-NOGO]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/CausalIdentitiesCannotForceQuarterRingdown.lean#L1600
[ARTINSEED]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheArtinFunctionOfTheCubeRootsOfTwoCarriesTheSeed.lean#L147
[AVERAGE]: ../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/TheAverageRowIsBlindToTheTarget.lean#L148
[BAG]: ../../../formal/GaloisForLFunctions/RHTower/ZetaDiscRecurrenceOnEveryClosedDiscOfTheStrip.lean#L294
[BALANCED]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSevenEighthsGeometryIsAVertex.lean#L541
[BRAUERCANCEL]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/WittMonomialsShiftedConvolutionsAndBrauerCancellation.lean#L497
[CDC]: ../../../formal/GaloisForLFunctions/RHTower/XiSourceHistoryPriceEscape.lean#L140
[CENSUS]: ../../../formal/GaloisForLFunctions/IncommensurableGaborPinching/CriticalLineZeroProportion.lean#L1042
[COFACTORS]: ../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheGrowingFilterReachesPolynomiallyManyCofactors.lean#L1
[CONJCENTRAL]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ConjugationIsCentralAtAZeroIffItsOrdinateValueLiesInThePrimeTraceField.lean#L279
[CONTACT]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheConductorOfTwoGraphsIsTheirContact.lean#L22
[CONTACT-EX]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheFirstTwoPrimeContactIdeals.lean#L14
[CORRZERO]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/GrossencharacterLFunctionsHaveZerosInTheRightHalfStrip.lean#L621
[COSH]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L142
[COX]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/Probability/CoxDetectionBoundary.lean#L65
[CRITICAL-SMALL]: ../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheCompleteWeilMatrixIsPositiveAtACriticalMultiple.lean#L145
[CRITMULT]: ../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/ReceiverRate/TheCriticalOverlapIsLogLogTimesLogSquared.lean#L503
[CYCLICSOURCE]: ../../../formal/GaloisForLFunctions/RHTower/Deninger/DeningerCyclicSourceClasses.lean
[DENSITY]: ../../../formal/GaloisForLFunctions/RHTower/PrimeShortIntervalsSeventeenThirtiethsUnconditional.lean#L25
[DIAGONAL]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheCouplingsOfAWindowAreNotMixedAreasAndTheIndexForcesLogarithmicSelfPairings.lean#L268
[DIPOLE]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheDipoleOfWeilsGreenMatrixCarriesTheFirstOverlapStep.lean#L364
[DOUBLECOLL]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheTurnAroundAnIsolatedDoubleCollisionOffTheCentreIsTheExchangeOfTwoPairs.lean#L162
[DOUBLING]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestDoublingFactorOfTheMarginIsTwoToTheWidth.lean#L217
[DOUBLING38]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestDoublingFactorOfTheMarginIsTwoToTheWidth.lean#L191
[DOUBLINGONE]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheLossOfTheMarginIsBoundedOrPolynomial.lean#L81
[ECP]: ../../../formal/GaloisForLFunctions/RHTower/Representation/EndpointCharacterCriterion.lean#L62
[EDIT]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L186
[EDITDEFECT]: ../../../formal/GaloisForLFunctions/WorldsOfTheZeroConfiguration/TheWorldOneScenarioTable.lean#L38
[EULERCOLUMN]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/RamanujanIsRealityOfAnEulerColumn.lean#L91
[EULERDOUBLING]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/EulerDilationAndRootCoincidenceExclusion.lean#L144
[EULERWORLD]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L81
[EVENLOG2]: ../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheEvenWeilFormHasAFloorAtApertureLogTwo.lean#L4149
[FARKAS]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheTrueVertexBelowSevenEighths.lean#L328
[FINOSC]: ../../../formal/GaloisForLFunctions/FloorFreeArithmetic/ThePrimeNumberTheoremIsNotAttainedOnWindows.lean#L68
[FIVERUN]: ../../../formal/GaloisForLFunctions/IncommensurableGaborPinching/ConsecutiveSimpleCriticalZeros.lean#L350
[FLOORLOG2]: ../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheTwoPrimeWindowHasAPositiveWeilFloorAtEveryBlockSize.lean#L48
[FOURTH]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheTwoPrimeWindowAndRatioThreeHoldAtEveryBlockSize.lean#L285
[FOURTHRED]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheTwoPrimeWindowAndRatioThreeHoldAtEveryBlockSize.lean#L310
[FRAMEWORLD]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L166
[GAP]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheBoundRangeEndsOnlyWhereTheGapOfTheBoundWindowsCloses.lean#L308
[GAUSS]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/MoebiusSignedGaussPairingsEndAtThreeFifths.lean#L595
[GROSSENTOWER]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheCubicProbeIsACoupledTowerReachingThreeFifths.lean#L1577
[GTA]: ../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaSchurQuarticSpectralDecayEquivalence.lean#L293
[HALVING]: ../../../formal/GaloisForLFunctions/ArithmeticHolographyOfTheModularHorizon/HalvingDescentAndShimuraZeros.lean#L40
[HEAT-EIGHT]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ARealCollisionOfMassNotDivisibleByEightGivesEverySignedPermutation.lean#L165
[HEAT-FINITE]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheArithmeticGroupActsOnContinuedWindowsOfZerosAsHeatMonodromy.lean#L81
[HEAT-NOGO]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheArithmeticGroupIsAHeatMonodromyOnFiniteWindowsButNotOnAFibre.lean#L62
[HEAT-UNIFORM]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/AUniformSpecializationOfTheOffLineZerosForcesThemToBeFinite.lean#L29
[HEATSPACING]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheHeatTimeIsTheWidthTimesTheSpacing.lean#L109
[HEATTHR]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L162
[HEATUNIT]: ../../../formal/GaloisForLFunctions/FloorFreeArithmetic/TheHeatFlowHasTheCountOfItsLimit.lean#L60
[HECKESEED]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/QuasiRiemannHypothesis.lean#L602
[HF]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalHalfLineStateIsUniqueUpToSign.lean#L96
[HF-BOUNDARY]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineStateHasNoBoundaryLaplaceZero.lean#L149
[HF-CYCLIC]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineStateIsCyclic.lean#L59
[HF-OUTER]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineLaplaceMultiplierIsOuter.lean#L45
[HIDDEN]: ../../../formal/GaloisForLFunctions/WindowVisibilityLaw/ShallowClusterExclusionAndTaperedCrystalBarrier.lean#L1179
[HPEQUIV]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ArithmeticHawkingPagePhaseStructure.lean#L352
[HPTRANS]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ArithmeticHawkingPagePhaseStructure.lean#L440
[INDEX]: ../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheFiniteStratumIsThePacketIndexDichotomy.lean#L85
[INDEXLAW]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheIndexOfTheNeutralPartIsOnePlusTheNumberOfZerosRightOfTheLine.lean#L166
[INDEXONE]: ../../../formal/GaloisForLFunctions/FloorFreeArithmetic/AnIndexOneRealizationIsAUnitGap.lean#L93
[IRK]: ../../../formal/GaloisForLFunctions/RHTower/Deninger/DeningerMeyerPrimeRotationResolution.lean#L25
[JENSEN]: ../../../formal/GaloisForLFunctions/VerifiedHeightRungs/TheJensenPolynomialsThroughDegree31922AreRealRooted.lean#L21
[JENSENBOUND]: ../../../formal/GaloisForLFunctions/FiniteFreeProbability/NonRealJensenCountBound.lean#L674
[JETS]: ../../../formal/GaloisForLFunctions/SelbergClass/DirichletSeries/PrimeDensityArithmeticJets.lean#L121
[K7]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/EulerDilationAndRootCoincidenceExclusion.lean#L212
[KLEIN]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/GaloisClosureAndMixedTracesOfAnIsolatedQuartet.lean#L445
[KUMMERMAX]: ../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/FunctionField/KummerMaximalCount.lean
[LANDING-TFAE]: ../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheLandingLawForZeta.lean#L145
[LEAVEQUART]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/AnOrbitLeavesItsQuartetOnlyThroughAnotherOffLineQuartetOfTheSameOrdinate.lean#L43
[LEVERTRANSPORT]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L85
[LOCAL-GLOBAL]: ../../../formal/GaloisForLFunctions/RepresentationLifting/PrimePlaneLocalSplitting.lean#L1
[LOGENERGY]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWidthIsTheRateOfTheWeilFloorInTheLogarithmicEnergy.lean#L428
[LOGENERGY0]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWidthIsTheRateOfTheWeilFloorInTheLogarithmicEnergy.lean#L441
[LOGLADDER]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheTwoPrimeWindowAndRatioThreeHoldAtEveryBlockSize.lean#L322
[LOSSDICHOT]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheLossOfTheMarginIsBoundedOrPolynomial.lean#L106
[LOWBARRIER]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSevenEighthsGeometryIsAVertex.lean#L802
[MARGIN-DECAY]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/UnderTheRiemannHypothesisTheMarginOfALongWindowTendsToZero.lean#L442
[MARGIN38]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesSinksAtTheRateOfTheWidth.lean#L800
[MARGINDEPTH]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesSinksAtTheRateOfTheWidth.lean#L789
[MARGINPOLY]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesSinksAtTheRateOfTheWidth.lean#L810
[MARGINRULER]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesIsARulerAtPolynomialBlockSize.lean#L782
[MARGINSINF]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesIsARulerAtPolynomialBlockSize.lean#L804
[MC]: ../../../formal/GaloisForLFunctions/RHTower/MobiusHilbertFormEquivalence.lean#L219
[MEASURING]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L79
[MERTENS78]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L169
[MINFILTER]: ../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/PhaseExtraction/MinimumTargetWeights.lean#L229
[MIXED]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/MixedTowersOfLeversStayAboveTheBestCentre.lean#L419
[NEARDIAG]: ../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheNearDiagonalCofactorsHaveASummableRow.lean#L162
[NEWMAN]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L155
[NONATTAIN]: ../../../formal/GaloisForLFunctions/FloorFreeArithmetic/ThePrimeNumberTheoremIsNotAttainedOnWindows.lean#L151
[ODDLOG2]: ../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheOddWeilFormHasAFloorAtApertureLogTwo.lean#L3966
[ODDPROP]: ../../../formal/GaloisForLFunctions/MultiscaleMollifiedZetaField/TheTwistedMomentGivesAPositiveCriticalProportion.lean#L109
[OFFCENTRE]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ACollisionAwayFromTheCentreExistsAtAForwardTime.lean#L625
[ORBIT]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheDegreeOfTheResidueFieldOfAZeroIsTheSizeOfItsOrbit.lean#L50
[OUTERALL]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ConfiningMinimizerOuterAndCyclic.lean#L299
[P2FACTOR]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/CausalIdentitiesCannotForceQuarterRingdown.lean#L95
[P2LOG2]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/PrimeTwoDeformedApertureLogTwoTest.lean#L278
[P2NYQ]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/PrimeTwoDeformedApertureLogTwoTest.lean#L169
[P2ONSET]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/PrimeTwoDeformedApertureLogTwoTest.lean#L196
[PA]: ../../../formal/GaloisForLFunctions/RHTower/PrimeArchEndpointCalibratedHausdorffRH.lean#L92
[PAIRS]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L295
[PAIRSABS]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L259
[PAIRSNOBITE]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L267
[PARITY]: ../../../formal/GaloisForLFunctions/RHTower/GlobalParityWall.lean#L1
[PARTIALFLIP]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/GaloisClosureAndMixedTracesOfAnIsolatedQuartet.lean#L308
[PBM]: ../../../formal/GaloisForLFunctions/RHTower/RegularizedLogZetaAbscissa.lean#L402
[PRICE]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/MoebiusSignedGaussPairingsEndAtThreeFifths.lean#L383
[PRICEABOVE]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheGaussPairingsArePricedAboveTheSign.lean#L126
[PRIME-FIBRES]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheFibreFieldsOverThePrimeTracesAreFiniteGaloisAndGenerateTheSpectralField.lean#L1
[QUARTET]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheOrbitOfAZeroLiesInItsQuartetIffItsWidthAndOrdinateValuesSolveAQuadraticOverThePrimeTraceField.lean#L281
[QUARTETFORCE]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/TheClosedConfigurationsOfHalvingAndDoubling.lean#L120
[RANK-WALL]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheBindingOfTheTwoHalvesOfAWindowOfRatioFourHasRankProportionalToTheBlockSize.lean#L929
[RAYSEED]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRayClassFunctionOfTheEisensteinFieldCarriesTheSeed.lean#L130
[REFLECTION]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ALiftOfTheReflectionIsConjugationExactlyWhereTheWeightLiesInThePrimeTraceField.lean#L55
[REGIMEA]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/GaloisClosureAndMixedTracesOfAnIsolatedQuartet.lean#L247
[REGULATOR]: ../../../formal/GaloisForLFunctions/RHTower/Deninger/DeningerRegulatorKernel.lean
[RETURNRH]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L254
[RFHM]: ../../../formal/GaloisForLFunctions/RHTower/JointAncestryAllPrimeReversibleRFHMSewingNoGo.lean#L37
[RIGIDITY]: ../../../formal/GaloisForLFunctions/EulerFETransportTheory/DecayingFunctionalEquationsDetermineThePrimes.lean#L486
[ROOTCOINC]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/EulerDilationAndRootCoincidenceExclusion.lean#L174
[ROOTS]: ../../../formal/GaloisForLFunctions/RHTower/XiHeightAdaptiveFiniteLadderClosure.lean#L234
[ROWCANCEL]: ../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/PhaseExtraction/SmoothArithmeticRowCancellation.lean#L214
[ROWCOUNTAT]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSevenEighthsGeometryIsAVertex.lean#L436
[ROWTARGET]: ../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/PhaseExtraction/TheNonprincipalRowRetainsTheTarget.lean#L46
[RULERS]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L55
[RUNG]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheCorrectionOfTheCubicProbeCarriesTheAbscissaOfItsRung.lean#L126
[RUNG3148]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheCorrectionOfTheCubicProbeCarriesTheAbscissaOfItsRung.lean#L167
[SADDLE]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ArithmeticHawkingPagePhaseStructure.lean#L660
[SAMPLING]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TransformsSampledOnLogarithmicallyDensePoints.lean
[SAVING]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheRankTwoMultipleDirichletSeriesConvexityHull.lean#L830
[SEC]: ../../../formal/GaloisForLFunctions/RHTower/TimeOneGammaJetFockRHCriterion.lean#L461
[SEEDZETA]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/QuasiRiemannHypothesis.lean#L631
[SHIFTKILL]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheFloorGraphNormAndTopOctaveBlindnessOfWindowGluing.lean#L542
[SHIFTMARGIN]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/WittMonomialsShiftedConvolutionsAndBrauerCancellation.lean#L426
[SIGNAL-WIDTH]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSignalExponentIsTheZeroAbscissa.lean#L212
[SIGNCOST]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMoebiusSignCostsHalfAUnitAtSomePlace.lean#L188
[SIGNLINE]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheShortMoebiusMonomialsPayExactlyHalf.lean#L139
[SIGNPRICE]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheShortMoebiusMonomialsPayExactlyHalf.lean#L97
[SIGNWALL]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheShortMoebiusMonomialsPayExactlyHalf.lean#L157
[SLOPE]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestSlopeLossOfTheLongMomentsIsTwiceTheWidth.lean#L110
[SLOPE34]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestSlopeLossOfTheLongMomentsIsTwiceTheWidth.lean#L95
[SLOWDEFECT]: ../../../formal/GaloisForLFunctions/EulerFETransportTheory/ArbitrarilySlowDefectsOfPositiveWeightedSystems.lean#L569
[SMALLEIG]: ../../../formal/GaloisForLFunctions/CompactHyperbolicSurfaces/SmallEigenvalueZeta.lean#L25
[SQFRULER]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/WittMonomialsShiftedConvolutionsAndBrauerCancellation.lean#L268
[SQFRULER2]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/EulerDilationAndRootCoincidenceExclusion.lean#L309
[SQREL]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ASquareRelationAmongHeightRadicandsHasAnEvenNumberOfCriticalHeights.lean#L33
[SQRT2]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L149
[SRT]: ../../../formal/GaloisForLFunctions/SurfaceOfSpecZ/ScaleLocality/PrimeLogarithmicWindows.lean#L145
[SUBCRITICAL]: ../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheCompleteWeilMatrixIsPositiveDefiniteBelowTheEighthRoot.lean#L166
[SUBDIR]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/SubSevenEighthsZeroFreeHalfPlane.lean#L141
[SUBEULER]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L319
[SUBPROBE]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/SubSevenEighthsHighTransport.lean#L1231
[SUBSEED]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/SubSevenEighthsZeroFreeHalfPlane.lean#L147
[SUBSTRIP]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/SubSevenEighthsZeroFreeHalfPlane.lean#L180
[TARGETFILTER]: ../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/TheNonprincipalFilterRecoversTheTarget.lean#L161
[TEMPERED]: ../../../formal/GaloisForLFunctions/RHTower/NonTemperedShiftedZetaPairCountermodel.lean
[TH]: ../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaHermiteTraceFlag.lean#L250
[THREEATOMS]: ../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheLandingLawForZeta.lean#L68
[TOPLOCAL]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheFloorGraphNormAndTopOctaveBlindnessOfWindowGluing.lean#L650
[TOPOCTAVE]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L663
[TRANSGAP]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ConfiningGlobalTransverseGapAndResponse.lean#L284
[TREE-GAP]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/TheDilationProcessHasNoGap.lean#L174
[TRUEVERTEX]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheTrueVertexBelowSevenEighths.lean#L109
[TRUNCATION]: ../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/FamilyContinuationRestoresTheGaussWallsUnderTruncation.lean#L1101
[TWISTRETURN]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSevenEighthsGeometryIsAVertex.lean#L780
[TWOTHIRDSWORLD]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L95
[UNITGAPAAL]: ../../../formal/GaloisForLFunctions/FloorFreeArithmetic/NonAttainmentGivesTheAbscissaLaw.lean#L117
[VERTEXFLOOR]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSevenEighthsGeometryIsAVertex.lean#L499
[VERTEXPOS]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSevenEighthsGeometryIsAVertex.lean#L333
[W1C]: ../../../formal/GaloisForLFunctions/InfiniteRankPurityTheory/TheIndexIsSemicontinuous.lean#L96
[WALLGEN]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/MixedTowersOfLeversStayAboveTheBestCentre.lean#L525
[WD]: ../../../formal/GaloisForLFunctions/MultiscaleMollifiedZetaField/TheWidthIsReadInOneWindow.lean#L85
[WD-LONG]: ../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/LongMoebiusSecondMomentRigidity.lean#L659
[WEAKEND]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ArithmeticHawkingPagePhaseStructure.lean#L182
[WIDTHSUB]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/EulerDilationAndRootCoincidenceExclusion.lean#L60
[WITT]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/Witt/RaynaudOperatorBoundary.lean#L19
[WITTORD]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/WittMonomialsShiftedConvolutionsAndBrauerCancellation.lean#L182
[WL]: ../../../formal/GaloisForLFunctions/BiScaleUncertainty/WeilLagCriticalDeficitEndpointAndLimitLaw.lean#L868
[WORLDI]: ../../../formal/GaloisForLFunctions/WorldsOfTheZeroConfiguration/AFiniteLayerCanBeEditedAway.lean#L136
[XN]: ../../../formal/GaloisForLFunctions/RHTower/XiNewtonDiscSourceMargin.lean#L219
