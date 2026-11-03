# RH proof-route frontier

**RH open · 33 live routes · 16 candidates.**
**Corpus checkpoint:** `bf31cc106047cc3f33cda86f4e589022902f19d1`.

Live = source observable + proved RH-sufficient receiver + explicit open estimate. Candidate = missing independent source mechanism/landing.
Evidence: [L] integrated, source-reviewed; [S] unfinished/unintegrated, unverified; [K] individual Lean + standard-only transitive-axiom audit. Untagged established facts: [L].

[Routes](#live-routes) · [Candidates](#route-candidates) · [Shared positivity frontier](#shared-frontier) · [Killed/retired](rh-killed-routes.md) · [Source codes](#source-locator)

<!-- Status quo only: replace the affected frontier; do not append theorem inventories. -->

## Find a route

| Family | Live routes | Candidates |
|---|---|---|
| Arithmetic incidence | [AIP](#aip) | — |
| Prime explicit formula / signed energy | [WL](#wl), [RW](#rw), [FU](#fu), [CFC](#cfc), [RP](#rp), [PA](#pa), [LI](#li), [JAS](#jas), [CTF](#ctf), [EWU](#ewu), [OWU](#owu), [PBM](#pbm), [RB](#rb), [ACT](#act) | [APF](#apf), [EGC](#egc), [EWJ](#ewj), [FEL](#fel) |
| Möbius cancellation | [MC](#mc) | [MSC](#msc) |
| Theta / heat / moments | [TT](#tt), [LA](#la), [TH](#th), [HCF](#hcf) | [HJ](#hj) |
| Zero visibility / localization | [SRT](#srt) | — |
| Causal hyperbolic–modular duality | [CHMD](#chmd) | — |
| Geometry / index / arithmetic rigidity | [TG](#tg), [HF](#hf), [GTA](#gta), [ACS](#acs) | [DR](#dr), [IRK](#irk) |
| Newton dynamics | [XN](#xn) | — |
| Renewal / singular comparison | [RN](#rn) | — |
| Ward / collision | [WD](#wd) | — |
| Suzuki / boundary limits | [SZ](#sz) | [SEC](#sec) |
| Physical realization | [PM](#pm) | [PTR](#ptr), [W1C](#w1c) |
| Singular source completion / affine index | [SC](#sc) | [BSH](#bsh), [CDC](#cdc), [PCS](#pcs), [RFHM](#rfhm), [WBF](#wbf) |
| Deterministic recurrence | [BAG](#bag) | — |

## Live routes

<a id="wl"></a>
### WL — Weil lag function

- **Path:** Prime lag/error → square-root bound or subexponential critical energy → RH.
- **Established:** Exact prime-error/energy criteria. Even the fixed first Chebyshev cyclotomic band has energy abscissa2Θ; RH iff its energy is O_ε(N^(1+ε)). Every eventually nonempty band has the same abscissa.
- **Open:** Actual signed square-root precision / first-band bound. Narrowing the band does not remove off-line zero growth.
- **Sources:** B:WeilLagCriticalDeficitEndpointAndLimitLaw; CAF:FirstCyclotomicBandAbscissa.

<a id="rw"></a>
### RW — Restricted Weil ground energy

- **Path:** Complete Weil form → μ(a)≥0 at every radius → RH.
- **Established:** Attained, strictly radius-decreasing minima; μ≥1/5000 through a=181/500, ≥1/8000 through a*=enlargedWeilFloorAperture>181/500. Exact {∞,2} trace through a=½log3; local Gamma/Tate domination for length≤2a*, 0≤k≤1/160000. Window positivity⇔all fitting lattices; actual margins positive through length181/250. RH forces every nonzero-bump lattice's margins positive and tending0 [L]. [Odd first-fold reduction](#owu); [lattice/refinement frontier](#shared-frontier).
- **Open:** All-stage contraction/Schur sign paying signed prime folds and low-moment cross-terms. Frozen interior infimum attainment; first-critical zero modes are determined by either end collar, but not excluded [L]. [Fixed positive lattice slack fails](rh-killed-routes.md#lattice-positive-slack).
- **Sources:** C:TheApertureFlowNeverStalls; I:AnExplicitLargerApertureRetainsAWeilFloor; ATD:FirstFoldStageDomination; SP:SemilocalPrimeTwoTrace/IntrinsicWeilTraceAndWindowCorollaries; CSTW:WindowGrowthIsATranslationContraction; CSTW:TheFrozenFormInClosedForm; GWZ:AWindowIsTheUnionOfItsLattices; GWZ:TheLatticeHasNoSlackUnderRH; GWZ:ZeroModesHaveReflectionParity [L].

<a id="fu"></a>
### FU — CCM-FU signed prime scheduling

- **Path:** Signed prime/Möbius history → completed Abel moment A(M)/M bounded above → RH.
- **Established:** Exact receiver, exhaustive prime schedules and clock kernels.
- **Open:** One joint bound paying seed, drift, prior action, cross-block covariance and endpoints.
- **Sources:** R:CCM/CCMFUSuzukiMobiusDivisorOneSided; B:PrimeGraphClockCorrelationKernels.

<a id="cfc"></a>
### CFC — CCM first-clock lower bound

- **Path:** Published first-clock sine coefficient bounded below on an aperture tail → RH.
- **Established:** Exact tail criterion; ¬RH forces unboundedness below on every tail. Phase-natural source transport is identity.
- **Open:** Actual lower bound retaining prime, archimedean and endpoint terms; transport feasibility supplies no bound.
- **Sources:** R:CCM/CCMFirstClockTailLowerBoundCompleteness; R:CCM/CCMFirstClockPhaseNaturalTransportRigidity.

<a id="rp"></a>
### RP — Route-P / SP-E history floor

- **Path:** Matched−quantile prime history → eventual linear defect floor → RH.
- **Established:** Exact linear-floor criterion; low-LCM and copied-diagonal payment. Sublinear floor is impossible.
- **Open:** High-LCM pairs, moving core and singular-domain terms in one complete-history floor.
- **Sources:** R:SPEQuantileRieszRoutePLinearFloorCriterion; R:RoutePLcmPairPayment.

<a id="pa"></a>
### PA — Prime–archimedean source passivity

- **Path:** Prime−archimedean trace → current sign or subexponential mismatch → RH.
- **Established:** Exact receivers; each fixed Hausdorff order positive at sufficiently large shifts.
- **Open:** All-order/all-shift sign. Order-dependent thresholds leave a signed high-frequency complement.
- **Sources:** R:PrimeArchEndpointFrequencyAccretivity; R:PrimeArchHausdorffFixedOrderLargeShiftPositivity.

<a id="finite-prime-clocks"></a><a id="mc"></a>
### MC — Möbius cancellation at half power

- **Path:** Actual Möbius/Liouville cancellation at half power → RH.
- **Established:** Half-power and Redheffer determinant criteria; polynomially growing near-frequency bands retain exponent2Θ. Gauge exponent is Haar-a.e.1/2 but Baire-generically1; generically every prescribed sublinear benchmark is exceeded arbitrarily late.
- **Open:** Actual Möbius cancellation, including moving-band head/leaf covariance. Neither measure-generic nor category-generic gauge behavior controls the trivial arithmetic point.
- **Sources:** R:MobiusHilbertFormEquivalence; ADT:TheMertensFunctionIsAGluingDeterminant; AGT:TheBaireGenericExponentIsOne.

<a id="tt"></a>
### TT — Theta-tail and heat–Cassini currents

- **Path:** Theta source → directed covariance/Wold decay or odd Weil sign → RH.
- **Established:** Exact receivers and Φ-Doob identities retaining every reflected-prime term; restricted current signs.
- **Open:** All-test directed covariance or odd/primitive positivity; signed reflected-prime interaction remains.
- **Sources:** R:PaperWoldDirectedCovarianceRH; R:WeilMarkovOddPositivity.

<a id="la"></a>
### LA — Line anchor

- **Path:** Theta source → all-height/all-degree Jensen or heated coefficient sign → RH.
- **Established:** Each fixed Jensen degree eventually real-rooted; quantitative heat/depth bounds and density-one fixed-depth control.
- **Open:** Uniform signs through all heights/degrees, shallow near-double pairs and exceptional windows. Fixed-degree or density-one statements are insufficient.
- **Sources:** R:Jensen/EveryFixedDegreeIsEventuallyRealRooted; R:Heat/TheLocalHeatThreshold; R:XiSliceHeatOrderUniformPositivity.

<a id="tg"></a>
### TG — Topological sub-unit gate

- **Path:** Euler/Gaussian source → nonnegative residual + integer trace<1 → RH.
- **Established:** Winding/index and cubic-transgression identities; exact central-gap receivers.
- **Open:** Matrix-complete positive residual and sub-unit integer trace on every disc, or zero-rate central-gap bound.
- **Sources:** R:FormationAnchoredCubicSpecialization; R:GaussianCentralGapExplicitCriterion.

<a id="hf"></a>
### HF — Positive Hodge form on arithmetic cohomology

- **Path:** Complete arithmetic form ≥0 → Hodge index → RH.
- **Established:** Hodge/Hecke/Riemann–Roch receivers; full-matrix positivity at every overlap exponent0<α<1/8. One aperture-independent 0<K≤K₀ gives eventual critical positivity for each fixed family. Fixed twisted sectors positive; critical conductor-diagonal convergence uniform on some M(N)→∞. Fixed-conductor bare-prime second-order entries explicit in γ,γ₁ and divisor logs [L].
- **Open:** Full growing-family critical-overlap sign at every required multiple, or independent all-window positive realization. Small-K aliasing masks Weil sign. Exact-clock eventual sign requires strict leading positivity; equality turns negative [L]: [critical boundary](rh-killed-routes.md#critical-pencil-nullspace). [Positive multiplicative Euler data and any finite ζ prefix do not force criticality](rh-killed-routes.md#definite-counts).
- **Sources:** J:TheIndexExit; [critical matrix, twists and conductors](#shared-frontier).

<a id="chmd"></a>
### CHMD — Causal Hyperbolic–Modular Duality

- **Path:** Complete causal prime/Möbius wave bound or odd Doob half-threshold bound → RH.
- **Established:** Wave/Doob receivers, Haar transport and prime-edge Gamma reserve. In original unit Haar/coarse masses, (full prime−pole)/√Y has operator norm O(exp(−√log Y/92160000)), uniformly over every detail horizon and M≤exp(√log Y/184320000). Same bound for the common-horizon all-prime source; normalized prime matrix approaches one separable pole channel [L].
- **Open:** Complete wave/odd sign: pay Gamma, signed potential and infinite-orbit terms in the receiver's normalization. The retained √Y scaling does not give an unnormalized vanishing error or full-Weil index ceiling.
- **Sources:** R:CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion; R:CHMDOddSectorCriterion; AID:AllDetailPrimePoleCancellation.

<a id="th"></a>
### TH — Theta moment positivity

- **Path:** Signed center-mixed theta jets → all-rank Hankel positivity → RH.
- **Established:** Rank7 strict; rank8 PSD. Native tails split into Gram-square mass minus signed local flux.
- **Open:** Rank8 strictness and uniform higher-rank flux payment; orthant positivity does not supply arbitrary signed positivity.
- **Sources:** R:ThetaCusp/ThetaCuspCenterMixedSignedJetCompleteness; R:ThetaCusp/ThetaCuspOddFourRankEight; R:ThetaCusp/ThetaCuspCenterTailSquareFlux.

<a id="rn"></a>
### RN — Theta renewal and singular comparison

- **Path:** Theta renewal source → divisor-faithful winding/boundary-work sign → RH.
- **Established:** Green/BV realization; compact cone-positive renewal operator with exact determinant/resonances.
- **Open:** Directed mixed prime+Gamma≥pole, including cusp/seam terms. Cone positivity alone does not give real spectrum.
- **Sources:** R:ThetaRenewalPositiveFredholm; R:ThetaRenewalFredholmSpectrum.

<a id="heat-charge"></a><a id="log-scale-defect"></a><a id="mollified-corridor"></a><a id="wd"></a>
### WD — Ward orientation and horizontal collision

- **Path:** Source current/window energy → collision charge<2 or all-resolution sectoriality → RH.
- **Established:** Attained extremizers; collision/index receivers; Laplace abscissa=twice maximal depth. Almost-all log-stage certificates⇔log-free unit occupancy [L]. Boundary-regular finite-theta windows: bounded P₊⇔line purity; [unweighted L²⇔empty window](rh-killed-routes.md#window-port-l2). Burnol N≥capCancelSqrtPrefix(m): P₊=O_(m,N)(e^((σ_m−1/2)t)/(1+t)), σ_m=1−1/(116log(m+5)); boundary-weighted L². Outside O(V/loglogV) unit windows, exponent improves to 3loglogV/logV for every N≥doorSqrtPrefix(m) [L].
- **Open:** Independent zero-rate right-port bound through inner caps and finite/shallow exceptions, with prefix-limit control. Density branch: thin nonempty Planck shadows in o_A(V) unit windows and compatible vanishing cluster tail at fixed A; volume/second-moment bounds do not pay them. [Density separations](rh-killed-routes.md#window-density-separation).
- **Sources:** CDG:LogScaleHeckeDefect/UnitWindowMinimumAndOscillation; CDG:LogScaleHeckeDefect/HalfGateClosureAndDensityEquivalence; CDG:SzegoCollision/WindowEnergyLaplace; CDG:SzegoCollision/LogStageBesselCertificate; CDG:WindowPortFlux/CauchyCapCancellationAndPolynomialStage; CDG:NearLineLogMean/NearLineDensityBesselCertificateAndSeparation; CDG:WindowPortFlux/RightHalfPortCriticalLineControl; CDG:NearLineLogMean/ShortShellSecondMomentAndPlanckBridge [L]; R:WD/MomentsDoNotDetermineTheLogMean.

<a id="li"></a>
### LI — Paired Li and prime–Gamma balances

- **Path:** Prime−Gamma history floor / theta-clock first-zero budget → RH.
- **Established:** Guarded history-zero set Z_S finite; RH iff Z_S=∅. Actual Cayley–Li primitive-sign receiver [S].
- **Open:** Pay outside budget at every guarded zero or establish primitive sign. Finiteness of Z_S is not finite off-line ζ support.
- **Sources:** R:LiEvenCrossActualClockTerminalHistory; R:LiEvenCrossActualClockGrowthLaw; ALG:RHIsReflectionPositivityOfTheCayleyLadder [S].

<a id="sz"></a>
### SZ — Suzuki screw and shifted-kernel limits

- **Path:** Complete rectangular Ward defect bounded below at one positive width → RH.
- **Established:** Exact lower-bound receiver; finite reflected-current/light-cone Gram identities. Complete first-variation transfer [S].
- **Open:** Uniform lower bound after assembling negative-light, Gamma, boundary and mixed costs; bare-source boundedness is insufficient.
- **Sources:** R:Suzuki/SuzukiRectangularWardDefectBoundedness; R:Suzuki/SuzukiWallFieldLightConeKernelCompletion.

<a id="fzz-p--parity-delay-mellin-orientation"></a><a id="gauss-mayer"></a><a id="pm"></a>
### PM — Physical-model Haar approximation (FZZ-P)

- **Path:** Faithful scattering source → Krein/Lewis positivity or pole/escape exclusion → RH.
- **Established:** Resonances⇔ζ(2s)=0; Krein positivity⇔RH. Faithful Haar/Mellin synthesis and coefficient completion; damped reflection energy→Weil [L]. Full-strip closed compatible reflection: dense domain, actual core exchange, every source interval a graph core [K]. Re s>0: paired WTZ T₂ lifts lie in whole-Haar L² iff H(−log2)=0; universal threshold A≤log2 [K]. On 0<Re s<1/2, Im s>0, global actual-core identity retains both boundary channels; two evaluations recover them and give every-prime corrected eigenvalue1+p^(1−2s), one channel at resonances [K].
- **Open:** Corrected boundary carrier with full Mayer transfer compatibility and physical signed-form descent; then independent positivity/pole exclusion. Point-evaluation corrections are not yet a closed Haar-space operator. Full eigenspace/rational Weyl identification remains. [Bounded reflection](rh-killed-routes.md#cauchy-reflection-order) requires Re s≥1/4; closed reflection supplies no sign.
- **Sources:** RIT:MayerScattering/MayerResonanceCharacterization; RIT:MayerScattering/TheHeckeEquivariantCompletion [L]; RIT:MayerScattering/ClosedCauchyReflection; RIT:MayerScattering/WholeHaarHeckeWindowAdmission; RIT:MayerScattering/CoreCauchyAnalyticContinuation; RIT:MayerScattering/GlobalCoreHeckeCorrection [K]. [Finite-core sign](rh-killed-routes.md#mayer-krein-sign), [boundary restoration](rh-killed-routes.md#core-hecke-boundary).

<a id="jas"></a>
### JAS — Joint ancestry

- **Path:** Prime-product positivity or every-exponent subpower square-shell bound → RH.
- **Established:** Exact receivers; finite-support/phase/grade admission; growing logarithmic-budget positivity.
- **Open:** Square-root power budget or all-amplitude/subpower shell control. Admission supplies no budget growth.
- **Sources:** R:JointAncestryLevelOneCapstones; R:JointAncestrySquareShellFinitePowerCriterion.

<a id="ctf"></a>
### CTF — Chronological tail / Báez–Duarte approximation

- **Path:** Actual Möbius approximation error→0 / complete covariance energy subpower → RH.
- **Established:** Exact completion, optimizer and residual-square identities; cutoff approximation retains terminal boundary and mass mismatch.
- **Open:** Signed covariance cancellation along compatible cutoffs. Receiver needs X^ε for inner X<M, not M^ε; terminal edge cannot be discarded.
- **Sources:** R:ChronologicalRiemannEquivalence; CAF:DivisorCovariance; R:EulerDeletionCutoffAverage.

<a id="hcf"></a>
### HCF — Gaussian heat trace / critical feature variance

- **Path:** Exact arch−prime heat trace → both prime-log grids positive at every degree → RH.
- **Established:** Heat explicit formula, two-grid RH criterion and arbitrary-zero detector.
- **Open:** Actual signs at every degree/height, or one-sided vertical bound. Two-grid non-aliasing does not control coalescence/many-node Gram eigenvalues.
- **Sources:** R:XiGaussianHeatTwoPrimeSourceSampling; R:HeatGridAliasingBoundary.

<a id="xn"></a>
### XN — Xi Newton invariant discs

- **Path:** Xi first jets → line-centered Newton self-map discs covering all zeros → RH.
- **Established:** Coverage/self-map criterion; nonnegative Laplacian of interior margin.
- **Open:** Actual covering with nonnegative interior margin. Boundary sign does not pay curvature.
- **Sources:** R:XiNewtonSchwarzPickCriticalLine; R:XiNewtonDiscCurvature.

<a id="bag"></a>
### BAG — Deterministic zeta self-return

- **Path:** Actual ζ returns near every right-strip target at every tolerance → RH.
- **Established:** Strong/local recurrence and Haar-mass receivers; weak ladders collapse to RH.
- **Open:** Returns including possible target zeros. Zero-free-target universality leaves precisely those targets untreated.
- **Sources:** R:ZetaStrongRecurrenceReceiver; R:ZetaWeakRecurrenceLadderCollapse.

<a id="ewu"></a>
### EWU — Even pole-weight uniqueness

- **Path:** Even blind minimum≥0 at every aperture → even positivity → RH.
- **Established:** Weight rigidity; attained aperture-antitone blind minima; local/high-window signs.
- **Open:** Nonnegative actual minima at all apertures, including low/mixed modes. Restricted positivity is not transported by arbitrary tent limits.
- **Sources:** R:EvenSectorPoleWeightUniqueness; R:EvenSectorBlindVariationalAttainment.

<a id="gta"></a>
### GTA — Transverse Schur charge

- **Path:** Positive theta-stage Schur charge → rank-uniform transverse decay → RH.
- **Established:** Exact decay criterion; positive charge and strong finite-prefix convergence.
- **Open:** Rank-uniform arithmetic energy decay independent of zero data.
- **Sources:** R:Hedenmalm/HedenmalmThetaSchurQuarticSpectralDecayEquivalence; R:PaperThetaSchurModeCharge.

<a id="owu"></a>
### OWU — Odd Weil-weight uniqueness

- **Path:** Actual odd Weil positivity at every aperture → RH.
- **Established:** Odd RH criterion; prime-free floor and complete unit-window coercivity off x,x³ [K]. Unit-window Q≥R_ret+‖F‖²/64; some C² test has R_ret<0<Q [K]. For G(u)=F(u/2), Q(F)≥firstFoldTwoMomentForm(G): exact logarithmic exterior potential and signed prime2 reflection, with explicit P₁/P₃ moment debits [L].
- **Open:** Sign of this explicit two-moment/reflection form, or stronger joint payment in complete Q; then all apertures. [Gamma reserve](rh-killed-routes.md#retained-gamma-lower-form) repairs one negative retained direction, not every odd test.
- **Sources:** R:WeilMarkovOddPositivity; WTZ:TheFirstFoldIsPositiveAwayFromTwoOddMoments; WTZ:TheGammaRemainderPaysAUniformReserve; WTZ:TheGammaRemainderCannotBeDiscarded [K]; WTZ:ThePrimitiveVarianceRetainsTheOddMoment; WTZ:TheFirstFoldRetainsTwoMomentCharges [L].

<a id="pbm"></a>
### PBM — Regularized prime/log-ζ abscissa

- **Path:** Pole-regularized prime/log-ζ Dirichlet convergence for every σ>1/2 → RH.
- **Established:** Exact convergence/RH equivalence.
- **Open:** Actual coefficient cancellation down to the critical abscissa; regularization alone supplies none.
- **Sources:** R:RegularizedLogZetaAbscissa; R:PaperPrimeRegularizedIdeal.

<a id="rb"></a>
### RB — Robin/Nicolas divisor-sum criterion

- **Path:** Growing extremal divisor sums/primorial products satisfy Robin/Nicolas → RH.
- **Established:** Eventual criteria, colossally abundant reduction and growing-prime-core constraints.
- **Open:** Square-root remainder on prime-saturated extremizers. Necessary divisibility conditions do not exclude counterexamples.
- **Sources:** R:RobinColossallyAbundantReduction; B:RobinMovingValuationDefect.

<a id="srt"></a>
### SRT — Prime-side one-parameter lag localization

- **Path:** Complete atomic-family sign / horizon-layer sign / late-lag bound → RH.
- **Established:** Full-family receivers/index exhaustion. Depth≥δ, |γ|≥2 gives a smooth negative test in [−a−1,a+1] for a≥max(e⁶,1/δ), C log(|γ|+306)log a≤a; no separation needed. Fixed packets e≤L, 0<2λL≤π, c_N>0, c_N/N→0: zero-bulk through |γ|≤λN, rescaled by logN/c_N, tends κ·poleCoefficient²·Σρ mρ/[ρ(1−ρ)]. Separate bare-prime fixed-conductor second order is explicit [L]: [shared frontier](#shared-frontier).
- **Open:** RH-complete sign at every required multiple; high-zero tail above the grid and receiver-scale conductor/frequency uniformity. A nonquantitative growing conductor range is available [L]; fixed bulk sees the pole coefficient, not off-line depth.
- **Sources:** S:ClusterProductHorizon; AHD:TheHorizonCriterion; [bulk, index and conductor sources](#shared-frontier).

<a id="act"></a>
### ACT — Arithmetic criticality / single-shift variation

- **Path:** One fixed shift pays every even compact C² profile → odd Weil positivity → RH.
- **Established:** Exact single-shift receiver; explicit collar thresholds pay any fixed finite admissible family.
- **Open:** One shift uniform in profile/support, including exterior primes and signed/polar remainder.
- **Sources:** D:ShortProfilePoleFreeVariationInequality; I:ShiftedCollarsHaveExplicitPaymentThresholds.

<a id="aip"></a>
### AIP — Arithmetic incidence positivity

- **Path:** Prime incidence + plateau gauge → all-aperture global allocation → odd positivity → RH.
- **Established:** Allocation receiver; full low-block/complement Schur payment for every 0<α<1/8; full tilted-spline matrix≥κ/(2c⁷)I uniformly 1≤c≤(log N)^α [L]. Small fixed critical-multiple far reserve on the pole complement, with a remaining prefix mass cost [S]: [shared frontier](#shared-frontier).
- **Open:** Global allocation or full sign at c=2K(log N)^(1/8) for every K>0; critical prefix/top Schur assembly remains incomplete [S]. Exact-clock leading equality turns negative [L]. Alternative: full-window translation contraction from the proved short-window seed.
- **Sources:** I:GlobalIncidenceAllocationCondition; I:GlobalSharedSurplusAllocation; CACT:TheCompleteWeilMatrixIsPositiveDefiniteBelowTheEighthRoot.

<a id="lattice-sections"></a><a id="acs"></a>
### ACS — Arithmetic Castelnuovo–Severi effectivity

- **Path:** Arithmetic effectivity / Rosati heights / bounded Weil coupling → Hodge → RH.
- **Established:** Effectivity/count-height receivers; primitive h¹=Q/2; local Weil floors/Tate domination. Pure-curve degeneration gives the Hurwitz form; finite-curve growth reads log(max|β_i|)/log q, with both signs when max|β_i|>1. Full-Selberg Euler discrepancy absolutely convergent at some σ<1/2 forces equal coefficients without Gamma matching; agreement outside finitely many primes suffices [L].
- **Open:** All-aperture primitive effectivity or an independent dominating count; sharp genus upper law. [Positive Tate counts](rh-killed-routes.md#tate-count-selector) do not descend to Weil sign; [finite-prefix positive Euler data](rh-killed-routes.md#definite-counts) do not force criticality. [Smooth reflection centralizers and same-window Hecke similitudes are scalar](rh-killed-routes.md#window-reflection-centralizer); a nontrivial positive realization needs a larger carrier.
- **Sources:** G:ExactArithmeticSourceEffectivity; LST:TheStepanovCountPaysThePrimitiveH1OverFiniteFields; ATD:FirstFoldStageDomination; AHD:DegenerationSelectsThePureCurves; AHD:TheMonodromyRateOfACurveIsItsZeroWidth; SEL:GammaIndependentEulerRigidity; SEL:FinitePrimeRigidity [L].

<a id="inter-tower-coupling"></a><a id="coupled-tower-signature"></a><a id="sc"></a>
### SC — Stokes/Witt–Krein / archimedean successor

- **Path:** Glued affine Weil index≤1 / bounded Gaussian-damped two-prime kernel coupling → RH.
- **Established:** Exact glued index=κ_ζ+1; complete-matrix/tensor receivers. For distinct primes p,q and fixed τ>0, Gaussian-damped coupling is O(exp(σt)) iff width≤σ, σ≥0, t=m log p+n log q; bounded ℕ² coupling⇔RH, including unattained width. All-detail/growing-coarse prime–pole norm decay and rank-one approximation: [CHMD](#chmd).
- **Open:** Prime/archimedean bound for damped coupling, or glued index≤1/complete pole-hyperplane sign. √Y-normalized prime–pole decay supplies neither. [Undamped coupling plus full RvM counts admits off-line exact-spline model divisors](rh-killed-routes.md#coupling-growth); arithmetic source control is essential.
- **Sources:** AKG:TheGluingFormulaAtEveryPlace; AKG:TowerCoupling/CoupledTowerSignatureFormula; ACPL:ConeBoundary/GaussianConeKernel; ACPL:ConeBoundary/PolynomialBoundaryRepulsion; ACPL:ConeMoments/RVMCompletedSplineDivisor; AID:AllDetailPrimePoleCancellation.

## Route candidates

Promotion requires the missing independent source mechanism/landing below; an unproved final estimate alone does not make a live route a candidate.

| Candidate / intended path | Established [L] | Promotion gap | Sources |
|---|---|---|---|
| <a id="apf"></a>**APF — Arithmetic paired Fredholm:** prime source → divisor exhaustion → trace vanishing. | Fredholm index and actual cycle-trace Fourier reconstruction. | Zero-independent divisor exhaustion/vanishing. Reconstructing off-line coefficients does not kill them. | R:PaperZetaCycleFourierReconstruction; R:PaperPrimeFredholmReconstruction |
| <a id="bsh"></a>**BSH — Arithmetic mate curvature:** prime−Gamma section → mate identity → orientation. | Framed curvature and radial-fibre diagnostics; finite cutoffs trace-blind. | Pre-divisor section and mate identity coupled to actual Ξ zeros without assuming neutral radial character. | R:Deninger/DeningerOneSidedFramedMateCurvatureTransgression |
| <a id="cdc"></a>**CDC — Constitutive dagger:** arithmetic presentation → confluence → neutral grade. | Calibrated confluence iff Re s=1/2; entropy/exchange-defect identities. | One source-defined potential descending on all closed error fibres and forcing confluence at actual zeros. | R:ConstitutiveDaggerConfluence; R:PaperCompletionInformationCost |
| <a id="dr"></a>**DR — Dyadic Xi roots:** compatible global strict-right roots → zero-free Ξ. | Cusp roots, finite monodromy/Kummer data and capped atlas. | Source-driven continuation and compatible roots on the whole strict-right domain; global monodromy remains. | R:XiSymmetricLittlewoodZeroFreeCuspDyadicRoots; R:XiTiltPuncturedMonodromy |
| <a id="egc"></a>**EGC — Pole-safe contour:** correction → outer covariance/sign. | Complete copy correction/enclosed-pole cancellation; centered exterior tail decay; nonzero Gamma baseline. | Outer expanding-contour sign excluding off-line copies. Inner cancellation is nonselective; raw decay cannot beat Gamma floor. | R:PaperEGCCompleteCorrection; R:PaperEGCSourceRayBaseline |
| <a id="ewj"></a>**EWJ — Euler/Wold jets:** faithful third jets → exhaustive source budget. | Finite-depth jets and compact-quotient character. | Zero-independent source admission and norm exhaustion into the RH receiver; fixed-history observations miss transverse gaps. | R:PaperEulerWoldDepthHistory; R:PaperEulerWoldCompactCharacter |
| <a id="fel"></a>**FEL — Theta likelihood:** predeclared history → zero/prime contrast balance. | Probability/KL and adaptive entropy accounting; BSY integral=convergent off-line zero sum. | Cofinal balance from a predeclared arithmetic source, not adaptive accounting or a zero-indexed identity. | R:PaperThetaObservationHistory; R:BalazardSaiasYorZeroSum |
| <a id="hj"></a>**HJ — Hurwitz reflection:** rational fibres → reflection residual zero. | Two-seed residual=SEC charge; vanishing iff criticality; all-divisor vanishing matches HCF two-grid sign. | Pre-divisor forcing of residual vanishing/even-witness sign at actual zeros. | R:PrimeTailSeedHurwitzReflection; R:XiHurwitzFunctionalEquationEvenWitness |
| <a id="irk"></a>**IRK — Rotation-algebra trace:** arithmetic defect → K₀/Chern count → orientation. | Trace/winding laws and completed Xi-jet relation classification. | Arithmetic Poisson/projective lift with integral analytic count and correct source defect. | R:PrimeRotationCanonicalTraceIntegrality; R:PrimeRotationXiCompletedResolution |
| <a id="msc"></a>**MSC — Möbius−Sonin transport:** squarefree Hilbert source → Sonin sign. | Strict-right divisor multiplicity/conormal preservation; critical logarithmic discrepancy in L². | Source-faithful bridge to nonnegative Sonin/Weil energy. Divisor preservation and admission do not give sign. | R:SquarefreeDiscrepancyHilbertTransport; B:SquarefreeUnweightedHilbertSource |
| <a id="pcs"></a>**PCS — Singular co-shift:** singular ground → wall annihilation preserving forward mode. | Singular/wall ground; strong finite-prime convergence with norm/ideal gap. | Source-natural wall annihilation; any CTF bridge must retain the nonzero shift defect, not identify incompatible carriers. | R:PaperPrimeCoShiftCofinalGap; R:PCSChronologicalDilationCarrierObstruction |
| <a id="candidate-ptr"></a><a id="ptr"></a>**PTR — Photonic source:** prime-faithful lossless stack → real-rooted Ξ limit. | Finite lossless real-rooted stacks; Ξ-limit criterion. Existing converse uses unknown Ξ zeros; continuum port has unit gap. | Independent nonlocal prime-faithful port preserving exact Ξ, or zero-loss mechanism overcoming that gap. | R:PhotonicLosslessProductPortRH; R:PaperPoissonCompletionGap |
| <a id="rfhm"></a>**RFHM — Support grade:** faithful phase/depth source → non-inverse-covariant wall law. | Full finite-support/phase/grade admission, forward creation and strong cutoff exhaustion. | Source-defined symmetry-breaking phase/depth/compound law with arithmetic wall orientation. Reversible sewing remains inverse-covariant. | R:GammaThetaFullSupportSource; R:PaperRFHMSurvivalInformation |
| <a id="sec"></a>**SEC — Adjacent prime seam:** exact compactness/Fock boundedness → seam jump zero. | Essential norm=seam jump; exact vanishing and time-one factorial-Fock criteria. | Pre-divisor proof of exact eventual compactness or Fock boundedness at actual zeros. Asymptotic seam smallness is nonselective. | R:XiPrimeSeamAdjacentEssentialNormNoGo; R:TimeOneGammaJetFockRHCriterion |
| <a id="w1c"></a>**W1C — Clifford–Dirac / centred Lee–Yang:** arithmetic operator or ferromagnetic limit → real-rooted Ξ. | Lee–Yang/Ising receiver; faithful Haar realization, closed compatible reflection and corrected all-prime core eigenlaw [K]: [PM](#pm). | Source-defined Ising couplings with centred slow-field convergence, or positive arithmetic reflection form with self-adjoint generator. Closed reflection and corrected eigenlaws do not give [Krein positivity](rh-killed-routes.md#mayer-krein-sign). | R:LeeYangIsingGraphDatum; R:IsingLawConvergenceRH; RIT:MayerScattering/ClosedCauchyReflection; RIT:MayerScattering/GlobalCoreHeckeCorrection [K] |
| <a id="wbf"></a>**WBF — Source certificates:** arithmetic stream → depth-uniform positive completion → Ξ. | Abstract genealogy Gram/Fredholm recovery and relative determinants; no arithmetic coupling. | Arithmetic certificate stream and source-faithful uniform-depth completion landing on Ξ/Weil positivity. | H:PaperGenealogyFredholmRecovery; H:PaperCriticalGenealogyCompletion |

## Shared frontier

<a id="first-overlap"></a><a id="relative-prime"></a><a id="physical-prime-defect"></a><a id="prime-centered-output"></a>
### Atomic positivity — RW, HF, SRT, AIP, ACS, SC

Twist/pencil limits: C² profile on [0,1], positive square mass, Fourier-square decay exponent>4, regular positive spectral tail of order β>0; tilted spline β=7. κ=(∫φ)²/∫φ². Families fixed unless stated.

| Established | RH-complete target / obstacle |
|---|---|
| Tilted spline: eventually, uniformly 1≤c≤(log N)^α, every 0<α<1/8, full matrix≥κ/(2c⁷)I. Low-block, complement and residual Schur bounds jointly discharged [L]. | Full/pole-hyperplane sign at every c=2K(log N)^(1/8), K>0. Subcritical exponents do not reach this endpoint. |
| Some K₀>0: uniformly 1≤c≤2K₀(log N)^(1/8), pole-orthogonal energy≥7D_M/8+δ(log N)S₇/(8c⁷)−κ_P(log N)P/(1+loglog N)^B, eventually for every B∈ℕ, κ_P>0. D_M=prefix pole defect, S₇=Σ_(M<n≤N)(N/n)⁷x_n², P=Σ_(n≤M)x_n², M=N/linearDefectCutoff(c), δ>0 fixed [S]. | Pay the remaining prefix cost and assemble the full critical Schur bound; reach every required K, not one small multiple. |
| Fixed nonzero mean-zero periodic χ: exact second-order coefficient is its nonnegative Fourier-power Hurwitz sum; every fixed independent window family has eventual positive Gram. Fixed Ramanujan-twisted/untwisted mixed limit splits; negative index equals the untwisted pencil's index [L]. | Uniformity in growing periods/families; untwisted Weil sign. Positivity is not uniform over the entire growing horizon space. |
| Fixed finite nonresonant cosine twists have the exact nonnegative Fourier-power Hurwitz coefficient and eventual positive Gram on each independent family; character sectors decouple across opposite parities, not equal parities. Subtracting the zero-frequency pole leaves the untwisted aliasing count βJ/K [L]. | Moving/coalescing frequencies and growing-family uniformity; the finite-part identity does not control the joint frequency/horizon limit. |
| Critical pencil=κWeil+(βJ/K)weighted Gram, K=lim c^(β+1)/log N. Q(H)≥−C_p∫e^(−pu)H² on every negative-half-line window, p>1, C_p aperture-independent. One 0<K≤K₀ works at every aperture, eventually for each fixed family. Length A≤3/5: every K>0; smooth A<log2+1/50: cosh-hyperplane positivity/index≤1 [L]. | Every required K and full growing-family sign. Small-K aliasing reserve masks possible negative Weil directions; starting N still depends on the family. |
| Exact clock c⁸=Klog N: each fixed independent family has eventual inertia (n₊(P), n₋(P)+n₀(P), 0). Correction is −B₁₀/K times the exponent-10 weighted Gram; O(c⁻¹) clock shifts give either sign on a nullvector [L]. | Strict leading positivity or second-order clock payment; growing-family uniformity. Nullvector existence is not established; [equality is not a sign certificate](rh-killed-routes.md#critical-pencil-nullspace). |
| Length-2a windows carry level-a Weil index; supremum over windows/K counts distinct right zeros. Fixed conductor packets e≤L, 0<2λL≤π, c_N>0, c_N/N→0: rescaled sum through |γ|≤λN tends κ·poleCoefficient²·Σρ mρ/[ρ(1−ρ)]; pole-free limit0 [L]. | High-zero tail above λN and growing packets; this bulk detects only the pole coefficient. |
| Bare prime matrix P, fixed conductors e,f: ⟨PR_e,R_f⟩−(logN−ρ_e)⟨R_e,R_f⟩→D(e,f), explicit in γ,γ₁ and divisor logs. D(1,1)=2γ₁+γ²; D(p,p)=D(1,1)+p(log p)²/(p−1)² [L]. | Complete overlapping-form second order, twisted packets and growing-conductor uniformity; a bare-prime entry limit is not a critical-matrix sign. |
| Subcritical conductor blocks have relative Jordan-diagonal control; J(m)/J(1)=#P⁷(ℤ/mℤ) [L]. Critical c⁸/logN→K: some M(N)→∞ gives coefficient-uniform diagonal convergence. Exact E_m(c)=J(m)c⁻⁷R_m(c/m)≥0; count ratio→1 uniformly for m≤M=o(c). Collective squared-residual ratio→0 through N^θ, 0<θ<1/2 [L]. | Prescribed growth rate and complement/cross-term sign. [Bare count approximation fails for m≥Lc](rh-killed-routes.md#conductor-count-resolution); collective quasimodes do not imply a full-matrix lower bound. |
| Large-prime/cofactor norm frames uniform for d≤N^ε, √N<p≤N^θ, θ>1/2, ε≥0, θ+2ε<1 [L]. | Complete-Weil comparison, smaller primes and remaining composite bands. |
| RH⇔all translation contractions abs(W(τ_εu,v))²≤Q(u)Q(v), from the short-window floor. Full two-window decomposition; stage=frozen pairing−incoming prime correlation. Two-collar infimum decreases with collar width and equals0 at birth if the current window is nonnegative. First-critical zero modes are determined by either end collar [L]. | Independent signed fold/cross-term payment; frozen interior infimum finiteness/attainment. End-collar uniqueness does not exclude a nonzero mode. [Uniform Tate horizons fail](rh-killed-routes.md#tate-domination). |
| Window sign⇔all fitting lattices. E_(n+1)=E_n−β_n²/E_n; short Λ margins positive. All-lattice positivity⇔RH∧λ=Λ on n≥2. First degeneration has a finite positive moment representation. Under RH every nonzero-bump lattice has E_n>0 and E_n→0; dyadic refinement lowers margins [L]. Positive evolution: E_n→0 iff Σγ_n² diverges; under RH fixed-bump dyadic limits equal the finite-translate continuum infimum [S]. | Actual Λ positivity beyond short windows, with vanishing margins, not a [fixed positive slack](rh-killed-routes.md#lattice-positive-slack). Conditional refinement/limit laws do not establish sign or frozen-interior attainment. |
| Any nonzero C² profile on [0,1]: positivity on conductor spans≤N^θ, 0<θ<1/1080, through b_φloglog N; every polylog span through Kloglog N, each fixed K. Every subpolynomial span has a cutoff-dependent super-log-log clock [L]. | For general profiles, omitted bands and the receiver's prescribed clock; a cutoff-dependent clock need not reach it. |
| Zero-free logarithmic profile positive through ε₀L(log L)², L=loglog N; its reciprocal-floor budget works iff K≤ε₀ [L]. | Every required multiple; this profile's sign does not transfer to the Beurling profile. |
| One fixed smooth Beurling profile compresses every finite rational Gram at c_N=2L(log L)². Eventual pole-hyperplane sign on this single schedule⇔RH. Smooth nonnegative unit-bump receiver at every positive-power overlap [L]. | Actual sign on the selected profile/schedule. |

Sources:

- **Full matrix / frames:** CACT:TheCompleteWeilMatrixIsPositiveDefiniteBelowTheEighthRoot; CACT:EverySubpolynomialSpanHasASuperLogLogPositivityClock; CAF:LargePrimeCofactorsHaveUniformConductorFrames [L]; CACT:TheTopCollarHasADyadicSeventhPowerReserve [S].
- **Horizon / twists:** AHD:TheWindowIndexCountsTheRightZeros; AHD:TheTwistedDirectionsCarryNoNegativeSquares; AHD:EveryFrequencySectorInheritsThePolarization; AHD:OneCriticalMultiplePaysEveryWindow; AHD:TheCoshHyperplaneInheritsThePolarization; AHD:TheCanonicalCriticalClockEntersFromTheNegativeSide; AHD:TheCriticalBoundaryAddsItsNullDirections; AHD:TheUntwistedCountIsTheFinitePartAtZeroFrequency; AHD:TheBulkIsBlindBelowItsGrid [L]; AHD:TheConductorDecompositionHoldsOnAGrowingRange; AHD:TheCountFormEndsAtTheResolution [L].
- **Bulk second order:** AHD:TheBulkEntriesAreReadByTheStieltjesConstants [L].
- **Windows:** WTZ:TheAliasingWeightPaysEveryWindow; DZG:TheGroundStateRepresentationOfAStage; ATD:FirstFoldStageDomination; GWZ:TheTwoCollarFormIsBornZero; GWZ:ZeroModesHaveReflectionParity; CSTW:TheFrozenFormInClosedForm; CSTW:WindowGrowthIsATranslationContraction [L].
- **Lattices:** GWZ:AWindowIsTheUnionOfItsLattices; GWZ:TheLatticeSelectsTheVonMangoldtWeight; GWZ:ADegenerateWindowIsACurve; GWZ:MarginsAreBoundedByRecurrence; GWZ:TheLatticeHasNoSlackUnderRH; GWZ:RefiningTheLatticeLowersTheMargin [L]; GWZ:TheContinuumMarginIsTheDyadicLimit; GWZ:TheSzegoVerblunskyLaw [S].
- **Receivers:** SSHA:EveryEighthRootMultipleReceivesTheTiltedSpline; TM:ReceiverRate/SharpLogarithmicOverlapBudget; TM:ReceiverRate/EveryFiniteGramFitsOneCriticalOverlap; RIT:TheHodgeIndexAtCriticalOverlap.

<a id="external-literature"></a>
### Scope guards

- RH-equivalent receivers are proved; their arithmetic positivity/cancellation inputs remain open.
- Finite off-line support is conditional, not established for ζ; it would not imply RH.
- Critical-line census: simple-critical proportion≥0.67250071−ε uses imported Zeta23 plus local IGP. Higher proportions need actual signed prime surplus/moments; model16/21 is not a ζ proportion. [Sub-threshold data, form-factor/pair-density positivity and F≥1 beyond threshold do not force the 75% certificate](rh-killed-routes.md#positivity-three-quarters) [L].
- Fixed aperture/rank/scale and density-one control leave finite or shallow exceptions. No uniform positive ground-energy gap at unbounded aperture.

<a id="pw-b"></a><a id="hb--theta-cusp-hawking-causal-scattering"></a><a id="isc-polar"></a><a id="art"></a>
### Non-route labels

PW-B: [retired source-uniform extinction mechanism](rh-killed-routes.md#kr-pwb); surviving critical-line detector feeds PM/scattering. ISC-polar: rational Weyl pole-exclusion branch of PM/HF, not a separate route. BVI/ART: support. [Other killed mechanisms and retired aliases](rh-killed-routes.md).

ADT: conductor degeneration supporting HF/ACS/SC; gluing determinant reformulates MC. AHD: horizon/index receivers within SRT/HF/SC. CWS: window locality/signed folds/index exhaustion within HF/RW/ACS; independent all-window positive realization open. See [shared frontier](#shared-frontier).

WTZ/DZG/ATD: window algebra, Tate jets and signed-count/Doob identities supporting RW/HF/ACS/PM. Bare first-jet domination⇔Weil sign; independent all-aperture domination open. Exact early Tate thresholds; no fixed k>0 works at all apertures. GWZ/CSTW: collar gluing and lattice Schur reformulations supporting RW/AIP; independent source positivity open.

## Source locator

`K:Module` = `formal/GaloisForLFunctions/<directory>/Module.lean`. Search exact names with `scripts/formal_tools.py research "<name>" --mode lexical`; inspect Lean statements for full scope.

| K | Directory | K | Directory |
|---|---|---|---|
| R | RHTower | H | HTGeometry |
| B | BiScaleUncertainty | V | BezoutValuationIncidence |
| T | TransHorizonIncidenceMechanics | A | arithmetic-positivity-theory |
| C | ArithmeticContinuationAndCriticalEnergy | I | ArithmeticIncidencePositivity |
| S | SquareRootThreshold | Q | ScaleSignedIncidenceCriticality |
| G | ArithmeticCastelnuovoSeveri | O | ArithmeticOrientationTheory |
| D | ArithmeticCriticalityTheory | M | ArithmeticCompensationTheory |
| P | TransThresholdPairCorrelation | J | ArithmeticOrientationGeometry |
| CP | ArithmeticCorrespondencePositivity | PL | ArithmeticPolarization |
| APD | ArithmeticPositiveDuality | MPG | MultiplicativePositivityGeometry |
| ACG | ArithmeticCorrelationGeometry | ALDG | ArithmeticLocalDivisorGeometry |
| BG | BiarithmeticGeometry | SB | StripBochnerWeilForcing |
| AK | ArithmeticKunnethTheory | SSA | SignedSuccessorArithmetic |
| SAEI | SignedArithmeticEnergyIncidence | AE | ArithmeticEffectivityTheory |
| BGG | BiarithmeticGaugeGeometry | CDG | ConjugateDiagonalGeometry |
| SP | SelectivePositivityAndThresholdLaws | AES | ArithmeticElectrostatics |
| RBG | RenormalizedBiarithmeticGeometry | AIT | ArithmeticIntersectionTheory |
| RAPT | RenormalizedArithmeticPotentialTheory | ALG | ArithmeticLorentzianGeometry |
| SSHA | SpacingScaleHarmonicAnalysis | IGP | IncommensurableGaborPinching |
| AID | ArithmeticIndexDescent | SAHT | SignedArithmeticHodgeTheory |
| SMAP | SelectiveMultiscaleArithmeticPositivity | AM | ArtinMertens |
| HLF | HeckeLFunctions | ACP | ArithmeticCountingPositivity |
| HKT | HeckeKreinToeplitz | SCP | ShallowCauchyPrimeEnergy |
| RDP | ReflectiveDirichletPolynomialS2 | CACT | CriticalArithmeticCorrelationTheory |
| AKLT | ArithmeticKreinLangerTheory | ASRP | ArithmeticOfSquareRootPrecision |
| TM | TransMetzlerWeilPositivity | EAHT | EffectiveArithmeticHodgeTheory |
| CAF | CompletedArithmeticForms | AGT | ArithmeticGaugeTheory |
| AHA | ArithmeticHarmonicAnalysis | HEF | HilbertianExplicitFormulas |
| SSH | SuccessorShellArithmetic | ART | ArithmeticResonanceTheory |
| AKG | AdelicKreinGeometry | RIT | RenormalizedIntersectionTheory |
| EHT | EdgeHodgeTheory | CSAR | CriticalScaleArithmeticRigidity |
| BOT | Bottcher | HM | HilbertMetric |
| ACPL | ArithmeticCouplingTheory | HWV | HodgeTheoryWithoutVarieties |
| LST | LatticeSectionTheory | ADT | ArithmeticDegenerationTheory |
| AHD | ArithmeticHodgeTheoryOfDegenerations | CWS | CohomologyOfWindowsOfSpecZ |
| WTZ | WindowTowerOfSpecZ | DZG | DimensionZeroGeometryOfSpecZ |
| ATD | ArchimedeanTateDomination | GWZ | GrowingWindowsOfSpecZ |
| CSTW | CanonicalSystemOfTheWindowTower | SEL | SelbergClass |
