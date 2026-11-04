# RH proof-route frontier

**RH open · 32 live routes · 16 candidates.**
**Corpus checkpoint:** `181564a4e34431b1c4ad773428b61b865d1e6a49`.

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
| Geometry / index / arithmetic rigidity | [TG](#tg), [HF](#hf), [GTA](#gta) | [ACS](#acs), [IRK](#irk) |
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
- **Established:** Attained, strictly radius-decreasing minima; μ≥1/5000 through a=181/500, ≥1/8000 through a*=enlargedWeilFloorAperture>181/500. Exact {∞,2} trace through a=½log3; local Gamma/Tate domination for length≤2a*, 0≤k≤1/160000. All-window/lattice positivity and all-test strict two-site orbit bound⇔RH [L]. A compact C² Rayleigh minimizer satisfies 𝒮ω=μΦ²ω and Q(Φωu)=J+μ·mass+2V_s−2V_c [S]. [Odd](#owu) / [lattice](#shared-frontier) frontiers.
- **Open:** Independent all-test contraction paying signed prime folds and collar coupling. Reflection-pair prime-count bound⇔positivity on that pair; reflection-sector growth retains −Q(interior) [L]. [Odd modulus has opposing frozen/prime effects](#owu) [L]. [Shifted gauges supply positive outside-window charge](#act) [S], not signed-energy payment; minimizer gauges still need smooth attainment. [Compact bare/folded gauges fail](rh-killed-routes.md#prime-free-markov) [S]; [collar parity assumes positivity](rh-killed-routes.md#collar-positivity-induction); [end-collar uniqueness gives no interior attainment/gap continuation](rh-killed-routes.md#lattice-interior-gap).
- **Sources:** C:TheApertureFlowNeverStalls; I:AnExplicitLargerApertureRetainsAWeilFloor; ATD:FirstFoldStageDomination; SP:SemilocalPrimeTwoTrace/IntrinsicWeilTraceAndWindowCorollaries; CSTW:WindowGrowthIsATranslationContraction; CSTW:TheFrozenFormInClosedForm; GWZ:RHIsDecidedOnTwoSites; GWZ:TheFirstPrimeStageOpensPositive; SWC:OnReflectionPairsTheCouplingIsTheSmoothedPrimeCount [L]; SWC:ACriticalWindowIsAPoleChargedSolution [S].

<a id="fu"></a>
### FU — CCM-FU signed prime scheduling

- **Path:** Signed prime/Möbius history → one-sided sampled Abel bound → RH.
- **Established:** For each fixed integer m≥1, either upper or lower boundedness of A(j^m)/j^m⇔RH. One controlled sample in each sufficiently large backward window of length N^(1−δ), some δ>0, suffices.
- **Open:** Produce those samples from the complete signed history, retaining seed, drift, covariance and endpoints; no sharp constant or all-horizon bound required.
- **Sources:** R:MobiusDivisorOneSidedPowerGapBootstrap; R:MobiusDivisorLowerStripPowerGapBootstrap.

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
- **Established:** Half-power and Redheffer determinant criteria; signed damping-continuation⇔admission. Exact short/long divisor split; square-root-cutoff short head has bounded pronic energy for each 0<ε<1.
- **Open:** Actual Möbius cancellation; horizon-uniform signed long-modulus quadrature energy for dampings cofinal at0, retaining the full harmonic tail. [Generic gauges](rh-killed-routes.md#mobius-gauge-genericity) do not control the arithmetic point; [fixed-arity local spectator transport fails](rh-killed-routes.md#fixed-arity-hall).
- **Sources:** R:MobiusHilbertFormEquivalence; ADT:TheMertensFunctionIsAGluingDeterminant; C:SignedAveragedContinuationAndTheZeroWidthBand; C:LongModulusExactDecomposition; C:LongModulusShortEnergy.

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
- **Established:** Hodge/Hecke/Riemann–Roch receivers; fixed twisted sectors positive; critical conductor-diagonal convergence uniform on some M(N)→∞ [L]. Full-horizon floorκ₀/(2c⁷) through one small critical multiple; family-uniform finite-horizon Gram nonnegativity and all-aperture compensated window signs [K]: [shared frontier](#shared-frontier).
- **Open:** Every required critical multiple on the full space, or unbounded compensated ratios separately for each fixed window test. Current absolute residual losses R and R² persist as N→∞ at fixed R=c⁸/logN. Remove them through signed arithmetic cancellation; bounded-R aliasing masks Weil sign. [Leading equality](rh-killed-routes.md#critical-pencil-nullspace), [count/Tate](rh-killed-routes.md#count-hodge-source) and [twist-only](rh-killed-routes.md#untwisted-tate-piece) shortcuts fail.
- **Sources:** J:TheIndexExit; [critical matrix, twists and conductors](#shared-frontier).

<a id="chmd"></a>
### CHMD — Causal Hyperbolic–Modular Duality

- **Path:** One-sided bounded prime wave or odd Doob half-threshold bound → RH.
- **Established:** Wave/Doob receivers, Haar transport and prime-edge Gamma reserve. In original unit Haar/coarse masses, (full prime−pole)/√Y has operator norm O(exp(−√log Y/92160000)), uniformly over every detail horizon and M≤exp(√log Y/184320000). Same bound for the common-horizon all-prime source; normalized prime matrix approaches one separable pole channel [L].
- **Open:** Either upper or lower boundedness of the unnormalized prime wave, or complete odd sign paying Gamma, potential and infinite-orbit terms. √Y-normalized decay supplies neither bound nor a full-Weil index ceiling.
- **Sources:** R:CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion; R:CHMDOddSectorCriterion; AID:AllDetailPrimePoleCancellation.

<a id="th"></a>
### TH — Theta moment positivity

- **Path:** Signed center-mixed theta jets → all-rank Hankel positivity → RH.
- **Established:** Signed center-mixed Hankel rank8 positive definite and I₇(a)>0 for every 0<a<1/2 [K]. Two-diagonal zero-flux repair preserves every literal even5 mixed moment; one aperture-independent correction is positive near zero and on a cofinal tail [K].
- **Open:** Rank9: sign of I₈(a). [Every real constant diagonal-load pair fails global source positivity](rh-killed-routes.md#ninth-section-diagonal), including weighted representatives [K]. Need a different source certificate or direct integrated sign; then all-rank flux payment.
- **Sources:** R:ThetaCusp/ThetaCuspCenterMixedSignedJetCompleteness; TCS:StrictEighthSection; TCS:FifthEvenSourceRepair; TCS:FifthEvenInheritedLoadBoundary; TCS:FifthEvenOriginObstruction [K].

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
- **Open:** Independent zero-rate right-port bound through inner caps and finite/shallow exceptions, with prefix-limit control. Density branch: thin nonempty Planck shadows occupy ≤η(A)V unit windows eventually in V, η(A)→0 as A→∞, plus compatible vanishing cluster tail; volume/second-moment bounds do not pay them. [Density separations](rh-killed-routes.md#window-density-separation).
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
- **Established:** Krein positivity⇔RH. On 0<Re s<1/2, Im s>0: actual core lower trace=−ζ(2s), finite whole-Haar square energy⇔Mayer resonance⇔ζ(2s)=0. Charge-normalized core κ_s: ‖κ_s(a)−a^(1−2s)‖≤C(1+Im s)⁴e^(π Im s)a uniformly over resonances and a>0 [K]. Finite physical cusp-energy residue=Krein square [K]; twice the Gaussian-packet residue, followed by damping removal, recovers the complete Weil form [K]. Faithful Haar/Mellin completion; damped reflection energy→Weil [L]. Closed reflection with source-interval graph cores. Re s>0: whole-Haar T₂ admission iff H(−log2)=0, universal A≤log2. Retained ζ coordinate makes boundary restoration invertible on 0<Re s<1/2; corrected prime actions intertwine restoration with multiplier1+p^(1−2s). All positive-determinant source Hecke operators preserve the full Lewis carrier, all s∈ℂ; Tₚg(1)=(1+p^(1−2s))g(1) [K].
- **Open:** Arithmetic sign after counterterm subtraction. Common mixed-parameter boundedness, analytic completion, full Mayer transfer and signed-form descent; full eigenspace/rational Weyl identification. [Bounded reflection](rh-killed-routes.md#cauchy-reflection-order) requires Re s≥1/4; closed reflection supplies no sign.
- **Sources:** RIT:MayerScattering/MayerResonanceCharacterization; RIT:MayerScattering/TheHeckeEquivariantCompletion [L]; RIT:MayerScattering/ClosedCauchyReflection; RIT:MayerScattering/WholeHaarHeckeWindowAdmission; RIT:MayerScattering/CoreHaarResonanceAdmission; RIT:MayerScattering/GlobalCoreHeckeCorrection; RIT:MayerScattering/BoundaryRestorationCarrier; RIT:MayerScattering/AllPrimeLewisCarrier; RIT:MayerScattering/PrimeLewisBoundaryFunctional; RIT:MayerScattering/AllPrimeBoundaryTransport; RIT:MayerScattering/CoreScatteringAsymptotics [K]; RIT:MayerScattering/PhysicalCuspKreinResidue; RIT:MayerScattering/UniformNormalizedCuspRemainder [K]; RIT:MayerScattering/GaussianPhysicalCuspResidue [K]. [Finite-core sign](rh-killed-routes.md#mayer-krein-sign), [boundary restoration](rh-killed-routes.md#core-hecke-boundary).

<a id="jas"></a>
### JAS — Joint ancestry

- **Path:** Prime-product positivity or subpower bounds on moving finite power windows → RH.
- **Established:** For every ε>0, bounds abs(Riesz(m²,k))≤m^(εk), m<k≤m+m/log(m+1), on infinitely many m⇔RH. Finite-support admission and growing logarithmic-budget positivity.
- **Open:** Uniform arithmetic control on that moving k-window, or square-root prime-product budget. Finite admission supplies neither.
- **Sources:** R:JointAncestryLevelOneCapstones; R:JointAncestrySquareShellFinitePowerCriterion.

<a id="ctf"></a>
### CTF — Chronological tail / Báez–Duarte approximation

- **Path:** Bounded coefficient rows with chronological error→0 / complete covariance energy subpower → RH.
- **Established:** RH⇔arbitrary real finite rows with abs(a_k)≤1 reach every error tolerance; natural Möbius rows are one construction. Exact residual squares retain terminal boundary and mass mismatch.
- **Open:** Construct such rows or prove signed covariance cancellation along compatible cutoffs. Inner-X receiver needs X^ε, not outer M^ε; retain the terminal edge.
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
- **Established:** Strong/local recurrence receivers. RH⇔all high zeros approach the line at each fixed depth AND arbitrarily high returns on off-line-zero discs; positive return density is unnecessary for this paired criterion.
- **Open:** Arithmetic construction of those returns and all-zero approach to the line. Zero-free-target universality and density-one clustering do not supply either missing input.
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
- **Established:** Odd RH criterion; prime-free floor. On odd C² unit-window tests, E=‖F‖², m₁=∫xF: Q+(3203/320)m₁²≥E/1000; exact Gamma remainder, strip+prime2 floor1/16 and Q≥R_ret+(193/10000+17/23040)E+(13/3840)m₁² [K]. Odd modulus sign(x)abs(F) lowers the prime-free form including its pole square, but raises each kick whose lag≥support radius; exact first-stage split for radius≤log2 [L]. [Shifted-gauge window identity and positive outside charge](#act) [S].
- **Open:** All-test joint Gamma/prime/pole sign; shifted-gauge branch must pay the reflected-prime term D_a using 2S_a and charge variance/slack at every window. [R_ret+E/64 and its two-moment comparison fail](rh-killed-routes.md#retained-gamma-lower-form) [K]. [Compact folded supersolutions fail at half-window1/2](rh-killed-routes.md#prime-free-markov) [S]; [zero origin correction fails](rh-killed-routes.md#folded-origin-charge) [K].
- **Sources:** R:WeilMarkovOddPositivity; WTZ:TheThirdOddMomentIsPaidByTheFirstFold; WTZ:TheGammaRemainderHasAnExactEnergyIdentity; WTZ:TheLogarithmicStripPaysTheFirstFold; WTZ:TheUniformGammaReserveCannotPayTheFirstFold; WTZ:TheGammaRemainderRetainsHigherLags; WTZ:TheHigherGammaReserveRepairsTheQuadraticCutoff [K]; SWC:TheFrozenOddFormIsMarkovAndTheKickIsNot [L]; SWC:TheFoldedCriterionIsVoidOnTheUnitWindow; SWC:TheKickIsAPositiveSourceAndANegativeCollarConductance [S].

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
- **Established:** Full-family receivers/index exhaustion. Depth≥δ, |γ|≥2 gives a smooth negative test in [−a−1,a+1] for a≥max(e⁶,1/δ), C log(|γ|+306)log a≤a; no separation needed. Fixed-conductor second order for 0<c<1; near-Gamma kernel, horizon decomposition and growing near-Gram polar limit [L]. Logarithmic-row/divisor-jet limits, nonratio exterior bound and complete-form moments [S]: [shared frontier](#shared-frontier).
- **Open:** RH-complete sign at every required multiple; high-zero tail above the grid and receiver-scale conductor/frequency uniformity. A nonquantitative growing conductor range is available [L]; fixed bulk sees the pole coefficient, not off-line depth.
- **Sources:** S:ClusterProductHorizon; AHD:TheHorizonCriterion; [bulk, index and conductor sources](#shared-frontier).

<a id="act"></a>
### ACT — Arithmetic criticality / single-shift variation

- **Path:** One fixed shift pays every even compact C² profile → odd Weil positivity → RH.
- **Established:** Single-shift receiver; collar thresholds pay fixed finite families. For m_a=Φ(·−a)−Φ(·+a), a,c>0 and even compact C² u supported in [−c,c]: Ẑ(m_au)=2S_a−D_a+8V_c+8τ_cA₂, with nonnegative charge variance V_c, charge square mass A₂, and strictly positive outside charge τ_c [S].
- **Open:** One shift uniform in profile/support paying reflected-prime D_a against same-side energy 2S_a and charge terms. Positive outside charge alone gives no such inequality.
- **Sources:** D:ShortProfilePoleFreeVariationInequality; I:ShiftedCollarsHaveExplicitPaymentThresholds [L]; SWC:ShiftedGroundStatesArePoleChargedOnEveryWindow [S].

<a id="aip"></a>
### AIP — Arithmetic incidence positivity

- **Path:** Prime incidence + plateau gauge → all-aperture global allocation → odd positivity → RH.
- **Established:** Allocation receiver; full tilted-spline floorκ₀/(2c⁷) through one small critical multiple, uniformly over all horizon vectors; compensated all-window consequences [K]: [shared frontier](#shared-frontier).
- **Open:** Global allocation or full sign at c=2K(log N)^(1/8) for every K>0; the audited small-K range does not discharge the all-K receiver. Alternative: all-window translation contraction from the short-window seed.
- **Sources:** I:GlobalIncidenceAllocationCondition; I:GlobalSharedSurplusAllocation [L]; CACT:CriticalMultipleCompleteWeilPositivity [K].

<a id="inter-tower-coupling"></a><a id="coupled-tower-signature"></a><a id="sc"></a>
### SC — Stokes/Witt–Krein / archimedean successor

- **Path:** Glued affine Weil index≤1 / bounded Gaussian-damped two-prime kernel coupling → RH.
- **Established:** Glued index=κ_ζ+1; complete-matrix receiver. Fixed spline: tensor bounds abs(c(t))^k≤C_k exp(L_k t), L_k/k→0, imply RH; one fixed exponent for all k⇔RH [L]. For distinct primes and fixed Gaussian damping, ℕ² coupling has rate≤σ iff zero width≤σ; bounded coupling⇔RH, including unattained width. Normalized prime–pole decay: [CHMD](#chmd).
- **Open:** Arithmetic bound for damped coupling, sublinear tensor loss, or glued index≤1/complete pole-hyperplane sign. Linear-in-order tensor loss only repeats the existing width bound. √Y-normalized prime–pole decay supplies no zero rate; [undamped coupling plus full RvM counts admits off-line model divisors](rh-killed-routes.md#coupling-growth).
- **Sources:** AKG:TheGluingFormulaAtEveryPlace; AKG:TowerCoupling/CoupledTowerSignatureFormula; CP:TheBaseIsAFixedLoss; ACPL:ConeBoundary/GaussianConeKernel; ACPL:ConeBoundary/PolynomialBoundaryRepulsion; ACPL:ConeMoments/RVMCompletedSplineDivisor; AID:AllDetailPrimePoleCancellation.

## Route candidates

Promotion requires the missing independent source mechanism/landing below; an unproved final estimate alone does not make a live route a candidate.

| Candidate / intended path | Established [L] | Promotion gap | Sources |
|---|---|---|---|
| <a id="lattice-sections"></a><a id="acs"></a>**ACS — Arithmetic Castelnuovo–Severi effectivity:** arithmetic effectivity / Rosati heights → Hodge index → RH. | Effectivity/count-height receivers; primitive h¹=Q/2; local Weil floors/Tate domination; pure-curve Hurwitz calibration [L]. Full-Selberg Euler-log rigidity; degree in (0,1) empty; full class d<1 is the Dirichlet unit. Degree one: conductor q≥2m₀ or a genuine pole at1; normalized full class q≥2 or a pole [K]. | Independent source of all-aperture primitive effectivity beyond [excluded count ansätze](rh-killed-routes.md#count-hodge-source). Rosati heights remain receivers; [same-window Hecke similitudes are scalar](rh-killed-routes.md#window-reflection-centralizer). Selberg selection still needs coefficient periodicity, integer conductor and primitive-character identification. | G:ExactArithmeticSourceEffectivity; LST:TheStepanovCountPaysThePrimitiveH1OverFiniteFields; AHD:DegenerationSelectsThePureCurves [L]; SEL:GammaIndependentEulerRigidity; SEL:DegreeGap; SEL:DegreeOneConductorPole [K] |
| <a id="apf"></a>**APF — Arithmetic paired Fredholm:** prime source → divisor exhaustion → trace vanishing. | Fredholm index and actual cycle-trace Fourier reconstruction. | Zero-independent divisor exhaustion/vanishing. Reconstructing off-line coefficients does not kill them. | R:PaperZetaCycleFourierReconstruction; R:PaperPrimeFredholmReconstruction |
| <a id="bsh"></a>**BSH — Arithmetic mate curvature:** prime−Gamma section → mate identity → orientation. | Framed curvature and radial-fibre diagnostics; finite cutoffs trace-blind. | Pre-divisor section and mate identity coupled to actual Ξ zeros without assuming neutral radial character. | R:Deninger/DeningerOneSidedFramedMateCurvatureTransgression |
| <a id="cdc"></a>**CDC — Constitutive dagger:** arithmetic presentation → confluence → neutral grade. | Calibrated confluence iff Re s=1/2; entropy/exchange-defect identities. | One source-defined potential descending on all closed error fibres and forcing confluence at actual zeros. | R:ConstitutiveDaggerConfluence; R:PaperCompletionInformationCost |
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
| <a id="w1c"></a>**W1C — Clifford–Dirac / centred Lee–Yang:** arithmetic operator or ferromagnetic limit → real-rooted Ξ. | Lee–Yang/Ising receiver; faithful Haar realization, closed reflection, all-determinant Lewis invariance and corrected all-prime transport; actual-core Haar admission⇔resonance [K]; finite physical Krein residue and height-uniform normalized cusp remainder [K]; Gaussian physical residue [K]: [PM](#pm). | Source-defined Ising couplings with centred slow-field convergence, or positive arithmetic reflection form with self-adjoint generator. Admission/transport do not give [Krein positivity](rh-killed-routes.md#mayer-krein-sign). | R:LeeYangIsingGraphDatum; R:IsingLawConvergenceRH; RIT:MayerScattering/ClosedCauchyReflection; RIT:MayerScattering/AllPrimeBoundaryTransport; RIT:MayerScattering/CoreHaarResonanceAdmission [K] |
| <a id="wbf"></a>**WBF — Source certificates:** arithmetic stream → depth-uniform positive completion → Ξ. | Abstract genealogy Gram/Fredholm recovery and relative determinants; no arithmetic coupling. | Arithmetic certificate stream and source-faithful uniform-depth completion landing on Ξ/Weil positivity. | H:PaperGenealogyFredholmRecovery; H:PaperCriticalGenealogyCompletion |

## Shared frontier

<a id="first-overlap"></a><a id="relative-prime"></a><a id="physical-prime-defect"></a><a id="prime-centered-output"></a>
### Atomic positivity — RW, HF, SRT, AIP, ACS, SC

Twist/pencil limits: C² profile on [0,1], positive square mass, Fourier-square decay exponent>4, regular positive spectral tail of order β>0; tilted spline β=7. κ=(∫φ)²/∫φ². Families fixed unless stated.

| Established | RH-complete target / obstacle |
|---|---|
| Tilted spline: eventually, uniformly 1≤c≤(log N)^α, every 0<α<1/8, full matrix≥κ/(2c⁷)I. Low-block, complement and residual Schur bounds jointly discharged [L]. | Full/pole-hyperplane sign at every c=2K(log N)^(1/8), K>0. Subcritical exponents do not reach this endpoint. |
| Some fixed K₀>0: W≥κ₀/(2c⁷)I, eventually uniformly 1≤c≤2K₀(log N)^(1/8), κ₀=tiltedSplineSpectralFloorConstant. Prefix/collar Schur payment is complete. One horizon threshold gives Gram nonnegativity/index0 for every finite family; compensated window limits hold at every aperture [K]. | Full-space sign at every K>0. Small-K aliasing masks possible negative Weil directions; increasing N does not remove residual losses R=c⁸/logN and R². |
| Fixed nonzero mean-zero periodic χ: exact second-order coefficient is its nonnegative Fourier-power Hurwitz sum; every fixed independent window family has eventual positive Gram. Fixed Ramanujan-twisted/untwisted mixed limit splits; negative index equals the untwisted pencil's index [L]. | Uniformity in growing periods/families; untwisted Weil sign. Positivity is not uniform over the entire growing horizon space. |
| Fixed finite nonresonant cosine twists have the exact nonnegative Fourier-power Hurwitz coefficient and eventual positive Gram on each independent family; character sectors decouple across opposite parities, not equal parities. Subtracting the zero-frequency pole leaves the untwisted aliasing count βJ/K [L]. | Moving/coalescing frequencies and growing-family uniformity; the finite-part identity does not control the joint frequency/horizon limit. |
| Critical pencil=κWeil+(βJ/R)weighted Gram, R=lim c^(β+1)/log N. Aperture-uniform weighted floors give small-R positivity; length A≤3/5: every R>0; smooth A<log2+1/50: cosh-hyperplane positivity/index≤1 [L]. Joint pole cost d(p)=1/√(p²−1)−1/p, C_joint(p)=abs(Γ(0))+2primeMass(p)+d(p), enlarges the weighted-floor threshold to R*=7J/(κC_joint(8)): pencil≥0 for 0<R≤R*, fixed independent horizon families eventually positive for 0<R<R* [K]. | For each fixed test, compensated sign at unbounded R removes aliasing. Bounded R does not suffice; no enlargement of the independently proved whole-space band follows. Whole-space alternative: every K and all vectors. |
| Exact clock c⁸=Klog N: each fixed independent family has eventual inertia (n₊(P), n₋(P)+n₀(P), 0). Correction is −B₁₀/K times the exponent-10 weighted Gram; O(c⁻¹) clock shifts give either sign on a nullvector [L]. | Strict leading positivity or second-order clock payment; growing-family uniformity. Nullvector existence is not established; [equality is not a sign certificate](rh-killed-routes.md#critical-pencil-nullspace). |
| Length-2a windows carry level-a Weil index; supremum over windows/K counts distinct right zeros. Fixed conductor packets e≤L, 0<2λL≤π, c_N>0, c_N/N→0: rescaled sum through |γ|≤λN tends κ·poleCoefficient²·Σρ mρ/[ρ(1−ρ)]; pole-free limit0 [L]. | High-zero tail above λN and growing packets; this bulk detects only the pole coefficient. |
| Fixed-conductor second order for 0<c<1; explicit near-Gamma kernel and logarithmic horizon decomposition. For fixed m,l, c≥1, c→∞, c⁴logN/N→0: near-Gram/c→κ·1_(m=l=1), relative subhorizon error O_φ((ml)⁵c⁴logN/N) [L]. Receiving-index logarithmic row/c has the same limit; receiving divisor-jet pairing/c→κ·1_(m=1)Λ(l)/√totient(l). Nonratio pairing splits into interior Mangoldt convolution and exterior O_(m,l)((1+c)²log(4N)/N), 0<c≤N [S]. | Assemble these limits with near-Gamma, center and separated-cross terms into the complete signed critical-clock limit; then growing-conductor/frequency uniformity and high-zero tail. Individual fixed-conductor limits supply no full-space sign. |
| Subcritical conductor blocks have relative Jordan-diagonal control; J(m)/J(1)=#P⁷(ℤ/mℤ) [L]. Critical c⁸/logN→K: some M(N)→∞ gives coefficient-uniform diagonal convergence. Exact E_m(c)=J(m)c⁻⁷R_m(c/m)≥0; count ratio→1 uniformly for m≤M=o(c). Collective squared-residual ratio→0 through N^θ, 0<θ<1/2 [L]. | Prescribed growth rate and complement/cross-term sign. [Bare count approximation fails for m≥Lc](rh-killed-routes.md#conductor-count-resolution); collective quasimodes do not imply a full-matrix lower bound. |
| Large-prime/cofactor norm frames uniform for d≤N^ε, √N<p≤N^θ, θ>1/2, ε≥0, θ+2ε<1 [L]. | Complete-Weil comparison, smaller primes and remaining composite bands. |
| Harmonic-neutral prime charge t, S_Q=Σ_(p≤Q)log p/p: J_N−(t²/S_Q)logN=−t²/2+O(t²/S_Q), uniformly N≥Q; J_Q→t²/2 [K]. Ordinary/harmonic square and actual overlap bounds [L]. Nonzero nonnegative C² profile on [0,1], 1≤c≤N/3, neutral packets F/√n: abs(W(F)−J(F))≤M(F)=Ac²ΣF²/n+Bc³(1+logN)ΣF²/N. For neutral G with ‖G/√n‖₂≤1, mixed remainder²≤(1+Ac²+Bc³(1+logN))M(F). Coherent moment costs vanish below one logarithmic power; mixed dilation pairing is prime-diagonal [S]. | Complete critical-charge energy and normalized mixed-limit specialization/audit; coprime fibres and dilation pairing with the growing complement. The mixed remainder bound compares W with J, not with zero; full-space sign remains open. |
| RH⇔all translation contractions abs(W(τ_εu,v))²≤Q(u)Q(v), from the short-window floor. Either end collar determines a first-critical zero mode. Ordered reflected pairs: Q(f±Rf)=2Q(f)±2C(f), C=Hankel−smoothed prime count; abs(C(f))≤Q(f) iff both pair forms≥0. For ordered collar f and interior y of parity±, Q(f+y±Rf)=2Q(f+y)−Q(y)±2C(f) [L]. | Independent signed fold/prime-count payment, including the subtracted interior energy; frozen interior infimum finiteness/attainment. End-collar uniqueness excludes no mode. [Uniform Tate horizons fail](rh-killed-routes.md#tate-domination). |
| Window sign⇔all fitting lattices; all-lattice positivity⇔RH∧λ=Λ on n≥2; RH⇔no first degeneration. ¬RH gives E₀>0=E₁ for a short generic bump. Positive evolution: collapse iff Σγ_n² diverges. Under RH, continuum corner margin=0, fixed-length dyadic margins→0 and E₁(φ,h)/h²→Σρ mρ γρ² abs(φ̂(γρ))², while E_n(φ,h)/h²→0 for n≥2 [L]. Positive conjugation-closed r-angle data: E_k>0 for k<r, E_r=0 [K]. RH⇔every lattice equals its folded-zero Gram form; finite-zero truncations bound margins below under RH [L]. All-test strict orbit bound⇔two-site positivity⇔RH [L]. | Prove the strict orbit bound from actual Λ data. Frozen-stage branch: attain interior infimum. [Unscaled refinement collapses](rh-killed-routes.md#lattice-positive-slack); rescaled asymptotics assume RH; higher-order Hankel limits remain open. Folded-zero domination assumes RH; it supplies no independent arithmetic sign. [Interior-gap continuation](rh-killed-routes.md#lattice-interior-gap) is not structural. |
| Any nonzero C² profile on [0,1]: positivity on conductor spans≤N^θ, 0<θ<1/1080, through b_φloglog N; every polylog span through Kloglog N, each fixed K. Every subpolynomial span has a cutoff-dependent super-log-log clock [L]. | For general profiles, omitted bands and the receiver's prescribed clock; a cutoff-dependent clock need not reach it. |
| Zero-free logarithmic profile positive through ε₀L(log L)², L=loglog N; its reciprocal-floor budget works iff K≤ε₀ [L]. | Every required multiple; this profile's sign does not transfer to the Beurling profile. |
| One fixed smooth Beurling profile compresses every finite rational Gram at c_N=2L(log L)². Eventual pole-hyperplane sign on this single schedule⇔RH. Smooth nonnegative unit-bump receiver at every positive-power overlap [L]. | Actual sign on the selected profile/schedule. |

Sources:

- **Full matrix / frames:** CACT:TheCompleteWeilMatrixIsPositiveDefiniteBelowTheEighthRoot; CACT:EverySubpolynomialSpanHasASuperLogLogPositivityClock; CAF:LargePrimeCofactorsHaveUniformConductorFrames [L]; CACT:TheCompleteWeilMatrixIsPositiveAtACriticalMultiple; CACT:CriticalMultipleCompleteWeilPositivity; AHD:CompleteWeilCriticalMultipleAndWindowCorollaries [K].
- **Horizon / twists:** AHD:TheWindowIndexCountsTheRightZeros; AHD:TheTwistedDirectionsCarryNoNegativeSquares; AHD:EveryFrequencySectorInheritsThePolarization; AHD:OneCriticalMultiplePaysEveryWindow; AHD:TheCoshHyperplaneInheritsThePolarization; AHD:TheCanonicalCriticalClockEntersFromTheNegativeSide; AHD:TheCriticalBoundaryAddsItsNullDirections; AHD:TheUntwistedCountIsTheFinitePartAtZeroFrequency; AHD:TheBulkIsBlindBelowItsGrid [L]; AHD:TheConductorDecompositionHoldsOnAGrowingRange; AHD:TheCountFormEndsAtTheResolution [L].
- **Bulk second order:** AHD:TheBulkEntriesAreReadByTheStieltjesConstants; AHD:TheCharacterPacketsReadTheLogarithmicDerivative; AHD:TheBulkEntriesAtEveryOverlap; AHD:TheCrossErrorOfTheBulkEntries; AHD:TheRowsOfANearPairSum; AHD:TheArchimedeanKernelOfNearAtoms; CACT:TheLogarithmicRowIsAnIntegralOfHorizons; RAPT:TheGrowingShellCorrectionIsPolar; CACT:TheNearGramRetainsOnlyThePolarConductor [L]; CACT:TheLogarithmicHorizonMeanIsPolar; CACT:TheDivisorJetHasAPolarNearMean; AHD:TheNonRatioPrimesOnConductorPackets [S].
- **Windows:** WTZ:TheAliasingWeightPaysEveryWindow; DZG:TheGroundStateRepresentationOfAStage; ATD:FirstFoldStageDomination; GWZ:TheTwoCollarFormIsBornZero; GWZ:ZeroModesHaveReflectionParity; CSTW:TheFrozenFormInClosedForm; CSTW:WindowGrowthIsATranslationContraction; SWC:OnReflectionPairsTheCouplingIsTheSmoothedPrimeCount [L]; WTZ:TheAliasingNormRetainsTheJointPole; AHD:JointPolePaymentExtendsTheCriticalRatio [K]; SWC:TheCollarHankelForm [S].
- **Receiving charges:** ACPL:ReceivingCharges/PrimeIncidenceDilationEnergy; CSAR:ReceivingCharges/FiniteHorizonPrimeCharge; CSAR:ReceivingCharges/PrimeChargeBoundaryCorrection [K]; CSAR:ReceivingCharges/PrimeChargeMoments; ACPL:ReceivingCharges/NearOverlapMoments [L]; ACPL:ReceivingCharges/CompleteFormMoments; ACPL:ReceivingCharges/CompleteFormMixedMoments; CSAR:ReceivingCharges/PrimeChargeScaleLimits; ACPL:ReceivingCharges/PrimeIncidenceDilationPairing [S].
- **Lattices:** GWZ:AWindowIsTheUnionOfItsLattices; GWZ:TheLatticeSelectsTheVonMangoldtWeight; GWZ:ForbiddingLatticeZeroModesIsRH; GWZ:TheLatticeHasNoSlackUnderRH; GWZ:TheSzegoVerblunskyLaw; GWZ:TheLatticeSchurDataCoalesce; GWZ:GapContinuationIsNotStructural; GWZ:TheFirstMarginIsBornQuadratically [L]; GWZ:ACurveDegeneratesAtItsNumberOfAngles [K]; GWZ:SpecZIsACurveOnEveryLattice [L]; GWZ:RHIsDecidedOnTwoSites; GWZ:TheHigherMarginsAreBornLater [L].
- **Receivers:** SSHA:EveryEighthRootMultipleReceivesTheTiltedSpline; TM:ReceiverRate/SharpLogarithmicOverlapBudget; TM:ReceiverRate/EveryFiniteGramFitsOneCriticalOverlap; RIT:TheHodgeIndexAtCriticalOverlap.

<a id="external-literature"></a>
### Scope guards

- RH-equivalent receivers are proved; their arithmetic positivity/cancellation inputs remain open.
- Finite off-line support is conditional, not established for ζ; it would not imply RH.
- Critical-line census: simple-critical proportion≥0.67250071−ε uses imported Zeta23 plus local IGP. Higher proportions need actual signed prime surplus/moments; model16/21 is not a ζ proportion. [Sub-threshold data, form-factor/pair-density positivity and F≥1 beyond threshold do not force the 75% certificate](rh-killed-routes.md#positivity-three-quarters) [L].
- Fixed aperture/rank/scale and density-one control leave finite or shallow exceptions. No uniform positive ground-energy gap at unbounded aperture.

<a id="pw-b"></a><a id="hb--theta-cusp-hawking-causal-scattering"></a><a id="isc-polar"></a><a id="art"></a><a id="dr"></a>
### Non-route labels

DR: [retired zero-freeness-based root construction](rh-killed-routes.md#dr); regional-root/multiplicity equivalence remains support, not an independent RH mechanism.

PW-B: [retired source-uniform extinction mechanism](rh-killed-routes.md#kr-pwb); surviving critical-line detector feeds PM/scattering. ISC-polar: rational Weyl pole-exclusion branch of PM/HF, not a separate route. BVI/ART: support. [Other killed mechanisms and retired aliases](rh-killed-routes.md).

ADT: conductor degeneration supporting HF/ACS/SC; gluing determinant reformulates MC. AHD: horizon/index receivers within SRT/HF/SC. CWS: window locality/signed folds/index exhaustion within HF/RW/ACS; independent all-window positive realization open. See [shared frontier](#shared-frontier).

WTZ/DZG/ATD: window algebra, Tate jets and signed-count/Doob identities supporting RW/HF/ACS/PM. Bare first-jet domination⇔Weil sign; independent all-aperture domination open. Exact early Tate thresholds; no fixed k>0 works at all apertures. GWZ/CSTW: collar gluing and lattice Schur reformulations supporting RW/AIP; independent source positivity open. SWC: signed-window ground-state programme within RW/OWU; [prime-free Markov negativity](rh-killed-routes.md#prime-free-markov) [S].

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
| TCS | ThetaCuspSections | SWC | SignedWindowCriticality |
