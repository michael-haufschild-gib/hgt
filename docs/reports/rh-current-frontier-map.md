# RH proof-route frontier

**RH open · 32 live routes · 17 candidates.**
**Corpus checkpoint:** `88ceca6a53b0e377473ab1816d04b05adb777425`.

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
| Zero-configuration geometry | — | [ZCG](#zcg) |
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
- **Established:** Exact prime-error/energy criteria; fixed first Chebyshev cyclotomic band has energy abscissa2Θ and O_ε(N^(1+ε))⇔RH. Pole-subtracted prime-source gauge exponents range exactly over [Θ,1], minimized at the trivial gauge; RH⇔minimum1/2 [K].
- **Open:** Actual signed square-root precision / first-band bound. Construct a gauge attaining pole-subtracted exponent1/2; the spectrum identity alone gives no such gauge. [Pole matching does not control finer exponents](rh-killed-routes.md#pole-matching-half-power).
- **Sources:** B:WeilLagCriticalDeficitEndpointAndLimitLaw; CAF:FirstCyclotomicBandAbscissa [L]; AGT:ThePoleSubtractedSpectrumIsAnInterval [K].

<a id="rw"></a>
### RW — Restricted Weil ground energy

- **Path:** Complete Weil form → μ(a)≥0 at every radius → RH.
- **Established:** Form-domain attained, strictly radius-decreasing minima; floor through enlargedWeilFloorAperture>181/500. Exact {∞,2} trace through a=½log3; all-lattice/two-site receivers. Odd/even sign⇔C≤Q/−C≤Q, C=collar Hankel−smoothed prime count. Smooth compact minimizers excluded. Sector sign⇔Hamburger jet moments; full sign⇔Stieltjes moments. Nonnegative windows give positive jet minors and alternating reflection limits [L].
- **Open:** Independent all-test coupling bound paying signed prime folds and interior energy; strictness on smooth tests does not bound the form-domain minimum. Collar-only payment fails at prime3. [Odd](#owu), [shifted-gauge](#act) and [critical-matrix](#shared-frontier) branches retain full signed payment.
- **Sources:** C:TheApertureFlowNeverStalls; I:AnExplicitLargerApertureRetainsAWeilFloor; SP:SemilocalPrimeTwoTrace/IntrinsicWeilTraceAndWindowCorollaries; GWZ:RHIsDecidedOnTwoSites; SWC:WindowEigenfunctionsAreSingularAtTheEdge; SWC:TheSectorsAreTheMomentConditionsOfTheJets; SWC:TheLatticeReflectionCoefficientsAlternateInTheContinuumLimit [L].

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
- **Established:** Half-power/Redheffer and signed damping-continuation receivers; square-root-cutoff short divisor head has bounded pronic energy for each 0<ε<1. Explicit Möbius exponent-1/2 gauge outside every finitely modified Dirichlet/vertical orbit [K]. Sparse-prime transfer bounds [L]; pole-preserving flips have Möbius exponent max(θ,Θ), 0<θ<1 [K].
- **Open:** Half-power cancellation at the actual trivial gauge; uniform signed long-modulus energy for dampings cofinal at0, retaining harmonic tails. Neither the constructed half-power gauge nor [pole matching](rh-killed-routes.md#pole-matching-half-power) supplies arithmetic cancellation.
- **Sources:** R:MobiusHilbertFormEquivalence; ADT:TheMertensFunctionIsAGluingDeterminant; C:SignedAveragedContinuationAndTheZeroWidthBand; C:LongModulusShortEnergy; AGT:AnExplicitPointHasExponentOneHalf [K]; AGT:TheExponentIsInvariantOnSparsePrimeSets [L]; AGT:TheFlipPointsBreakTheMoebiusHalfPowerLaw [K].

<a id="tt"></a>
### TT — Theta-tail and heat–Cassini currents

- **Path:** Theta source → directed covariance/Wold decay or odd Weil sign → RH.
- **Established:** Exact receivers and Φ-Doob identities retaining every reflected-prime term; restricted current signs.
- **Open:** All-test directed covariance or odd/primitive positivity; signed reflected-prime interaction remains.
- **Sources:** R:PaperWoldDirectedCovarianceRH; R:WeilMarkovOddPositivity.

<a id="la"></a>
### LA — Line anchor

- **Path:** Theta source → all-height/all-degree Jensen or heated coefficient sign → RH.
- **Established:** Each fixed Jensen degree eventually real-rooted; quantitative heat/depth bounds and density-one fixed-depth control. Polynomial Laguerre/heat steps preserve root strips; heat steps preserve real-root mesh; shift averages contract squared depth. Loss of reality along a fixed-degree continuous real family requires collision [L]. Finite-degree unit-circle purity exits only through a double trace root or trace ±2 [L].
- **Open:** Uniform signs for actual Ξ at every height/degree; a source-faithful deformation excluding collisions and controlling shallow exceptional windows. Polynomial preservation alone supplies neither.
- **Sources:** R:Jensen/EveryFixedDegreeIsEventuallyRealRooted; R:Heat/TheLocalHeatThreshold; R:XiSliceHeatOrderUniformPositivity; ZCG:HeatStepsNeverShrinkTheMesh; ZCG:ShiftAveragesContractTheDepth; ZCG:RealityLeavesOnlyThroughCollision [L]. ZCG:PurityLeavesOnlyThroughCollision [L].

<a id="tg"></a>
### TG — Topological sub-unit gate

- **Path:** Euler/Gaussian source → nonnegative residual + integer trace<1 → RH.
- **Established:** Winding/index and cubic-transgression identities; exact central-gap receivers.
- **Open:** Matrix-complete positive residual and sub-unit integer trace on every disc, or zero-rate central-gap bound.
- **Sources:** R:FormationAnchoredCubicSpecialization; R:GaussianCentralGapExplicitCriterion.

<a id="hf"></a>
### HF — Positive Hodge form on arithmetic cohomology

- **Path:** Complete arithmetic form ≥0 → Hodge index → RH.
- **Established:** Hodge/Hecke/Riemann–Roch receivers; fixed twisted-sector positivity; small-critical-multiple full-space floor. Every R=c⁸/logN>0: conductors≤⌊(logN)^(13/32)⌋ retain positive diagonal and polar genus. Interior-terminal inverse-energy source concentrates at m=1; on its explicit nontrivial kernel, no packet corrector has positive limiting benefit after division by c [K].
- **Open:** Full signed complement/mixed Schur payment at every R; sharp correction retaining polar genus, larger-conductor transport and complete upward-prime source. Interior-terminal results stay inside the known positivity range. [Shared frontier](#shared-frontier).
- **Sources:** J:TheIndexExit; CACT:CriticalMultipleCompleteWeilPositivity; CACT:TheCriticalLowPacketRetainsItsSignedPolarPart; CACT:LowConductorCorrectorsCannotImproveZeroSourceWindows; AHD:TerminalPolarSourceHasANontrivialKernel [K].

<a id="chmd"></a>
### CHMD — Causal Hyperbolic–Modular Duality

- **Path:** One-sided bounded prime wave or odd Doob half-threshold bound → RH.
- **Established:** Wave/Doob receivers, Haar transport and prime-edge Gamma reserve. In original unit Haar/coarse masses, (full prime−pole)/√Y has operator norm O(exp(−√log Y/92160000)), uniformly over every detail horizon and M≤exp(√log Y/184320000). Same bound for the common-horizon all-prime source; normalized prime matrix approaches one separable pole channel [L].
- **Open:** Either upper or lower boundedness of the unnormalized prime wave, or complete odd sign paying Gamma, potential and infinite-orbit terms. √Y-normalized decay supplies neither bound nor a full-Weil index ceiling.
- **Sources:** R:CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion; R:CHMDOddSectorCriterion; AID:AllDetailPrimePoleCancellation.

<a id="th"></a>
### TH — Theta moment positivity

- **Path:** Signed center-mixed theta jets → all-rank Hankel positivity → RH.
- **Established:** Rank8 positive definite throughout 0<a<1/2; ranks≤N strict on |a−1/2|<c/(1+log(N+1)), fixed c>0. Full native even5 matrix has Gaussian-coordinate floor49/4000 for q=πexp(2x)≥5, including the unique compensation zero; all omitted pairs and tail paid [K]. One fixed cross-load repairs endpoint neighborhoods and a cofinal tail [L]; explicit x≥4 cross-ray [S].
- **Open:** Rank9 integrated sign I₈(a)>0 for every 0<a<1/2; fixed cross-load sign on the remaining compact source interval. Native-ray positivity alone does not pay that interval or give all-rank sign.
- **Sources:** R:ThetaCusp/ThetaCuspCenterMixedSignedJetCompleteness; TCS:StrictEighthSection; TCS:LogarithmicCriticalCollar; TCS:FifthEvenCrossLoadContinuation [L]; TCS:FifthEvenNativeRay [K]; TCS:FifthEvenEffectiveCrossRay [S].

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
- **Established:** Krein positivity⇔RH; on 0<Re s<1/2, Im s>0, actual-core whole-Haar admission⇔Mayer resonance⇔ζ(2s)=0. Height-uniform cusp asymptotics; physical cusp residue=Krein square, Gaussian residue→complete Weil form [K]. Closed reflection, all-determinant Lewis invariance and corrected all-prime transport. Retained T₂ boundary channel is uniquely fixed by L² remainder; its co-isometry defect has sign(1/4−Re s), reversed at the reflected resonance [K].
- **Open:** Arithmetic sign after counterterm subtraction; source-forced extinction/balance of the retained channel, not detection of its side. Mixed-parameter completion, full Mayer transfer/signed-form descent and rational Weyl identification remain. [Bounded reflection](rh-killed-routes.md#cauchy-reflection-order) requires Re s≥1/4.
- **Sources:** RIT:MayerScattering/MayerResonanceCharacterization; RIT:MayerScattering/ClosedCauchyReflection [L]; RIT:MayerScattering/CoreHaarResonanceAdmission; RIT:MayerScattering/AllPrimeBoundaryTransport; RIT:MayerScattering/UniformNormalizedCuspRemainder; RIT:MayerScattering/GaussianPhysicalCuspResidue; RIT:MayerScattering/TheRetainedHeckeChannelReadsTheQuarterLine [K].

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
- **Established:** Weight rigidity; attained aperture-antitone blind minima; local/high-window signs. Even positivity⇔−C≤Q on every smooth half-window test⇔Hamburger moment representation of s_k=W(φ^(k)) for every even bump. Sector sign gives smooth strictness and positive even-jet blocks [L].
- **Open:** Actual all-aperture lower-band bound, including low/mixed modes. [Nonnegative even theta-gauge cosh certificates fail](rh-killed-routes.md#theta-gauge-cosh-defect) [S]; retained variance and signed interactions remain.
- **Sources:** R:EvenSectorPoleWeightUniqueness; R:EvenSectorBlindVariationalAttainment; SWC:TheParitySectorsAreTheBandAtTheCentre; SWC:TheSectorsAreTheMomentConditionsOfTheJets [L].

<a id="gta"></a>
### GTA — Transverse Schur charge

- **Path:** Positive theta-stage Schur charge → rank-uniform transverse decay → RH.
- **Established:** Exact decay criterion; positive charge and strong finite-prefix convergence.
- **Open:** Rank-uniform arithmetic energy decay independent of zero data.
- **Sources:** R:Hedenmalm/HedenmalmThetaSchurQuarticSpectralDecayEquivalence; R:PaperThetaSchurModeCharge.

<a id="owu"></a>
### OWU — Odd Weil-weight uniqueness

- **Path:** Actual odd Weil positivity at every aperture → RH.
- **Established:** Odd RH criterion; prime-free and moment-constrained unit-window floors [K]. Odd positivity⇔C≤Q on half-window tests⇔Hamburger moments of shifted jets s_(k+1) for every even bump [L]. Folded archimedean energy nonnegative for odd half-line-positive gauges; explicit collar payment for each prime kick [L].
- **Open:** Joint Gamma/prime/pole sign at every aperture. Bare collar payment fails at prime3. Variance-dropped shifted-gauge certificates fail for c>273/400 [S]; [retained-variance payment](#act) remains open.
- **Sources:** R:WeilMarkovOddPositivity; WTZ:TheHigherGammaReserveRepairsTheQuadraticCutoff [K]; SWC:TheSectorsAreTheMomentConditionsOfTheJets; SWC:TheOddLightConeInTheDoobGauge; SWC:TheCollarRatioIsSharp [L]; SWC:BelowLogFour/TwoProfileRefutationBelowLogFour [S].

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
- **Established:** Full-family receivers/index exhaustion; controlled-aperture negative tests for depth≥δ without separation. Growing low-block positivity; fixed interior-terminal mixed source exactly polar at every R>0. No packet correction has positive normalized limiting benefit on the source kernel; explicit nonzero kernel tests [K]. ZCG prime pinning/depth identification [L].
- **Open:** Complementary-window sign at every critical ratio; high-zero tail, sharp polar optimization and larger-conductor transport. General-window upward-source pieces [S]; complete mixed assembly remains. [ZCG](#zcg) lacks source-side global rigidity.
- **Sources:** S:ClusterProductHorizon; AHD:TheHorizonCriterion; AHD:TheCompleteCriticalResidueIsSupportedAtThePole; AHD:CriticalWindowsSurviveLowConductorRemoval [K]; ZCG:ThePrimesPinEveryFinitePieceOfZeta; ZCG:ResolutionIsUniformInDepth [L]; [shared frontier](#shared-frontier).

<a id="act"></a>
### ACT — Arithmetic criticality / single-shift variation

- **Path:** One fixed shift pays every even compact C² profile → odd Weil positivity → RH.
- **Established:** Single-shift receiver; collar thresholds pay fixed finite families. For m_a=Φ(·−a)−Φ(·+a), even compact profiles satisfy Ẑ(m_au)=2S_a−D_a+8V_c+8τ_cA₂, V_c≥0, τ_c>0 [L]. Variance-free sum is extension-invariant; explicit two-profile obstruction for c>273/400 [S]. Below c=log2, retained-variance certificates⇔exact {2,3} half-window band [S].
- **Open:** One shift, uniform in profile/support, paying reflected-prime D_a with same-side energy and retained variance/slack. Variance-dropping fails [S]; full retained-variance sign remains open.
- **Sources:** D:ShortProfilePoleFreeVariationInequality; I:ShiftedCollarsHaveExplicitPaymentThresholds; SWC:ShiftedGroundStatesArePoleChargedOnEveryWindow [L]; SWC:BelowLogFour/{TwoProfileRefutationBelowLogFour,RetainedVarianceAndHalfWindowBandBelowLogFour} [S].

<a id="aip"></a>
### AIP — Arithmetic incidence positivity

- **Path:** Prime incidence + plateau gauge → all-aperture global allocation → odd positivity → RH.
- **Established:** Allocation receiver; small-K full-space floor; all-R growing low-block positivity. Exact charge energies, capacity=loglogN+O(1), finite receiving coordinates and completed-diagonal control. At every K>0, harmonic-prime-charge physical complete energy→0 for independently diverging Q,N [K].
- **Open:** Full-space allocation at every K: signed complement, mixed control/growing fibres and complete-energy capacity comparison. Uniform reciprocal covariance [K] and literal logarithmic-kernel variation [L] are available; prime-weighted upward-row assembly remains [S]. Vanishing self-energy does not pay mixed terms.
- **Sources:** I:GlobalIncidenceAllocationCondition; CACT:CriticalMultipleCompleteWeilPositivity; CACT:TheCriticalLowPacketRetainsItsSignedPolarPart; ACPL:ReceivingCharges/PrimeIncidenceCapacityGrowth [K]; [receiving-charge frontier](#shared-frontier).

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
| <a id="lattice-sections"></a><a id="acs"></a>**ACS — Arithmetic Castelnuovo–Severi effectivity:** arithmetic effectivity / Rosati heights → Hodge index → RH. | Effectivity/count-height receivers, primitive h¹=Q/2, pure-curve calibration. Integral/window Rosati and Jacobi–Hurwitz degree-zero rigidity [L]. All-R growing low block [K]. Full Selberg class: degree gap (0,1), d<1 Dirichlet unit; normalized degree1 has conductor≥2 or a pole [K]. | Arithmetic height comparison producing all-aperture primitive effectivity. Generic rigidity and finite-curve calibrations do not supply it; [same-window Hecke similitudes are scalar](rh-killed-routes.md#window-reflection-centralizer). Selberg selection needs periodicity, integer conductor and primitive-character identification. | G:ExactArithmeticSourceEffectivity; AHD:DegenerationSelectsThePureCurves; KPA:{IntegralRosatiFormsOfDegreeZero,JacobiHurwitzHeightsOfDegreeZero,TheQuinticCurveCalibratesTheEffectivityCalculus} [L]; SEL:GammaIndependentEulerRigidity; SEL:DegreeGap; SEL:DegreeOneConductorPole [K] |
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
| <a id="w1c"></a>**W1C — Clifford–Dirac / centred Lee–Yang:** arithmetic operator or ferromagnetic limit → real-rooted Ξ. | Lee–Yang/Ising receiver; faithful Haar realization, closed reflection, all-determinant Lewis invariance and corrected all-prime transport; actual-core Haar admission⇔resonance [K]; physical Krein/Gaussian residues and height-uniform cusp remainder; retained Hecke channel detects the resonance side of Re s=1/4 [K]: [PM](#pm). | Source-defined Ising couplings with centred slow-field convergence, or positive arithmetic reflection form with self-adjoint generator. Admission/transport do not give [Krein positivity](rh-killed-routes.md#mayer-krein-sign). | R:LeeYangIsingGraphDatum; R:IsingLawConvergenceRH; RIT:MayerScattering/ClosedCauchyReflection; RIT:MayerScattering/AllPrimeBoundaryTransport; RIT:MayerScattering/CoreHaarResonanceAdmission [K] |
| <a id="wbf"></a>**WBF — Source certificates:** arithmetic stream → depth-uniform positive completion → Ξ. | Abstract genealogy Gram/Fredholm recovery and relative determinants; no arithmetic coupling. | Arithmetic certificate stream and source-faithful uniform-depth completion landing on Ξ/Weil positivity. | H:PaperGenealogyFredholmRecovery; H:PaperCriticalGenealogyCompletion |
| <a id="zcg"></a>**ZCG — Zero-configuration geometry:** prime image → configuration rigidity / collision control → RH. | Prime pinning; isolable-cluster identification, including finite exceptions over perturbed-lattice backgrounds at a>πD [L]. Shallow configurations identified at separation g>π/(2a); equality admits mimics [L]. On-line difference density D<2a/π suffices without separation [S]. Finite degree-g trace model: g readings identify; purity⇔all-order bounded image; integral roots collide or quantitatively repel [L]. Finite Euler-stage zeros simple/separated above an X-dependent horizon [L]. | Source-side purity for actual ζ, including arbitrarily close infinite clusters. Identification constructs no on-line match; finite-model bounds and stage repulsion need a faithful horizon-uniform passage to ζ. | ZCG:ThePrimesPinEveryFinitePieceOfZeta; ZCG:IsolationIdentifiesTheCluster; ZCG:ShallowConfigurationsAreResolvedAtTheInghamScale; ZCG:BoundedImagesCertifyPurity; ZCG:IntegralConfigurationsRepel; ZCG:EulerStagesRepelAboveTheHorizon [L]; ZCG:SparseOnLineClustersNeverCancel [S] |

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
| Tilted-spline critical pencil=κWeil+(7J/R)weighted Gram, R=lim c⁸/logN. Exact aperture threshold R_A is antitone in A: every nonzero fixed test is eventually positive for R<R_A; R>R_A admits a negative window. R_A=∞ through the enlarged short-window floor; RH⇔R_A=∞ at every aperture [K]. Existing weighted floors give a positive aperture-independent lower bound. | Prove unbounded compensated ratios for each fixed test, or full-space sign at every K. A bounded threshold improvement does not remove aliasing. |
| Exact clock c⁸=Klog N: each fixed independent family has eventual inertia (n₊(P), n₋(P)+n₀(P), 0). Correction is −B₁₀/K times the exponent-10 weighted Gram; O(c⁻¹) clock shifts give either sign on a nullvector [L]. | Strict leading positivity or second-order clock payment; growing-family uniformity. Nullvector existence is not established; [equality is not a sign certificate](rh-killed-routes.md#critical-pencil-nullspace). |
| Length-2a windows carry level-a Weil index; supremum over windows/K counts distinct right zeros. Fixed conductor packets e≤L, 0<2λL≤π, c_N>0, c_N/N→0: rescaled sum through |γ|≤λN tends κ·poleCoefficient²·Σρ mρ/[ρ(1−ρ)]; pole-free limit0 [L]. | High-zero tail above λN and growing packets; this bulk detects only the pole coefficient. |
| Complete fixed-conductor residual: (logN/c)⟨W_Nv_m−E_m(c)v_m,v_l⟩→κ(2+γ−log(4π))·1_(m=l=1), c⁸/logN→R>0. Rescaled tilted-spline Gram=positive Jordan diagonal+positive polar genus [K]. | Fixed-conductor limits do not control complementary windows or moving frequencies. |
| Tilted spline, every R>0: Q=⌊(logN)^(13/32)⌋, y=Σ_(m≤Q)b_mv_m; W_N[y]=ΣE_m b_m²+κ(2+γ−log(4π))(c/logN)b₁²+o(ΣE_m b_m²), uniformly in b. Hence W_N[y]≥½ΣE_m b_m² eventually [K]. | Intermediate/far bands and mixed Schur payment. Orthogonal removal of this entire block preserves the compensated window limit [K]; interior-terminal inverse-energy sources are controlled below. [Full-horizon reference-energy floors fail](rh-killed-routes.md#full-conductor-diagonal), even for b_m≥0 [K]. |
| Large-prime/cofactor norm frames uniform for d≤N^ε, √N<p≤N^θ, θ>1/2, ε≥0, θ+2ε<1 [L]. | Complete-Weil comparison, smaller primes and remaining composite bands. |
| At c=2K(logN)^(1/8), nonnegative C² atom, Q=X^a,N=X^d, 0<a≤d: charge t has raw energy→t²(d/a−1/2), vanishing adjunction/norm/physical energy; fixed-fibre and complete-minus-jump laws [K]. Tilted spline, charges1..M, Q=M!X²,N=X⁴⁰: raw energy→(39/2)Σt_m², terminal pairing→t_l/80 (0 for l>M), physical energy→0 [S]. | Uniform mixed control/growing fibres. These receiving contrasts have log-width 2logX, outside the fixed compact terminal-profile theorem. |
| Scalar prime-charge complement is asymptotic to an explicit logarithmic ramp. At Q=X²,N=X⁴⁰, an orthogonal terminal receiver r has ⟨Wv,r⟩→t/80, W[r]/logN→1/20, and source–receiver determinant→6239t²/6400>0 for t≠0 [K]. Balanced terminal contrasts retain endpoint cancellation and small low-conductor projections after multiplication by each fixed conductor [K]. | Uniform vanishing of all complementary pairings is false; this two-dimensional span is eventually positive. Pay the full complement, not just its coupling or source norm. |
| Exact capacity Cap_N=loglogN+O(1); minimum dilation energy=t²/Cap_N. Harmonic-prime-charge complete physical energy→0 as Q,N→∞ independently, every K>0 [K]. Reciprocal residue covariance has modulus-uniform discrepancy bounds [K]; literal logarithmic-offset kernels have scale-uniform variation [L]. | Complete-energy capacity comparison and prime-weighted mixed payment. Finite offset/normalization and weighted progression bounds [S] are not the assembled upward-row law. [Raw-cost charge control fails](rh-killed-routes.md#prime-pole-cost). |
| Terminal F supported strictly inside (1/2,1), every R=c⁸/logN>0: complete fixed-conductor mixed source S(F) is polar; all nonpolar limits vanish. Pole correction gains S(F)²/(J₁/R+κg), g=2+γ−log(4π) [K]. | Log-support length<log2 lies inside the known positive floor; this does not enlarge it. Larger apertures retain an upward-prime source. Terminal boundary mass is controlled [K]; model/Riemann-sum assembly [S], full general-window transport and growing-packet uniformity remain. |
| Interior-terminal F, R>0, Q=⌊(logN)^(13/32)⌋: inverse-energy source mass→S(F)²R/J₁, nonpolar mass→0. Gain/c≤2S(F)²R/J₁+o(1); on ker S, no positive limiting gain, even for unbounded coefficients. Explicit nonzero kernel tests [K]. | Sharp full-packet optimization retaining polar genus; larger-conductor source control. Long-index near-row cancellation [S] alone does not assemble complete mixed transport. |
| RH⇔all translation contractions from the short-window floor. Odd/even signs⇔C≤Q/−C≤Q. No nonzero smooth compact window eigenfunction/minimizer; window nonnegativity forces strict smooth band abs(C)<Q [L]. Collar Hankel has arbitrarily large negative-definite subspaces [L]. | Independent signed band bound; form-domain minimizers need not be smooth. Neither smooth strictness nor collar compactness gives all-window positivity or a uniform gap. [Collar-only payment fails](rh-killed-routes.md#collar-local-payment). |
| Window sign⇔all fitting lattices; all-lattice positivity⇔RH∧λ=Λ. For every even bump, s_k=W(φ^(k)): even/odd sign⇔Hamburger moments of s_k/s_(k+1); full sign⇔Stieltjes moments [L]. Nonnegative windows give positive jet minors, γ_n(h)→(−1)^n and positive h²-scaled reflection defects [L]. | Construct the actual positive measures / all-aperture signed band. Below c=log2, exact {2,3} band and retained-variance equivalents [S] still require sign; [variance-dropped gauges fail](rh-killed-routes.md#variance-dropped-theta-gauge). |
| Any nonzero C² profile on [0,1]: positivity on conductor spans≤N^θ, 0<θ<1/1080, through b_φloglog N; every polylog span through Kloglog N, each fixed K. Every subpolynomial span has a cutoff-dependent super-log-log clock [L]. | For general profiles, omitted bands and the receiver's prescribed clock; a cutoff-dependent clock need not reach it. |
| Zero-free logarithmic profile positive through ε₀L(log L)², L=loglog N; its reciprocal-floor budget works iff K≤ε₀ [L]. | Every required multiple; this profile's sign does not transfer to the Beurling profile. |
| One fixed smooth Beurling profile compresses every finite rational Gram at c_N=2L(log L)². Eventual pole-hyperplane sign on this single schedule⇔RH. Smooth nonnegative unit-bump receiver at every positive-power overlap [L]. | Actual sign on the selected profile/schedule. |

Sources:

- **Full matrix / frames:** CACT:TheCompleteWeilMatrixIsPositiveDefiniteBelowTheEighthRoot; CACT:EverySubpolynomialSpanHasASuperLogLogPositivityClock; CAF:LargePrimeCofactorsHaveUniformConductorFrames [L]; CACT:TheCompleteWeilMatrixIsPositiveAtACriticalMultiple; CACT:CriticalMultipleCompleteWeilPositivity; AHD:CompleteWeilCriticalMultipleAndWindowCorollaries [K].
- **Horizon / twists:** AHD:TheWindowIndexCountsTheRightZeros; AHD:TheTwistedDirectionsCarryNoNegativeSquares; AHD:EveryFrequencySectorInheritsThePolarization; AHD:OneCriticalMultiplePaysEveryWindow; AHD:TheCoshHyperplaneInheritsThePolarization; AHD:TheCanonicalCriticalClockEntersFromTheNegativeSide; AHD:TheCriticalBoundaryAddsItsNullDirections; AHD:TheUntwistedCountIsTheFinitePartAtZeroFrequency; AHD:TheBulkIsBlindBelowItsGrid [L]; AHD:TheConductorDecompositionHoldsOnAGrowingRange; AHD:TheCountFormEndsAtTheResolution [L].
- **Signed critical / low block:** AHD:TheCompleteCriticalResidueIsSupportedAtThePole; AHD:TheBulkEntriesAlongAGrowingOverlap; ADT:TheCriticalConductorFormRetainsThePolarGenus; CACT:TheCriticalLowPacketRetainsItsSignedPolarPart; AHD:CriticalWindowsSurviveLowConductorRemoval; AHD:TheCriticalThresholdOfAWindow [K].
- **Windows:** SWC:TheParitySectorsAreTheBandAtTheCentre; SWC:WindowEigenfunctionsAreSingularAtTheEdge; SWC:TheJetMinorsArePositiveOnEveryNonnegativeWindow; SWC:TheSectorsAreTheMomentConditionsOfTheJets; SWC:TheLatticeReflectionCoefficientsAlternateInTheContinuumLimit [L]. SWC:BelowLogFour/RetainedVarianceAndHalfWindowBandBelowLogFour [S].
- **Terminal sources:** CACT:TerminalConductorSourcesConcentrateAtThePole; CACT:LowConductorCorrectorsCannotImproveZeroSourceWindows; CACT:TheFullConductorDiagonalOverpricesTerminalWindows; AHD:ThePoleCorrectorRetainsItsSignedWindowBenefit; AHD:TerminalPolarSourceHasANontrivialKernel; AHD:TerminalPrimeBoundaryMassHasFiniteSupport [K]. AHD:TerminalNearRowsCancelAlongTheLongIndex; AHD:TerminalUpwardRowReplacementDisappears; AHD:TerminalUpwardShellsHaveTheirPolarMean; AHD:TerminalPrimeMeansAreFiniteRiemannSums [S].
- **Receiving charges:** CSAR:ReceivingCharges/{CoprimePrimeChargeCompleteEnergy,PrimeChargeComplementProfile,FixedChargeJordanLimit,CommonPrimeFibrePackets,PrimeChargeUniformHorizonEnergy,CoprimePrimeChargeWindowScales}; V:Sieve/WeightedResidueCovariance [K]. V:Sieve/LogarithmicKernelVariation [L]. CSAR:ReceivingCharges/SimultaneousCompleteReceivingLaw; CACT:ReceivingCharges/UpwardProfileNormalization; V:Sieve/WeightedPrimeProgressions [S].
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

WTZ/DZG/ATD: window algebra, Tate jets and signed-count/Doob identities supporting RW/HF/ACS/PM. Bare first-jet domination⇔Weil sign; independent all-aperture domination open. Exact early Tate thresholds; no fixed k>0 works at all apertures. GWZ/CSTW: collar gluing and lattice Schur reformulations supporting RW/AIP; independent source positivity open. SWC: signed-window ground-state and half-window band identities within RW/EWU/OWU/ACT; independent complete band sign remains open.

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
| ZCG | ZeroConfigurationGeometry | KPA | KodairaParshinAbc |
