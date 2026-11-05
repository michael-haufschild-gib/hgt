# RH proof-route frontier

**RH open · 32 live routes · 17 candidates.**
**Corpus checkpoint:** `95145d4992fcc874816c4784dceb5326624fa8f6`.

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
- **Established:** Attained strictly decreasing minima; positive apertures=[0,a*]. Strictly increasing a_k carries floor1/(20000·2^k), a₀>181/500, retaining entering prime powers. Precontact Hermite–Biehler kernels and bounded Riesz vectors; finite contact forces diagonal-kernel blowup. Reference logarithmic form: domain=range W, q(Wf,Wg)=⟨f,g⟩, unique L²-forced inverse WW* with explicit overlap kernel [L]. All-lattice/two-site receivers [L]; exact {2,3} band below log2 [K].
- **Open:** Actual Weil-Riesz boundary traces and global multiplier-domain admission; arithmetic kernel bound uniform up to contact, or all-aperture signed payment. Increasing a_k need not exhaust apertures. [Prime-entry margins](#prime-entry), [EWU](#ewu), [OWU](#owu), [ACT](#act).
- **Sources:** C:TheApertureFlowNeverStalls; I:MultiPrimeDilationModulusAndIteratedWeilFloors; CSTW:{TheWeilFormIsCompleteBeforeContact,TheLocalWeilKernelIsHermiteBiehler,TheWeilKernelDivergesAtContact,TheWeilRieszEquationIsALogarithmicDirichletEquation,TheHalfLineLogarithmicFormHasItsActualInverse,TheHalfLineLogarithmicGreenKernelIsExplicit}; GWZ:RHIsDecidedOnTwoSites [L]; SWC:BelowLogFour/RetainedVarianceAndHalfWindowBandBelowLogFour [K].

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
- **Established:** Exact receivers; explicit H(k)=explicitPrimeArchHausdorffShift k gives Hausdorff-row nonnegativity for every r≥H(k). RH⇔nonnegativity for every k and r<H(k) [L].
- **Open:** Arithmetic sign on those initial segments, uniformly over unbounded k. Finite per row is not a finite RH certificate.
- **Sources:** R:PrimeArchEndpointFrequencyAccretivity; S:EffectiveHorizons/{HausdorffShifts,XiZeroMass} [L].

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

- **Path:** Theta source → collision-free heat descent / Jensen-root imaginary-part control → RH.
- **Established:** RH⇔infinitely many unshifted Ξ Jensen degrees real-rooted⇔every positive-time H_t zero simple. For 0<t≤1/8, zeros with abs(Re z)≥2πexp((6600/9991+ε)/t) are real/simple. For every fixed finite Möbius mollifier, σ>0 and phase: RH⇔uniform upper imaginary-root bound along infinitely many reversed Jensen degrees⇔sublinear bounds; ¬RH forces a root with Im≥κd eventually. Arbitrarily many real Jensen roots occur eventually, unconditionally [L].
- **Open:** Actual sublinear Jensen-root bound, or collision exclusion below the sub-Weyl horizon and at bounded heights. Fixed-degree reality and growing real-root counts give no all-root control; [uniform strict stability margin fails](rh-killed-routes.md#xi-stability-margin) [L]. Positive-time bounds do not reach t=0; [size-only models still collide](rh-killed-routes.md#heat-method-floor). [ZCG](#zcg): local arithmetic input.
- **Sources:** R:Jensen/EveryFixedDegreeIsEventuallyRealRooted; R:XiSliceHeatOrderUniformPositivity; R:Heat/TheLocalDeBruijnNewmanConstant; R:DeBruijnNewmanCollisionCriterion; ZCG:HeatScaleRepulsion/{SubWeylCollisionFreeHorizon,SymmetricHalfCollisionLaw}; FFP:{MollifiedJensenCriterion,BoundedImaginaryPartsCriterion,ImaginaryPartDichotomy,FiniteFreeHardyTheorem} [L].

<a id="tg"></a>
### TG — Topological sub-unit gate

- **Path:** Euler/Gaussian source → nonnegative residual + integer trace<1 → RH.
- **Established:** Winding/index and cubic-transgression identities; exact central-gap receivers.
- **Open:** Matrix-complete positive residual and sub-unit integer trace on every disc, or zero-rate central-gap bound.
- **Sources:** R:FormationAnchoredCubicSpecialization; R:GaussianCentralGapExplicitCriterion.

<a id="hf"></a>
### HF — Positive Hodge form on arithmetic cohomology

- **Path:** Complete arithmetic form ≥0 → Hodge index → RH.
- **Established:** Hodge/Hecke/Riemann–Roch receivers; small-critical-multiple full-space floor. Every R>0: positive fixed-family pencil on A≤2a_k from [RW](#rw); complete mean-zero periodic joint Gram eventually PD iff joint spatial/twist independence. Prime2 Dirichlet-shift corrections stabilize modified tests at every aperture/ratio [L]. Conductors≤⌊(logN)^(13/32)⌋ retain positive diagonal/polar genus; optimal terminal correction is pole-attained, zero on ker S_A [K].
- **Open:** Full signed complement at every R; source-kernel window control and larger-conductor transport. Existing far-complement estimate still loses O(c) against its O(logN/c⁷) reserve. [Shared frontier](#shared-frontier).
- **Sources:** J:TheIndexExit; CACT:CriticalMultipleCompleteWeilPositivity; CACT:TheCriticalLowPacketRetainsItsSignedPolarPart; CACT:EveryLowPacketCorrectionHasItsPolarCapacity; AHD:TerminalPolarSourceHasANontrivialKernel [K]; AHD:{EveryCriticalRatioIsPositiveOnALargerWindow,MultiplicativeConvolutionHorizonAndTailCancellation,JointPeriodicWindowsInheritThePolarization} [L].

<a id="chmd"></a>
### CHMD — Causal Hyperbolic–Modular Duality

- **Path:** One-sided bounded prime wave or odd Doob half-threshold bound → RH.
- **Established:** Wave/Doob receivers, Haar transport and prime-edge Gamma reserve. In original unit Haar/coarse masses, (full prime−pole)/√Y has operator norm O(exp(−√log Y/92160000)), uniformly over every detail horizon and M≤exp(√log Y/184320000). Same bound for the common-horizon all-prime source; normalized prime matrix approaches one separable pole channel [L].
- **Open:** Either upper or lower boundedness of the unnormalized prime wave, or complete odd sign paying Gamma, potential and infinite-orbit terms. √Y-normalized decay supplies neither bound nor a full-Weil index ceiling.
- **Sources:** R:CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion; R:CHMDOddSectorCriterion; AID:AllDetailPrimePoleCancellation.

<a id="th"></a>
### TH — Theta moment positivity

- **Path:** Signed center-mixed theta jets → all-rank Hankel positivity → RH.
- **Established:** Rank8 positive for 0<a<1/2; ranks≤N strict on |a−1/2|<c/(1+log(N+1)) [K]. Truncated quartic positive for q≥7, false at q=6; exact scale-six capacity τ(a)<350/417. Literal first atom plus both ordered (1,2) cross terms has positive-definite fifth-even tail matrix for every cutoff r≥0, retaining gamma reserve [L].
- **Open:** Pay remaining unequal pairs and infinite remainder in a fixed tail quadratic form, including compact scales. Then rank9 I₈(a)>0 and all ranks. [Full quartic repair fails](rh-killed-routes.md#theta-fixed-cross-load).
- **Sources:** R:ThetaCusp/ThetaCuspCenterMixedSignedJetCompleteness; TCS:{StrictEighthSection,LogarithmicCriticalCollar} [K]; TCS:{FifthEvenTruncatedQuarticUpperRay,FifthEvenScaleSixApertureCapacity,FifthEvenFourAtomRemainder,FifthEvenLeadingTail} [L].

<a id="rn"></a>
### RN — Theta renewal and singular comparison

- **Path:** Theta renewal source → divisor-faithful winding/boundary-work sign → RH.
- **Established:** Green/BV realization; compact cone-positive renewal operator with exact determinant/resonances.
- **Open:** Directed mixed prime+Gamma≥pole, including cusp/seam terms. Cone positivity alone does not give real spectrum.
- **Sources:** R:ThetaRenewalPositiveFredholm; R:ThetaRenewalFredholmSpectrum.

<a id="heat-charge"></a><a id="log-scale-defect"></a><a id="mollified-corridor"></a><a id="wd"></a>
### WD — Ward orientation and horizontal collision

- **Path:** Source current/window energy → collision charge<2 or all-resolution sectoriality → RH.
- **Established:** Attained extremizers; collision/index and Laplace-depth receivers. Boundary-regular finite-theta windows: bounded P₊⇔line purity; [unweighted L²⇔empty window](rh-killed-routes.md#window-port-l2). Inner-cap flux=off-line exponential source+bounded source−L² left port; all-polynomial-stage cancellation⇔RH. Vinogradov–Korobov caps improve the outer exponent with square-root prefix retained. Almost-all log-stage certificates⇔log-free unit occupancy [L].
- **Open:** Independent zero-rate right-port bound through inner caps and finite/shallow exceptions, with prefix-limit control. Density branch: thin nonempty Planck shadows occupy ≤η(A)V unit windows eventually in V, η(A)→0 as A→∞, plus compatible vanishing cluster tail; volume/second-moment bounds do not pay them. [Density separations](rh-killed-routes.md#window-density-separation).
- **Sources:** CDG:LogScaleHeckeDefect/UnitWindowMinimumAndOscillation; CDG:SzegoCollision/{WindowEnergyLaplace,LogStageBesselCertificate}; CDG:WindowPortFlux/{InnerCapSourceIdentityAndStageCancellation,VinogradovKorobovCapsAndStageReceivers,RightHalfPortCriticalLineControl}; CDG:NearLineLogMean/{NearLineDensityBesselCertificateAndSeparation,ShortShellSecondMomentAndPlanckBridge} [L].

<a id="li"></a>
### LI — Paired Li and prime–Gamma balances

- **Path:** Prime−Gamma history floor / theta-clock first-zero budget → RH.
- **Established:** Guarded history-zero set Z_S finite; RH iff Z_S=∅. RH⇔Cayley–Li ladders nonpositive on primitive vectors⇔actual clock primitive eventually bounded below [L].
- **Open:** Pay outside budget at every guarded zero, prove primitive lower bound, or Cayley–Li sign. Finiteness of Z_S is not finite off-line ζ support.
- **Sources:** R:LiEvenCrossActualClockTerminalHistory; R:LiEvenCrossActualClockGrowthLaw; R:LiEvenCrossActualClockPrimitiveNegative; ALG:RHIsReflectionPositivityOfTheCayleyLadder [L].

<a id="sz"></a>
### SZ — Suzuki screw and shifted-kernel limits

- **Path:** Complete rectangular Ward defect bounded below at one positive width → RH.
- **Established:** Exact lower-bound receiver; finite reflected-current/light-cone Gram identities. Literal first variation=complete Weil energy on compact Lipschitz sources; RH⇔nonnegative limit/no linear overshoot on factorial/grid-tent families [L].
- **Open:** Complete first-variation sign, or rectangular lower bound after assembling negative-light, Gamma, boundary and mixed costs; bare-source boundedness is insufficient.
- **Sources:** R:Suzuki/{SuzukiRectangularWardDefectBoundedness,SuzukiWallFieldLightConeKernelCompletion,SuzukiCriticalRHCompleteFamilyTransfer} [L].

<a id="fzz-p--parity-delay-mellin-orientation"></a><a id="gauss-mayer"></a><a id="pm"></a>
### PM — Physical-model Haar approximation (FZZ-P)

- **Path:** Faithful scattering source → Krein/Lewis positivity or pole/escape exclusion → RH.
- **Established:** Krein positivity⇔RH; for 0<Re s<1/2, Im s>0, actual-core Haar admission⇔ζ(2s)=0. Physical cusp residue=Krein square; Gaussian residue→complete Weil form [K]. Corrected all-prime transport gives resonant D_s=−‖T_pψ_s‖²/|1+p^(1−2s)|²≤0, with equality iff Re s=1/4 [L]. Retained-channel defect reverses sign under reflection [K]; full D_s is negative on both off-line partners [L].
- **Open:** Independent arithmetic D_s≥0, equivalently extinction, or complete renormalized Krein positivity. Positive raw norms cannot supply this sign; [critical resonances already refute their identification with D_s](rh-killed-routes.md#mayer-krein-sign). Mixed-parameter completion and full signed-form descent remain.
- **Sources:** RIT:MayerScattering/{MayerResonanceCharacterization,ClosedCauchyReflection,ArithmeticDefectObstructionAndReflectedCuspLaw} [L]; RIT:MayerScattering/{CoreHaarResonanceAdmission,AllPrimeBoundaryTransport,GaussianPhysicalCuspResidue,TheRetainedHeckeChannelReadsTheQuarterLine} [K].

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
- **Established:** Heat explicit formula and two-grid RH criterion [L]. Absolute heat mass≤6/h; pole-annihilating detector has explicit degree from the finite outer sampled spectrum, at every odd offset [S].
- **Open:** Actual signs at every degree/height, or one-sided vertical bound. Detector degree depends on spectral separation; two-grid non-aliasing supplies no uniform finite sign certificate.
- **Sources:** R:XiGaussianHeatTwoPrimeSourceSampling; R:HeatGridAliasingBoundary [L]; S:EffectiveHorizons/{TraceHankelDegrees,HeatGridDegrees} [S].

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
- **Established:** Weight rigidity; attained blind minima; even sign⇔−C≤Q⇔Hamburger moments. Neutral signed gauge reduces sign to jump energy≥2·charge variance. Pole-neutral difference is pocket-location invariant; sending pockets to infinity conserves the exact outside deficit. Even continuous kernel is sign-gauge balanced iff c≤logρ, ρ³=ρ+1 [L].
- **Open:** Pay variance with complete signed jumps at every aperture; outside-window negative conductances remain. No sign gauge removes frustration above logρ. Perron branch still needs saturation-gap/height control; [entry transfer](#prime-entry) still needs a margin.
- **Sources:** R:{EvenSectorPoleWeightUniqueness,EvenSectorBlindVariationalAttainment}; SWC:{TheParitySectorsAreTheBandAtTheCentre,NeutralThetaGaugeOptimizationAndPrimeFourSliverFrontier}; SWC:PerronSignLaw/ThePerronMarginIsBoundedByThePoleSaturationGap; FADF:{SignedThetaGaugesReverseTheEvenDeficit,FrustrationCannotBeSwitchedAway} [L].

<a id="gta"></a>
### GTA — Transverse Schur charge

- **Path:** Positive theta-stage Schur charge → rank-uniform transverse decay → RH.
- **Established:** Exact decay criterion; positive charge and strong finite-prefix convergence.
- **Open:** Rank-uniform arithmetic energy decay independent of zero data.
- **Sources:** R:Hedenmalm/HedenmalmThetaSchurQuarticSpectralDecayEquivalence; R:PaperThetaSchurModeCharge.

<a id="owu"></a>
### OWU — Odd Weil-weight uniqueness

- **Path:** Actual odd Weil positivity at every aperture → RH.
- **Established:** Odd RH criterion; prime-free and moment-constrained unit-window floors [K]. Odd sign⇔C≤Q⇔shifted-jet Hamburger moments. Trivial-zero squares split exactly into reflected Dirichlet energy minus mirror killing; mirror killing is paid by the Lévy edge energy. No sign gauge removes an acting negative prime antidiagonal [L].
- **Open:** Joint Gamma/prime/pole sign at every aperture. [Prime3](#prime-entry): collar-mass replacement fails for c≥287/500; deleting its signed term gives a negative odd test for c≥3/5 [L]. Outward-edge bounds still need a sector margin. Variance-dropped certificates fail for c>273/400 [K]; [retained-variance payment](#act) remains open.
- **Sources:** R:WeilMarkovOddPositivity; WTZ:TheHigherGammaReserveRepairsTheQuadraticCutoff [K]; FADF:{TheCentreReflectsTheTrivialZeros,FrustrationCannotBeSwitchedAway}; SWC:{TheSectorsAreTheMomentConditionsOfTheJets,TheCollarRatioIsSharp} [L]; SWC:BelowLogFour/TwoProfileRefutationBelowLogFour [K].

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
- **Established:** Full-family/index receivers; terminal correction pole-attained, zero on a nontrivial kernel [K]. N(t,t+1]≤240log(abs(t)+3) gives explicit all-height/depth negative-test horizons without separation/simplicity. Symmetric ξ mass has explicit relative-error heights, including zero ordinates. Complex two-bump amplitudes retained; tight k-point models share k·pairEnergy≤L. Split-column receiver a>πD_on+πD_off/2; closed-contact depth receiver [L].
- **Open:** Complementary-window sign, high-zero tail and source-kernel payment at every critical ratio; literal Gamma/full mixed assembly beyond logarithmic packets. Short floor does not reach the contact/cluster receivers; column/lattice structure is not established for ζ. [Mixed columns forbid the universal πD/2 shortcut](rh-killed-routes.md#mixed-column-threshold); [finite-aperture models remain blind](rh-killed-routes.md#kr-crt).
- **Sources:** S:AnExplicitClusterDetectorConstant; S:EffectiveHorizons/XiZeroMass [L]; AHD:{TheHorizonCriterion,TheCompleteCriticalResidueIsSupportedAtThePole,CriticalWindowsSurviveLowConductorRemoval} [K]; S:EvenAndOddTwoBumpTestsDecideTheCriticalLine; [distinct-cluster threshold](../../formal/GaloisForLFunctions/WindowVisibilityLaw/DistinctCoherentClustersHaveTheMultiplicityThreshold.lean), [split-column laws](../../formal/GaloisForLFunctions/WindowVisibilityLaw/SplitColumnThresholdAndPerturbedFragility.lean), [contact laws](../../formal/GaloisForLFunctions/WindowVisibilityLaw/ShallowClusterExclusionAndTaperedCrystalBarrier.lean) [L]; [shared frontier](#shared-frontier).

<a id="act"></a>
### ACT — Arithmetic criticality / single-shift variation

- **Path:** One fixed shift pays every even compact C² profile → odd Weil positivity → RH.
- **Established:** Single-shift receiver; Ẑ(m_au)=2S_a−D_a+8V_c+8τ_cA₂, V_c≥0, τ_c>0. Joint neutral-even/retained-odd certificate⇔reflection band; for2c<log5 only {2,3,4} can enter. Their outward kicks cost<991/1000 of Lévy energy; full reflected-pair floor1/(20000·2^k) holds through a_k from [RW](#rw) [L]. Variance-free certificates fail for c>273/400 [K].
- **Open:** One shift, uniform in profile/support, paying reflected-prime D_a with same-side energy and retained variance/slack. Actual-weight band membership remains open; [prime-entry transfer](#prime-entry) assumes, rather than supplies, a sector margin. Variance-dropping fails [K].
- **Sources:** D:ShortProfilePoleFreeVariationInequality; I:ShiftedCollarsHaveExplicitPaymentThresholds; SWC:{ShiftedGroundStatesArePoleChargedOnEveryWindow,NeutralThetaGaugeOptimizationAndPrimeFourSliverFrontier} [L]; SWC:BelowLogFour/{TwoProfileRefutationBelowLogFour,RetainedVarianceAndHalfWindowBandBelowLogFour} [K].

<a id="aip"></a>
### AIP — Arithmetic incidence positivity

- **Path:** Prime incidence + plateau gauge → all-aperture global allocation → odd positivity → RH.
- **Established:** Allocation receiver; small-K full-space floor; all-R growing low-block positivity. Capacity=loglogN+O(1) [K]. At each K>0, one monotone R(X)→∞ receives every unit-bounded charge vector uniformly: exact neutrality/charges, physical energy→0, complementary pairings→t_l/80, conductor cutoff R(X)!X²≤X³, horizon X⁴⁰. Arbitrary fixed charge profiles admit profile-dependent growing cutoffs [L].
- **Open:** Effective growth on RH-complete schedules and full complementary Schur/four-channel payment at every K, including small/offset-dividing primes. Existential growing cutoffs do not supply those bounds. [Raw/physical charge-cost bounds fail](rh-killed-routes.md#prime-pole-cost) [L].
- **Sources:** I:GlobalIncidenceAllocationCondition; CACT:CriticalMultipleCompleteWeilPositivity; CACT:TheCriticalLowPacketRetainsItsSignedPolarPart; ACPL:ReceivingCharges/PrimeIncidenceCapacityGrowth [K]; CSAR:ReceivingCharges/GrowingSimultaneousReceivingModes [L]; [receiving-charge frontier](#shared-frontier).

<a id="inter-tower-coupling"></a><a id="coupled-tower-signature"></a><a id="sc"></a>
### SC — Stokes/Witt–Krein / archimedean successor

- **Path:** Glued affine Weil index≤1 / bounded Gaussian-damped two-prime kernel coupling → RH.
- **Established:** Glued index=κ_ζ+1; complete-matrix receiver. Fixed spline: sublinear-in-order tensor loss implies RH. Gaussian-damped ℕ² coupling has rate≤σ iff zero width≤σ; bounded coupling⇔RH. Exact normalized heat-average representation retains the full arithmetic prime+Gamma+pole spline source, with integrability and sum exchange [L].
- **Open:** Arithmetic bound for damped coupling, sublinear tensor loss, or glued index≤1/complete pole-hyperplane sign. Linear-in-order tensor loss only repeats the existing width bound. √Y-normalized prime–pole decay supplies no zero rate; [undamped coupling plus full RvM counts admits off-line model divisors](rh-killed-routes.md#coupling-growth).
- **Sources:** AKG:TheGluingFormulaAtEveryPlace; AKG:TowerCoupling/CoupledTowerSignatureFormula; CP:TheBaseIsAFixedLoss; ACPL:ConeBoundary/{GaussianConeKernel,PolynomialBoundaryRepulsion,TheGaussianCouplingIsAnArithmeticHeatAverage}; ACPL:ConeMoments/RVMCompletedSplineDivisor.

## Route candidates

Promotion requires the missing independent source mechanism/landing below; an unproved final estimate alone does not make a live route a candidate.

| Candidate / intended path | Established [L] | Promotion gap | Sources |
|---|---|---|---|
| <a id="lattice-sections"></a><a id="acs"></a>**ACS — Arithmetic Castelnuovo–Severi effectivity:** arithmetic effectivity / Rosati heights → Hodge index → RH. | Effectivity/count-height receivers, primitive h¹=Q/2, pure-curve calibration. Integral/window and concrete-curve Rosati rigidity [L]. Legendre-j reality at nontrivial ζ zeros⇔RH [L]; modular-j cusp growth abs(j)≍exp(2πImτ) [L]. All-R growing low block [K]. Full Selberg class: degree gap (0,1), d<1 Dirichlet unit; normalized degree1 has conductor≥2 or a pole [K]. | Arithmetic height comparison producing all-aperture primitive effectivity. Cusp growth, bounded-form rigidity and j-reality do not produce effectivity; [same-window Hecke similitudes are scalar](rh-killed-routes.md#window-reflection-centralizer). Selberg selection needs periodicity, integer conductor and primitive-character identification. | G:ExactArithmeticSourceEffectivity; AHD:DegenerationSelectsThePureCurves; KPA:{RosatiDegreesOfDegreeZero,RiemannHypothesisIsTheRealityOfTheLegendreInvariant} [L]; KPA:TheModularInvariantNearTheCusp [L]; SEL:GammaIndependentEulerRigidity; SEL:DegreeGap; SEL:DegreeOneConductorPole [K] |
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
| <a id="zcg"></a>**ZCG — Zero-configuration geometry:** prime image → local rigidity → collision exclusion → RH. | Isolated small RvM clusters admit polynomial-loss discriminant readout with exp(−Klog³T) tail; exact prime curvature. Period-N one-orbit/residue threshold (N−1)π/(Ng), sharp at period6 [L]. Integral finite configurations: explicit impurity gaps; N consecutive late power-sum bounds certify purity. Uniform distinct-root separation transports reality along fixed-degree paths [S]. | Independent ζ arithmetic gap and exhaustive cluster coverage. Integral realization and certificate-scale power-sum bounds are unproved; [continuous integral paths are constant](rh-killed-routes.md#integral-deformation). [General mixed-depth resolution: lower5π/(6g), upperπ/g](rh-killed-routes.md#two-carrier-inversion). | ZCG:{IsolatingWindowsVarySlowlyAtTheirTarget,TheImageReadsTheDiscriminantOfACluster,NearCoincidencePrimeCurvatureAndStripCollisionLaw,MixedDepthsHideBeyondTheInghamScale,PeriodicMimicsAreResolvedAboveTheirLastLag} [L]; ADO:{FinitelyManyOrdersCertifyIntegralPurity,UniformRepulsionCarriesReality} [S] |

## Shared frontier

<a id="first-overlap"></a><a id="relative-prime"></a><a id="physical-prime-defect"></a><a id="prime-centered-output"></a>
### Atomic positivity — RW, HF, SRT, AIP, ACS, SC

Twist/pencil limits: C² profile on [0,1], positive square mass, Fourier-square decay exponent>4, regular positive spectral tail of order β>0; tilted spline β=7. κ=(∫φ)²/∫φ². Families fixed unless stated.

| Established | RH-complete target / obstacle |
|---|---|
| Tilted spline: eventually, uniformly 1≤c≤(log N)^α, every 0<α<1/8, full matrix≥κ/(2c⁷)I. Low-block, complement and residual Schur bounds jointly discharged [L]. | Full/pole-hyperplane sign at every c=2K(log N)^(1/8), K>0. Subcritical exponents do not reach this endpoint. |
| Some fixed K₀>0: W≥κ₀/(2c⁷)I, eventually uniformly 1≤c≤2K₀(log N)^(1/8), κ₀=tiltedSplineSpectralFloorConstant. Prefix/collar Schur payment is complete. One horizon threshold gives Gram nonnegativity/index0 for every finite family; compensated window limits hold at every aperture [K]. | Full-space sign at every K>0. Small-K aliasing masks possible negative Weil directions; increasing N does not remove residual losses R=c⁸/logN and R². |
| Every fixed finite mean-zero periodic family, with arbitrary spatial profiles/moduli and each critical ratio: complete complex Weil Gram eventually PD iff joint spatial/twist functions independent; coefficient-uniform positive floor. Character specialization has no parity restriction. Orthogonal twisted/untwisted energy limit splits [L]. | Growing periods/families and untwisted Weil sign; fixed-family joint positivity supplies no full-space uniform floor. |
| Fixed finite nonresonant cosine twists have the exact nonnegative Fourier-power Hurwitz coefficient and eventual positive Gram on each independent family; character sectors decouple across opposite parities, not equal parities. Subtracting the zero-frequency pole leaves the untwisted aliasing count βJ/K [L]. | Moving/coalescing frequencies and growing-family uniformity; the finite-part identity does not control the joint frequency/horizon limit. |
| Tilted-spline critical pencil=κWeil+(7J/R)weighted Gram, R=lim c⁸/logN. R_A=∞⇔A/2≤a*_ζ; RH⇔every R_A=∞. Every tower stage a_k=weilFloorApertureTower k: A≤2a_k gives strict pencil positivity at every R>0 and eventual PD on fixed independent families [L]. | All-aperture/all-K full-space sign. Tower strict increase does not prove exhaustion; fixed-family positivity does not control the growing complement. |
| Exact clock c⁸=Klog N: each fixed independent family has eventual inertia (n₊(P), n₋(P)+n₀(P), 0). Correction is −B₁₀/K times the exponent-10 weighted Gram; O(c⁻¹) clock shifts give either sign on a nullvector [L]. | Strict leading positivity or second-order clock payment; growing-family uniformity. Nullvector existence is not established; [equality is not a sign certificate](rh-killed-routes.md#critical-pencil-nullspace). |
| Length-2a windows carry level-a Weil index. I(A)=#{n:L_n<A}; critical lengths L_n nondecreasing and locally finite, L_n=∞ iff at most n distinct right zeros. Inward dilation preserves finite negative spaces [L]. Fixed-packet rescaled zero bulk detects only the pole coefficient. | Arithmetic index ceiling; high-zero tail and growing packets. Critical-length counting does not bound the count. |
| Single-prime threshold transport⇔RH; fixed orthogonal twists cannot repair a negative untwisted pencil at large R. Nonorthogonal Dirichlet shifts retain O(1) Weil coupling and cancel pure tails. Prime2 correction makes each modified test positive at every aperture/critical ratio; universal stabilization across all primes⇔RH [L]. | Corrected-test positivity is not positivity of the original test. Universal d-shift stabilization requires Weil sign on the untouched length-log d head; a positive slightly larger head suffices. |
| Complete fixed-conductor residual: (logN/c)⟨W_Nv_m−E_m(c)v_m,v_l⟩→κ(2+γ−log(4π))·1_(m=l=1), c⁸/logN→R>0. Rescaled tilted-spline Gram=positive Jordan diagonal+positive polar genus [K]. | Fixed-conductor limits do not control complementary windows or moving frequencies. |
| Tilted spline, every R>0: Q=⌊(logN)^(13/32)⌋, y=Σ_(m≤Q)b_mv_m; W_N[y]=ΣE_m b_m²+κ(2+γ−log(4π))(c/logN)b₁²+o(ΣE_m b_m²), uniformly in b. Hence W_N[y]≥½ΣE_m b_m² eventually [K]. | Intermediate/far bands and mixed Schur payment. Orthogonal removal preserves the compensated window limit; compact-terminal sources concentrate at the pole [K]. [Full-horizon reference-energy floors fail](rh-killed-routes.md#full-conductor-diagonal), even for b_m≥0 [K]. |
| Large-prime/cofactor norm frames uniform for d≤N^ε, √N<p≤N^θ, θ>1/2, ε≥0, θ+2ε<1 [L]. | Complete-Weil comparison, smaller primes and remaining composite bands. |
| Tilted spline, each fixed K>0: one monotone R(X)→∞ receives every charge vector abs(t_m)≤1 uniformly through R(X), with exact neutrality/coordinates; adjunction, input norm² and absolute complete physical energy→0; complementary pairings→t_l/80, receiver norm²→1/20. Cutoff M=R(X)!X²≤X³, horizon X⁴⁰. Arbitrary infinite real profiles admit profile-dependent cutoffs [L]. | Growth rate is existential, not a prescribed RH-complete schedule. Uniform full-complement Schur payment remains. Cutoff=N instead leaves complement={0}; preserve cutoff/horizon separation. |
| Scalar prime-charge complement is asymptotic to an explicit logarithmic ramp. At Q=X²,N=X⁴⁰, an orthogonal terminal receiver r has ⟨Wv,r⟩→t/80, W[r]/logN→1/20, and source–receiver determinant→6239t²/6400>0 for t≠0 [K]. Balanced terminal contrasts retain endpoint cancellation and small low-conductor projections after multiplication by each fixed conductor [K]. | Uniform vanishing of all complementary pairings is false; this two-dimensional span is eventually positive. Pay the full complement, not just its coupling or source norm. |
| Cap_N=loglogN+O(1); complete physical energy→0 as Q,N→∞ independently [K]. Literal three-range bound; bounded-profile norm O(Vc(1+log c)); exact upward centering and coprime harmonic mean; signed incidence second-moment bounds [L]. For orthogonal neutral packets, complete−dilation=center−cross+(overlap−downward)−upward−Mertens; Mertens norm≤log8+4 [L]. | Critical-scale smallness with growing periods, offsets and prime bands; small/offset-dividing primes and joint four-channel payment. Nonorthogonal packets retain scalar/self correction. [Raw-cost control fails; combined adjunction/physical-norm/complete-energy costs admit no fixed linear charge² bound](rh-killed-routes.md#prime-pole-cost). |
| Fixed compact C² h supported in [−A,0], every R=c⁸/logN>0: (√logN/c)⟨W_Nv_m,x_N⟩→S_A(h)·1_(m=1). S_A retains the negative finite upward prime-power mean. Summable m⁻⁵ envelope and vanishing upper-packet mass give total inverse-energy mass→S_A(h)²R/J₁ through Q=⌊(logN)^(13/32)⌋ [K]. | Conductors beyond Q and signed complementary-window payment; no growing-aperture uniformity. Far-reserve proof requires 8C_S R≤g₀ independently of the pole's R² cost. |
| Every fixed compact terminal window: optimal packet gain S_A²/D_R, D_R=J₁/R+κg, g=2+γ−log(4π), attained by one pole coefficient, uniformly optimal over all coefficient families. Corrected energy→κWeil+7J₁M₈/R−S_A²/D_R; nonnegative on the established small-R band. Zero gain on ker S_A; explicit nonzero interior witness [K]. | Source-kernel energy and channels beyond Q. Rank-one optimization leaves aliasing and does not extend the positive R-band. |
| Ratio-prime row completes the divisor jet. Fixed bounded Lipschitz F=0 on x≤1/2, K=0 on x≥1; mean-zero period-q mode bounded B: actual near-row/overlap=O(B(q+c)/N), c≥1, 8c≤N. Annular selector 0≤α,β≤T, T≥1, 8Tc≤N: O(B(qT²+cT³)/N) for fixed bounded Lipschitz F,K; no q≤c restriction [K]. | Transfer to literal Gamma profiles and complete center/divisor/error assembly uniform beyond the logarithmic packet; Q=N^(1/64) remains a target. |
| <a id="prime-entry"></a>Each entered weight has a closed bounded convex admissible fibre. For δ=2c−log n↓0: abs(λ_n)≤√n(log(1/δ)+O(1)); an existing Lévy margin η permits changes≤√n·η(½log(1/δ)−¼). Absolute edge-cost E(c) crosses1 at a unique c*∈(½log5,½log6] [L]. | Actual-weight membership/full margin; fibres may be empty. [Absolute edge payment fails from c* onward](rh-killed-routes.md#absolute-edge-payment). Preserve signed prime gain, reflected energies and pole terms. |
| Reflection-prime-count band⇔RH⇔WL/JAS/CTF/PBM/Robin receivers. For2c<log5, only prime powers {2,3,4} can enter reflection terms, only2 the half-window diagonal. Their outward kicks cost<991/1000 of Lévy energy. Full reflected-pair floor1/(20000·2^k) holds for c≤a_k [L]. | Outside the proved floors, pay the remaining Hankel/pole/variance terms jointly. Sub-unit outward-kick cost alone does not establish the band. |
| Window sign⇔all fitting lattices; all-lattice positivity⇔RH∧λ=Λ. For every even bump, s_k=W(φ^(k)): even/odd sign⇔Hamburger moments of s_k/s_(k+1); full sign⇔Stieltjes moments. Nonnegative windows give positive jet minors and alternating reflection limits. Gamma-only Rayleigh quotients increase under differentiation; Gamma floors transfer even→odd→even mean-zero [L]. | Construct actual positive measures / all-aperture signed band; Gamma monotonicity omits prime/pole payment. For 0<c<log2, retained-variance certificates⇔convex {2,3} band; c≥21/40 excludes every w₂≤0 [K]. Actual prime-weight membership remains open; [variance-dropped gauges fail](rh-killed-routes.md#variance-dropped-theta-gauge). |
| Any nonzero C² profile on [0,1]: positivity on conductor spans≤N^θ, 0<θ<1/1080, through b_φloglog N; every polylog span through Kloglog N, each fixed K. Every subpolynomial span has a cutoff-dependent super-log-log clock [L]. | For general profiles, omitted bands and the receiver's prescribed clock; a cutoff-dependent clock need not reach it. |
| Zero-free logarithmic profile positive through ε₀L(log L)², L=loglog N; its reciprocal-floor budget works iff K≤ε₀ [L]. | Every required multiple; this profile's sign does not transfer to the Beurling profile. |
| One fixed smooth Beurling profile compresses every finite rational Gram at c_N=2L(log L)². Eventual pole-hyperplane sign on this single schedule⇔RH. Smooth nonnegative unit-bump receiver at every positive-power overlap [L]. | Actual sign on the selected profile/schedule. |

Sources:

- **Full matrix / frames:** CACT:TheCompleteWeilMatrixIsPositiveDefiniteBelowTheEighthRoot; CACT:EverySubpolynomialSpanHasASuperLogLogPositivityClock; CAF:LargePrimeCofactorsHaveUniformConductorFrames [L]; CACT:TheCompleteWeilMatrixIsPositiveAtACriticalMultiple; CACT:CriticalMultipleCompleteWeilPositivity; AHD:CompleteWeilCriticalMultipleAndWindowCorollaries [K].
- **Horizon / twists:** AHD:{TheWindowIndexCountsTheRightZeros,TheTwistedDirectionsCarryNoNegativeSquares,EveryFrequencySectorInheritsThePolarization,TheCanonicalCriticalClockEntersFromTheNegativeSide,TheCriticalBoundaryAddsItsNullDirections,TheUntwistedCountIsTheFinitePartAtZeroFrequency,TheBulkIsBlindBelowItsGrid,JointPeriodicWindowsInheritThePolarization,MultiplicativeConvolutionHorizonAndTailCancellation,StageTransportAndEnteringConductorLaw}; I:MultiPrimeDilationModulusAndIteratedWeilFloors; CWS:TheWindowIndexCountsCriticalLengths; G:InwardDilationPreservesTheWindowIndex [L].
- **Signed critical / low block:** AHD:TheCompleteCriticalResidueIsSupportedAtThePole; AHD:TheBulkEntriesAlongAGrowingOverlap; ADT:TheCriticalConductorFormRetainsThePolarGenus; CACT:TheCriticalLowPacketRetainsItsSignedPolarPart; AHD:CriticalWindowsSurviveLowConductorRemoval; AHD:TheCriticalThresholdOfAWindow [K]; [onset dictionary](../../formal/GaloisForLFunctions/WindowVisibilityLaw/OnsetApertureAndPositivityDictionary.lean) [L].
- **Windows:** SWC:{TheParitySectorsAreTheBandAtTheCentre,TheSectorsAreTheMomentConditionsOfTheJets,NeutralThetaGaugeOptimizationAndPrimeFourSliverFrontier,TheReflectionPrimeCountFeedsTheClassicalReceivers}; FADF:{TheEntryConstantIsOne,TheEdgeLawCrossesOneBetweenLogFiveAndLogSix,TheArithmeticHardyInterval} [L]; SWC:BelowLogFour/RetainedVarianceAndHalfWindowBandBelowLogFour [K].
- **Terminal sources:** AHD:{TerminalPolarSourceHasANontrivialKernel,TheCompleteTerminalSourceIsPolar,TheRatioPrimeRowCompletesTheTerminalJet,TerminalNearRowsCancelAlongTheLongIndex,TerminalLogarithmicAnnuliCancelAlongTheLongIndex}; CACT:{EveryTerminalWindowHasSummableConductorSources,EveryTerminalWindowHasAPolarConductorSource,EveryLowPacketCorrectionHasItsPolarCapacity} [K]. CACT:TheTopCollarHasADyadicSeventhPowerReserve [L].
- **Receiving charges:** CSAR:ReceivingCharges/{CoprimePrimeChargeCompleteEnergy,PrimeChargeComplementProfile,FixedChargeJordanLimit,PrimeChargeUniformHorizonEnergy}; CACT:ReceivingCharges/LiteralUpwardKernelVariation [K]. CACT:ReceivingCharges/{LiteralThreeRange,LiteralBoundedProfileNorm,UpwardCentering}; ACPL:ReceivingCharges/{WeightedIncidenceMoments,MixedChannelDecomposition,MixedChannelBounds}; CSAR:ReceivingCharges/{CoprimeHarmonicMean,GrowingSimultaneousReceivingModes,PrimeChargeFullHorizon,PrimeChargeConsequences} [L].
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

WTZ/DZG/ATD: RW/HF/ACS/PM support. Tate-positive dimensions=[0,κ(A)], κ(A)>0 and κ(A)→0; strict interior floor and exact rational-Hecke graph criterion [L]. Finite matrix reduction through A≤log(81/16); actual dimension1 sign through log(9/2). First-jet domination⇔Weil sign; no all-aperture domination. Sources: WTZ:{PositiveTateDimensionsFormAClosedInitialInterval,PositivePrimeMultipliersLowerTateDimension,TheTateHorizonBeforeEightyOneSixteenths,TheThirdTateStageDistinguishesEdgeSigns}.

GWZ/CSTW: RW/AIP precontact/lattice support. Causal density v: mass1, multiplier1/κ, V(x)√log(1/x)→1; inverse WW* has overlap kernel ∫₀^min(x,y)v(x−s)v(y−s)ds, integrable off diagonal. Normalized convolution reads right-continuous boundary data [L]. Backward readout is continuous at0 for L² forcing essentially bounded on y≤δ, δ>0 [S]. Actual Weil-Riesz regularity/domain admission and finite-contact exclusion remain. Sources: CSTW:{TheHalfLineLogarithmicFormHasItsActualInverse,TheHalfLineLogarithmicGreenKernelIsExplicit,TheLogarithmicRenewalAverageReadsTheBoundary} [L]; CSTW:TheLogarithmicBackwardConvolutionHasBoundaryValues [S]. SWC/FADF: signed charge/edge support; all-aperture payment open.

FFP: LA/TH support. Canonical zero-piece realization is exact; piece reality⇔RH. Genus-one stability⇔upper-half-plane zeros and drift D≥0; sharp margin −D. ξ has drift0: reversed Jensen roots concentrate near Im0 for σ≥1; e^{c(s−σ)}ξ is stable iff ξ is zero-free right ofσ and c≥0 [L]. Critical-line stability/all-root control remain open; [strict-margin obstruction](rh-killed-routes.md#xi-stability-margin). Sources: FFP:{ZeroPieceRealization,GenusOneStabilityClassification,StabilityBoundaryOfXi} [L].

ADO: [ZCG](#zcg)/[LA](#la) support. Integral trace polynomial with N eigenvalues paired by α↦q/α: sufficiently late N-order square-root power-sum bounds force purity [S]. Missing ζ realization and those bounds. HWV: squarefree prime complex≃wedge of S^(ω(m)−1), odd squarefree N/2<m≤N; topology supplies no signed cancellation. Source: HWV:SquarefreePrimeComplexIsASphereBouquet [L].

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
| FFP | FiniteFreeProbability | FADF | FrustratedArithmeticDirichletForms |
| ADO | ArithmeticDiscreteness | — | — |
