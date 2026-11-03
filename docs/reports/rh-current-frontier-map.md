# RH proof-route frontier

**RH open · 33 live routes · 16 candidates.**
**Corpus checkpoint:** `4c804b1979956863951ccdff94ad8103f8c397e7`.

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
- **Established:** Attained, strictly radius-decreasing minima; μ≥1/5000 through a=181/500, ≥1/8000 through a*=enlargedWeilFloorAperture>181/500. Exact {∞,2} trace through a=½log3. Explicit Gamma/Tate domination holds on windows of length≤2a* for 0≤k≤1/160000. Prime2 repairs an explicit negative frozen direction; the frozen odd complement is coercive off one cubic moment [K]: [OWU](#owu).
- **Open:** Sign at a=½log3, then every radius: joint Gamma, fold and sinh payment. Local Tate domination needs an aperture-dependent horizon; [uniform horizons fail](rh-killed-routes.md#tate-domination). Barta/Doob identities still need an actual paying weight.
- **Sources:** C:TheApertureFlowNeverStalls; I:AnExplicitLargerApertureRetainsAWeilFloor; ATD:FirstFoldStageDomination; WTZ:TheGroundStateTransformOfAWindow; SP:SemilocalPrimeTwoTrace/IntrinsicWeilTraceAndWindowCorollaries.

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
- **Established:** Hodge/Hecke/Riemann–Roch receivers. Tilted-spline full-matrix positivity at every overlap exponent0<α<1/8, including low-block/complement coupling. Fixed periodic twisted sectors eventually positive; mixed Ramanujan sectors add no limiting negative squares. Window-index exhaustion and large-prime/cofactor lower frames.
- **Open:** Exact critical-overlap sign at every positive multiple, or independent all-window positive realization. Fixed-family polarization does not control growing families or the untwisted Weil sign.
- **Sources:** J:TheIndexExit; CACT:TheCompleteWeilMatrixIsPositiveDefiniteBelowTheEighthRoot; AHD:EveryPeriodicTwistedSectorInheritsThePolarization; AHD:TheTwistedDirectionsCarryNoNegativeSquares; CAF:LargePrimeCofactorsHaveUniformConductorFrames.

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
- **Established:** Collision/index receivers; attained extremizers; dyadic mean o(log U)⇔critical-scale clustering; Laplace abscissa=twice maximal depth. Almost-all log-stage certificates⇔log-free unit-window occupancy; log-free multiplicity density implies both and the log-mean law. Planck bad-window volume≤C_r B e^(−rA)V/A; stage c log m/loglog m, 0<c<1/48, has O_c(V/loglog V) exceptional unit windows. All-degree/window certificates⇔RH; exterior cap cancellation reaches σ_m=1−1/(116log(m+5)) [L].
- **Open:** All-window certificate sign or right-port Laplace bound; inner caps [1/2,σ_m] unpaid. Actual log-free occupancy/multiplicity bounds; finite/shallow exceptions. [Occupancy and horizontal-moment control are incomparable under generic density data](rh-killed-routes.md#window-density-separation); occupancy needs bounded per-window multiplicity second moments to recover log-free density [L].
- **Sources:** CDG:LogScaleHeckeDefect/UnitWindowMinimumAndOscillation; CDG:LogScaleHeckeDefect/HalfGateClosureAndDensityEquivalence; CDG:SzegoCollision/WindowEnergyLaplace; CDG:SzegoCollision/LogStageBesselCertificate; CDG:WindowPortFlux/CauchyCapCancellationAndPolynomialStage; CDG:NearLineLogMean/ClusteringLogMeanAndMollifierEquivalence; CDG:NearLineLogMean/NearLineDensityBesselCertificateAndSeparation [L]; R:WD/MomentsDoNotDetermineTheLogMean.

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
- **Established:** Resonances⇔ζ(2s)=0; D_s≤0, equality iff Re s=1/4; Krein positivity⇔RH. On the Eisenstein family, finite dyadic cusp energy⇔resonance [L]. Every finite T₂/T₃ word preserves finite cusp energy of window lifts (Re s>0) and upper-strip actual cores. Completed periods have eigenvalues1+p·p^(−2s), p=2,3; Mellin transport realizes T_p−Id with Weil similitude factor p. Full Weil energy is the limit of twice finite-core Krein squares, with conjugate-twisted reflection [K]. Uniform resonant-core bound C(1+Im s)^N exp(πIm s/2)min(a⁻¹,a^(1−2Re s)) [K]. Gaussian core sums converge pointwise and in whole-axis Haar L², with exact Mellin interchange on 0<Re u<1; removing damping recovers complete Weil energy through the coefficient reflection pairing [K].
- **Open:** Arithmetic D_s≥0 on resonances, Krein positivity or pole exclusion. Finite-core positivity already requires included zeros on the line; short-window positivity can be paid by omitted zeros. Retain outgoing boundary charge in any positive completion; full Mayer eigenspace classification and rational Weyl/loop-group identification remain open.
- **Sources:** RIT:MayerScattering/MayerResonanceCharacterization; RIT:MayerScattering/FareyLewisTransferAndCuspSeparation; RIT:MayerScattering/PhysicalCoresHaveFiniteHeckeCuspEnergy; RIT:MayerScattering/PrimeThreeWindowMellinBridge; RIT:MayerScattering/WindowWeilCorePackets; RIT:MayerScattering/WindowCoreProjectionAndTailCompensation; RIT:MayerScattering/PhysicalCoreSpectralBounds; RIT:MayerScattering/ResonantCoreEndpointBounds; RIT:MayerScattering/GaussianPhysicalCoreSynthesis; RIT:MayerScattering/GaussianCoreMellinSynthesis [K]. [Compact Hecke closure](rh-killed-routes.md#hecke-window-cusp), [bare reflection identification](rh-killed-routes.md#window-krein-reflection) and [raw core eigenlaw](rh-killed-routes.md#core-hecke-boundary) fail.

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
- **Established:** Odd/polar criteria; local odd floor and Liouville-twist separation. Prime-free tests: W≥‖f‖²/1000, primitive h¹≥‖f‖²/2000. Odd C² tests in [−1/2,1/2], m_cubic=∫F(x)x(1−16x²/5)dx: frozen Q₁+20|m_cubic|²≥‖f‖²/125 [K]; the cubic-moment kernel is coercive. The complete form satisfies Q≥‖f‖²/100 when ∫xF=∫x³F=0 [K], including prime2 and the pole.
- **Open:** Pay the two low moments and their cross terms with the positive complete-form complement, then all-aperture reflected-prime/Gamma/polar payment. One repaired negative test does not give the full-stage sign.
- **Sources:** R:WeilMarkovOddPositivity; LST:WindowJumpCounts/OddPrimeFreeGammaJumpCount; WTZ:TheFirstFoldPaysANegativeFrozenDirection [K]; WTZ:TheCubicMomentPaysTheFrozenOddComplement [K]; WTZ:TheFirstFoldIsPositiveAwayFromTwoOddMoments [K]; LST:WindowJumpCounts/RegionalLogarithmicGap [K].

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
- **Established:** Full-family receivers and index exhaustion. Cluster-product detector needs a≥max(e⁶,1/δ) and C log(|γ|+306)log a≤a for a zero of depth≥δ, |γ|≥2, universal C; yields a smooth negative test in [−a−1,a+1], without zero separation. Fixed periodic twists have exact positive second-order limits; fixed pole-free packets are blind to the zero sum below N^θ, every 0<θ<1, under the shared overlap condition.
- **Open:** Actual RH-complete sign; growing-conductor/frequency uniformity and unresolved high-zero tail. Stronger visibility and fixed-sector positivity do not exclude the detected zeros.
- **Sources:** S:ClusterProductHorizon; AHD:TheHorizonCriterion; AHD:TheWindowIndexCountsTheRightZeros; AHD:TheSecondOrderTermOfEveryPeriodicTwist; AHD:TheBulkIsBlindBelowTheResolutionHeight.

<a id="act"></a>
### ACT — Arithmetic criticality / single-shift variation

- **Path:** One fixed shift pays every even compact C² profile → odd Weil positivity → RH.
- **Established:** Exact single-shift receiver; explicit collar thresholds pay any fixed finite admissible family.
- **Open:** One shift uniform in profile/support, including exterior primes and signed/polar remainder.
- **Sources:** D:ShortProfilePoleFreeVariationInequality; I:ShiftedCollarsHaveExplicitPaymentThresholds.

<a id="aip"></a>
### AIP — Arithmetic incidence positivity

- **Path:** Prime incidence + plateau gauge → all-aperture global allocation → odd positivity → RH.
- **Established:** Allocation receiver; jump/incidence/shell decomposition. Deep-row inverse-energy estimates close full low-block/complement Schur payment for every exponent0<α<1/8; full tilted-spline matrix≥κ/(2c⁷)I uniformly 1≤c≤(log N)^α.
- **Open:** Global allocation or full sign at c=2K(log N)^(1/8) for every K>0. The endpoint, not below-endpoint block assembly, is unpaid.
- **Sources:** I:GlobalIncidenceAllocationCondition; I:GlobalSharedSurplusAllocation; CACT:TheCompleteWeilMatrixIsPositiveDefiniteBelowTheEighthRoot.

<a id="lattice-sections"></a><a id="acs"></a>
### ACS — Arithmetic Castelnuovo–Severi effectivity

- **Path:** Arithmetic effectivity / Rosati heights / bounded Weil coupling → Hodge → RH.
- **Established:** Effectivity/count-height receivers; primitive h¹=Q/2; local Weil floors. Tate first-jet domination⇔Weil sign; explicit first-fold domination. Pure-curve degeneration gives the Hurwitz form of Frobenius angles; the golden impure model instead grows exponentially with stationary own-tower index1.
- **Open:** All-aperture primitive effectivity or an independent dominating count; sharp genus upper law. [Positive Tate coefficients](rh-killed-routes.md#tate-count-selector) do not descend to Weil sign. [Smooth reflection centralizers and same-window Hecke similitudes are scalar](rh-killed-routes.md#window-reflection-centralizer); a nontrivial positive realization needs a larger carrier.
- **Sources:** G:ExactArithmeticSourceEffectivity; LST:TheStepanovCountPaysThePrimitiveH1OverFiniteFields; DZG:TheDominationQuestionIsFirstOrder; ATD:FirstFoldStageDomination; AHD:DegenerationSelectsThePureCurves; AHD:TheGoldenFakeIsSelfSimilarUnderDilation.

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
| <a id="w1c"></a>**W1C — Clifford–Dirac / centred Lee–Yang:** arithmetic operator or ferromagnetic limit → real-rooted Ξ. | Finite Lee–Yang/Ising-limit receiver; faithful PM divisor and algebraic Krein realization [L]; finite-cusp-energy resonance criterion and exact window/core Weil transport: [PM](#pm). | Source-defined Ising couplings with centred slow-field convergence, or positive arithmetic Hilbert realization with self-adjoint generator. Cusp selection and window transport do not establish positivity of the [Krein form](rh-killed-routes.md#mayer-krein-sign). | R:LeeYangIsingGraphDatum; R:IsingLawConvergenceRH; R:HermitianPencilEulerFactorObstruction; RIT:MayerScattering/MayerKreinLaxPhillipsRealization [L] |
| <a id="wbf"></a>**WBF — Source certificates:** arithmetic stream → depth-uniform positive completion → Ξ. | Abstract genealogy Gram/Fredholm recovery and relative determinants; no arithmetic coupling. | Arithmetic certificate stream and source-faithful uniform-depth completion landing on Ξ/Weil positivity. | H:PaperGenealogyFredholmRecovery; H:PaperCriticalGenealogyCompletion |

## Shared frontier

<a id="first-overlap"></a><a id="relative-prime"></a><a id="physical-prime-defect"></a><a id="prime-centered-output"></a>
### Atomic positivity — RW, HF, SRT, AIP, ACS, SC

Twist/pencil limits: C² profile on [0,1], positive square mass, Fourier-square decay exponent>4, regular positive spectral tail of order β>0; tilted spline β=7. κ=(∫φ)²/∫φ². Families fixed unless stated.

| Established | RH-complete target / obstacle |
|---|---|
| Tilted spline: eventually, uniformly 1≤c≤(log N)^α, every 0<α<1/8, full matrix≥κ/(2c⁷)I. Low-block, complement and residual Schur bounds jointly discharged [L]. | Full/pole-hyperplane sign at every c=2K(log N)^(1/8), K>0. Subcritical exponents do not reach this endpoint. |
| Fixed nonzero mean-zero periodic χ: exact second-order coefficient is its nonnegative Fourier-power Hurwitz sum; every fixed independent window family has eventual positive Gram. Fixed Ramanujan-twisted/untwisted mixed limit splits; negative index equals the untwisted pencil's index [L]. | Uniformity in growing periods/families; untwisted Weil sign. Positivity is not uniform over the entire growing horizon space. |
| Fixed frequency cos(2παn), sin(2πα)≠0: Hurwitz coefficient ½[ζ(β+1,{α})+ζ(β+1,1−{α})], rational or irrational. Primitive character windows have exact Gauss/L-value coefficients at β+1>1; opposite parities decouple, equal parities remain coupled [L]. | Moving-frequency/coalescence control. Finite-frequency energy decoupling [S] does not supply a uniform critical-horizon sign. |
| Critical pencil=κWeil+(βJ/K)weighted Gram. Fixed-family sign holds for length A≤3/5, or κ(10+72e^(A/2))K<βJ. Smooth length A<log2+1/50: cosh-hyperplane positive, eventual finite-family negative index≤1 [L]. | Every aperture and every required K. Small-K count reserve and finite-family index bounds do not establish the full receiver. |
| Length-2a windows carry level-a Weil index; supremum over windows/K counts distinct right zeros. Fixed conductor packets, c_N≥1, c_N log²N/N^(1−θ)→0, 0<θ<1: the rescaled zero sum below N^θ tends κ·poleCoefficient²·(2+γ−log4π); pole-free limit0 [L]. | High-zero tail and growing packets. Low-height bulk detects the pole coefficient, not off-line depth. |
| c_N→∞, c_N≤(log N)^α, α<1/8: conductor block e≤⌊c_N/X⌋ is ε-relative-close to its Jordan diagonal after rescaling, for suitable X. J(m)/J(1)=#P⁷(ℤ/mℤ); local count laws hold over every finite ring [L]. | Critical-scale transition/growing-conductor coupling. Scalar counts do not provide full Weil sign. |
| Large-prime/cofactor norm frames uniform for d≤N^ε, √N<p≤N^θ, θ>1/2, ε≥0, θ+2ε<1 [L]. | Complete-Weil comparison, smaller primes and remaining composite bands. |
| RH⇔complete fold-capacity inequality. Exact stage Doob/Barta and exit-charge decompositions retain Gamma, signed folds and polar terms. Explicit Gamma/Tate domination for length A≤2a*, a*=enlargedWeilFloorAperture, 0≤k≤1/160000 [L]. | Independent all-aperture paying weight/domination. [Uniform Tate horizons and scalar shifted-pole repairs fail](rh-killed-routes.md#tate-domination). |
| Any nonzero C² profile on [0,1]: positivity on conductor spans≤N^θ, 0<θ<1/1080, through b_φloglog N; every polylog span through Kloglog N, each fixed K. Every subpolynomial span has a cutoff-dependent super-log-log clock [L]. | For general profiles, omitted bands and the receiver's prescribed clock; a cutoff-dependent clock need not reach it. |
| Zero-free logarithmic profile positive through ε₀L(log L)², L=loglog N; its reciprocal-floor budget works iff K≤ε₀ [L]. | Every required multiple; this profile's sign does not transfer to the Beurling profile. |
| One fixed smooth Beurling profile compresses every finite rational Gram at c_N=2L(log L)². Eventual pole-hyperplane sign on this single schedule⇔RH. Smooth nonnegative unit-bump receiver at every positive-power overlap [L]. | Actual sign on the selected profile/schedule. |

Sources:

- **Full matrix / frames:** CACT:TheCompleteWeilMatrixIsPositiveDefiniteBelowTheEighthRoot; CACT:EverySubpolynomialSpanHasASuperLogLogPositivityClock; CAF:LargePrimeCofactorsHaveUniformConductorFrames.
- **Horizon / twists:** AHD:TheWindowIndexCountsTheRightZeros; AHD:EveryPeriodicTwistedSectorInheritsThePolarization; AHD:TheTwistedDirectionsCarryNoNegativeSquares; AHD:EveryFrequencyActsAsAFrobeniusAngle; AHD:TheCharacterWindowsAreGradedByParity; AHD:TheCountPaysTheSecondOrderBelowAUniformMultiple; AHD:TheCoshHyperplaneInheritsThePolarization; AHD:TheBulkIsBlindBelowTheResolutionHeight [L]; AHD:TheHorizonLayerIsGradedByFrequency [S].
- **Windows:** WTZ:TheGroundStateTransformOfAWindow; DZG:TheGroundStateRepresentationOfAStage; ATD:FirstFoldStageDomination.
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

WTZ/DZG/ATD: window algebra, Tate jets/flow and signed-count/Doob identities supporting RW/HF/ACS/PM. Bare first-jet domination⇔Weil sign; independent all-aperture domination open. Tate window positivity has exact first/second-stage thresholds but no fixed k>0 works at all apertures. Sources: WTZ:TheSecondStagePathIsAttained; WTZ:NoTatePositivityIsUniform; DZG:TheDominationQuestionIsFirstOrder; ATD:FirstFoldStageDomination.

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
| ATD | ArchimedeanTateDomination | | |
