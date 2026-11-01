# RH proof-route frontier

**RH open · 33 live routes · 16 candidates.**
**Corpus checkpoint:** `b4bf677c5627ef6ce93aa74366256775bb8efdf3`.

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
- **Established:** Exact prime-error/energy criteria; integer count producers approach leading slope1.
- **Open:** Signed square-root precision. Near-main-term counts lack uniform error as slope→1; integrality alone gives no parity cancellation.
- **Sources:** B:WeilLagCriticalDeficitEndpointAndLimitLaw; CP:TheAbelSlopeOfThePrimeErrorIsTheArchimedeanGenus.

<a id="rw"></a>
### RW — Restricted Weil ground energy

- **Path:** Complete Weil form → μ(A)≥0 at every aperture → RH.
- **Established:** Ground minima attained; strict aperture monotonicity; μ≥1/5000 through A=181/500. Exact {∞,2} trace through A=½log3; intrinsic operator-trace positivity equivalent to μ≥0, with polar Krein (+1,−1) split [S]. Shared atomic positivity below.
- **Open:** Sign at A=½log3, then every aperture, paying low/mixed modes and polar cost. Separate local-factor positivity fails [S]; a uniform positive gap at unbounded aperture is impossible.
- **Sources:** C:TheApertureFlowNeverStalls; SP:LiouvilleOddWindowRefutationAndSelectiveFullPositivity; SP:SemilocalPrimeTwoTrace/IntrinsicWeilTraceAndWindowCorollaries [S].

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
- **Established:** Half-power criteria; every polynomially growing near-frequency band retains actual exponent2Θ. Individual finite-clock leaf squares paid. Redheffer detR_N=M(N)=star-nerve Euler characteristic; RH iff detR_N=O_ε(N^(1/2+ε)) for every ε>0 [S].
- **Open:** Actual half-power cancellation/determinant bound, including moving-band head/leaf and leaf/leaf covariance. Fixed-conductor or almost-sure bounds do not control actual Möbius coefficients.
- **Sources:** R:MobiusHilbertFormEquivalence; V:UnconditionalEscapedMoebiusDecayAndCrossRouteBridge; ADT:TheMertensFunctionIsAGluingDeterminant [S].

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
- **Established:** Hodge/Hecke/Riemann–Roch receivers and prime-star decomposition; shared atomic positivity below.
- **Open:** RH-complete full-family sign, or independent primitive section effectivity. Growing-conductor and mixed-complement costs must fit the vanishing floor.
- **Sources:** J:TheIndexExit; PL:HeckeInvarianceOfTheCollidedPolarizationIsRH; CACT:CollectivePacketCoercivityAndLogarithmicConfinement.

<a id="chmd"></a>
### CHMD — Causal Hyperbolic–Modular Duality

- **Path:** Complete causal prime/Möbius wave bound or odd Doob half-threshold bound → RH.
- **Established:** Wave/Doob receivers, Haar transport, prime-edge Gamma reserve and mixed-polar cancellation on controlled growing packets.
- **Open:** Full wave/odd sign paying remaining non-arithmetic Gamma, signed potential, coarse/head and infinite-orbit terms together.
- **Sources:** R:CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion; R:CHMDOddSectorCriterion.

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

- **Path:** Source current → collision charge<2; alternatively one shared all-dyadic-scale defect bound → RH.
- **Established:** Exact collision/index and all-dyadic-bound receivers; fixed-c mean-sup O_c(log U), c<1/2; extremizer attainment/asymptotics. Birkhoff–Szegő factorization and stopping-prefix RH⇔disk-unit sectoriality; prefix strip multiplicity Θ(N²log N), stabilized prefix Ω(√T) at resolved scales [S].
- **Open:** Actual sectoriality at each height and all sufficiently fine resolutions, or one uniform all-dyadic bound. Fixed-c control permits finite exceptions; averaged corridors permit exceptional heights/shallow zeros. Little-o mean⇔critical-scale clustering; both open.
- **Sources:** CDG:LogScaleHeckeDefect/FiniteThetaPoleNodalRHEquivalence; CDG:LogScaleHeckeDefect/HalfGateClosureAndDensityEquivalence; CDG:LogScaleHeckeDefect/UnitWindowMinimumAndOscillation; CDG:SzegoCollision/SharpStripZeroGrowthAndSqrtLowerBound [S].

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

- **Path:** Global Haar approximation / cofinal damping ε↓0 / every escape limit visible → RH.
- **Established:** Escape receivers; actual Mayer product D(w,z)D(w,−z)=∏_(c,m≥0)(1−z^(2ℓ_c)exp(−(w/2+m)L_c)), L_c=2logλ_c the attained hyperbolic translation length. Absolute convergence near z=0 for Re w>1, on |z|≤1 for Re w>2. D(w,−1)≠0 for real w>0.
- **Open:** Cofinal complete-energy control/exclusion of escape. Faithful ζ/Selberg-scattering identification, including geodesic multiplicities/normalization, and critical-strip resonance exclusion.
- **Sources:** CP:TheEscapeCompletenessCriterion; ACG:RHIsTheVisibilityOfEveryEscapeState; RIT:GaussMayerPrimitiveOrbitProduct; RIT:GaussMayerUnitEvenWordDeterminant.

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
- **Established:** Odd/polar criteria; local odd floor through radius181/500; explicit Liouville-twist separation.
- **Open:** Full odd sign with reflected-prime/polar payment. Current companion-forcing and conductor-horizon requirements are incompatible.
- **Sources:** R:WeilMarkovOddPositivity; CDG:TheConductorForcingGap.

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

- **Path:** Complete atomic-family sign / late-lag bound / exhaustive tower sign → RH.
- **Established:** Full-index exhaustion and exact family receivers; shared atomic positivity below.
- **Open:** Actual sign/index ceiling on an RH-complete family. One small critical coefficient, fixed aperture or subpower index ceiling is insufficient.
- **Sources:** S:EveryWidthDecidesTheCriticalLine; SMAP:TheDyadicSignOfAPoleFreeGeneratorIsRH; SSHA:EveryEighthRootMultipleReceivesTheTiltedSpline.

<a id="act"></a>
### ACT — Arithmetic criticality / single-shift variation

- **Path:** One fixed shift pays every even compact C² profile → odd Weil positivity → RH.
- **Established:** Exact single-shift receiver; explicit collar thresholds pay any fixed finite admissible family.
- **Open:** One shift uniform in profile/support, including exterior primes and signed/polar remainder.
- **Sources:** D:ShortProfilePoleFreeVariationInequality; I:ShiftedCollarsHaveExplicitPaymentThresholds.

<a id="aip"></a>
### AIP — Arithmetic incidence positivity

- **Path:** Prime incidence + plateau gauge → all-aperture global allocation → odd positivity → RH.
- **Established:** Allocation receiver; jump/incidence/shell decomposition; shared atomic positivity below.
- **Open:** Global allocation or RH-complete family sign. Mixed conductor, Gamma and polar costs must fit the retained positive reserve.
- **Sources:** I:GlobalIncidenceAllocationCondition; I:GlobalSharedSurplusAllocation; CACT:CollectivePacketCoercivityAndLogarithmicConfinement.

<a id="lattice-sections"></a><a id="acs"></a>
### ACS — Arithmetic Castelnuovo–Severi effectivity

- **Path:** Arithmetic effectivity / Rosati heights / bounded Weil coupling → Hodge → RH.
- **Established:** Exact receivers; finite-grid-blind Künneth effectivity at every aperture. Prime-free h¹_prim≥‖f‖²/40 at radius≤1/64. Odd-characteristic hyperelliptic Frobenius calibration gives Hodge/Künneth positivity. All-profile arithmetic Künneth positivity through radius181/500 [S]. Shared atomic positivity below.
- **Open:** Arithmetic primitive effectivity at every aperture, paying constrained modes/mixed coupling; alternatively bounded coupling or finite product-group tensor index. Sharp genus upper law open; N−N_simple=o(T) follows only assuming that law.
- **Sources:** G:ExactArithmeticSourceEffectivity; LST:RiemannRochOutsideAFiniteDivisorAtEveryDegree; LST:TheExteriorJumpsOfAPrimeFreeCycle; LST:TheStepanovCountPaysThePrimitiveH1OverFiniteFields; G:TheGenusLawForcesSimpleZeros; SP:SemilocalPrimeTwoTrace/IntrinsicWeilTraceAndWindowCorollaries [S].

<a id="inter-tower-coupling"></a><a id="coupled-tower-signature"></a><a id="sc"></a>
### SC — Stokes/Witt–Krein / archimedean successor

- **Path:** Actual glued affine Weil index≤1 at any place → RH.
- **Established:** Exact glued index=κ_ζ+1; coupled-source exhaustion and tensor/coupling receivers. Complete-matrix Gram realization and critical-overlap pole-hyperplane receiver: shared frontier. Finite ordinary index gives finite off-line support only.
- **Open:** Independent glued index≤1, pole-hyperplane sign at every fixed critical multiple, or uniform dense-lattice coupling. Matching/differencing supplies no sign or index reduction.
- **Sources:** AKG:TheGluingFormulaAtEveryPlace; AKG:TowerCoupling/CoupledTowerSignatureFormula; RIT:TheHadamardPowersOfWeilsKernel.

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
| <a id="w1c"></a>**W1C — Clifford–Dirac / centred Lee–Yang:** arithmetic operator or ferromagnetic limit → real-rooted Ξ. | Finite Lee–Yang theorem and Ising-limit receiver; explicit density/field constraints. | Source-defined couplings converging to Riemann's measure with centred slow-field law, or faithful arithmetic scattering denominator. | R:LeeYangIsingGraphDatum; R:IsingLawConvergenceRH; R:HermitianPencilEulerFactorObstruction |
| <a id="wbf"></a>**WBF — Source certificates:** arithmetic stream → depth-uniform positive completion → Ξ. | Abstract genealogy Gram/Fredholm recovery and relative determinants; no arithmetic coupling. | Arithmetic certificate stream and source-faithful uniform-depth completion landing on Ξ/Weil positivity. | H:PaperGenealogyFredholmRecovery; H:PaperCriticalGenealogyCompletion |

## Shared frontier

<a id="first-overlap"></a><a id="relative-prime"></a><a id="physical-prime-defect"></a><a id="prime-centered-output"></a>
### Atomic positivity — RW, HF, SRT, AIP, ACS, SC

| Established | RH-complete target / obstacle |
|---|---|
| Tilted spline, eventually uniformly 1≤c≤(log N)^α, 0<α<1/9: full matrix≥κ/(2c⁷)I; W≥bc⁻⁸D_N. Deep stars inherit positivity. Spectral-floor sublevel has D_N≤C log(2c)‖x‖² [L]. | RH iff eventual full/pole-hyperplane sign at every 2K(log N)^(1/8), K>0. Close the full-space rate gap. |
| Fixed conductors: c_N⁷G_N(e,e′)→δ_ee′ C J₈(e)/ϕ(e), C>0, when c_N→∞ and c_N≤(log N)^α, α<1/8; each fixed nonzero finite packet eventually positive [L]. | Growing-conductor/mixed-complement control at every K(log N)^(1/8); fixed-packet positivity supplies no uniform full-family sign. |
| Individual conductor energies: c⁷E_m(c)/J(m)→1 uniformly as c/m→∞, J(m)=C J₈(m)/ϕ(m). Limiting coefficients satisfy J(1)J(ab)=J(a)J(b) for coprime a,b [S]. | Finite-horizon mixed entries, transition m≈c and full complement at RH overlap. Scalar uniformity/multiplicativity does not establish complete-matrix positivity/factorization. |
| Mid-band V_⌊N^θ⌋∩V_⌊(log N)^q⌋^⊥ coercive for α<1/4, q>3α, 0<θ≤1/4096 [L]. | This omits low conductors and terminal complement. Their mixed terms remain unpaid at the RH rate. |
| Top block n>N/L_c, L_c=linearDefectCutoff(c)≈c: ratio+non-ratio prime self-form costs O(c(1+log c)) per atom-normalized coefficient mass, c≥1, N≥L_c [S]. | Head/top mixed terms and complete Gamma/pole balance; this self-form bound does not improve the full-matrix positivity range. |
| Zero-free logarithmic profile positive through explicit ε₀L(log L)², L=loglog N. Some reciprocal-floor budget with 0<α≤1/128 works at coefficient K iff K≤ε₀ [L]. | Reach every fixed positive multiple; tuning within current budgets cannot suffice. Improve the floor/residual estimate. Sinc comparison uses a different profile. |
| Finite rational Grams are positive-mass-weighted complete Steklov matrix compression limits at family-dependent 2KL(log L)², L=loglog N. RH iff eventual pole-hyperplane sign at every fixed K≥1: compression index≤1 plus even ζ index; moment-preserving approximation unnecessary [L]. | Actual pole-hyperplane sign for every K≥1. Approximation supplies neither sign nor a family-uniform K. |
| Smooth nonnegative unit-bump pole-hyperplane receiver at every α>0 [L]. | Prove actual sign at any positive-power overlap rate. |
| Prime-defect decomposition and sharp relative residual scale (log Q)²/log N. Coprime-successor window energy≥(K−Q(Q−1))×nonconstant packet mass for K≥Q(Q−1), gcd(p,Q!)=1 [L]. | Full Gamma/pole/row-potential comparison; successor/prime-defect gaps alone are not complete-Weil positivity. |

Sources: CACT:CollectivePacketCoercivityAndLogarithmicConfinement; CACT:TheTopPrimeSelfFormCostsOnlyALogarithm [S]; SSHA:EveryEighthRootMultipleReceivesTheTiltedSpline; HWV:StarsOfTheCompleteWeilFamily; RIT:TheHodgeIndexAtGrowingOverlap; RAPT:ThePhysicalPrimeKernelRetainsThePoleDefect; CSAR:SharpPrimeResidualScale; CSAR:CoprimeSuccessorGap; ADT:TheLimitingMixedStructure; ADT:TheSubthresholdBlockIsUniformlyJordan [S]; ADT:TheRescaledLimitTensorizesOverThePrimes [S]. Logarithmic profile: TM:ReceiverRate/TheLogarithmicProfileIsPositiveBelowCriticalOverlap; TM:ReceiverRate/SharpLogarithmicOverlapBudget; TM:ReceiverRate/ABoundedOverlapRateSeesASemilocalWindow; RIT:TheHodgeIndexAtCriticalOverlap.

<a id="external-literature"></a>
### Scope guards

- RH-equivalent receivers are proved; their arithmetic positivity/cancellation inputs remain open.
- Finite off-line support is conditional, not established for ζ; it would not imply RH.
- Critical-line census: simple-critical proportion≥0.67250071−ε uses imported Zeta23 plus local IGP. Higher-proportion certificates still require actual signed prime surplus/moment estimates; model16/21 is not a ζ proportion.
- Fixed aperture/rank/scale and density-one control leave finite or shallow exceptions. No uniform positive ground-energy gap at unbounded aperture.

<a id="pw-b"></a><a id="hb--theta-cusp-hawking-causal-scattering"></a><a id="isc-polar"></a><a id="art"></a>
### Non-route labels

PW-B: [retired source-uniform extinction mechanism](rh-killed-routes.md#kr-pwb); surviving critical-line detector feeds PM/scattering. ISC-polar, BVI and ART: support, not independent live routes. [Other killed mechanisms and retired aliases](rh-killed-routes.md).

ADT: conductor degeneration supporting HF/ACS ([shared frontier](#shared-frontier)); gluing determinant reformulates [MC](#mc). Not a separate RH route.

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
