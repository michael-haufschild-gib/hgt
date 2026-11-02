# RH proof-route frontier

**RH open · 33 live routes · 16 candidates.**
**Corpus checkpoint:** `0cbd3adb4f413c3786d0cfbb68089be4e18aff2a`.

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
- **Established:** Ground minima attained; strict aperture monotonicity; μ≥1/5000 through A=181/500. Exact {∞,2} trace through A=½log3 with polar Krein (+1,−1) split. Finite-prime zero crossing by 2log(|S|+2)+11; bounded-below weighted energy requires Ω_κ(X) active weight in every large (X,κX), κ>1. Shared atomic positivity below.
- **Open:** Sign at A=½log3, then every aperture, paying low/mixed modes and polar cost with the full prime source.
- **Sources:** C:TheApertureFlowNeverStalls; SP:LiouvilleOddWindowRefutationAndSelectiveFullPositivity; SP:SemilocalPrimeTwoTrace/IntrinsicWeilTraceAndWindowCorollaries; SP:SemilocalPrimeTwoTrace/FinitePrimeSetSemilocalObstruction.

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
- **Established:** Half-power criteria; every polynomially growing near-frequency band retains actual exponent2Θ. Individual finite-clock leaf squares paid. Redheffer detR_N=M(N)=star-nerve Euler characteristic, with Ω±(√N) oscillation; RH iff detR_N=O_ε(N^(1/2+ε)) for every ε>0.
- **Open:** Actual half-power cancellation/determinant bound, including moving-band head/leaf and leaf/leaf covariance. Fixed-conductor or almost-sure bounds do not control actual Möbius coefficients.
- **Sources:** R:MobiusHilbertFormEquivalence; V:UnconditionalEscapedMoebiusDecayAndCrossRouteBridge; ADT:TheMertensFunctionIsAGluingDeterminant.

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
- **Established:** Hodge/Hecke/Riemann–Roch receivers; zero-density prime-flip separation. Restricted positivity, regular-bulk limits and exact window-index exhaustion [L]; first-prime fold decomposition [S]: shared frontier.
- **Open:** RH-complete full-family/horizon sign or primitive section effectivity. Remaining conductor bands and band–far cross must fit the vanishing floor; the complement's subpower index ceiling is not index0.
- **Sources:** J:TheIndexExit; PL:HeckeInvarianceOfTheCollidedPolarizationIsRH; CACT:CollectivePacketCoercivityAndLogarithmicConfinement.

<a id="chmd"></a>
### CHMD — Causal Hyperbolic–Modular Duality

- **Path:** Complete causal prime/Möbius wave bound or odd Doob half-threshold bound → RH.
- **Established:** Wave/Doob receivers, Haar transport, prime-edge Gamma reserve and mixed-polar cancellation on growing packets. abs(full-prime Haar coupling)/√Y≤C√(b+1)m_a/√a, Y,a,b≥1, m_a=haarMass(a).
- **Open:** Summed pole-subtracted all-detail/coarse remainder and full wave/odd sign, retaining non-arithmetic Gamma, signed potential, coarse/head and infinite-orbit terms.
- **Sources:** R:CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion; R:CHMDOddSectorCriterion; AID:FullPrimeWindowHaarDecay.

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
- **Established:** Collision/index receivers; attained extremizers. For 0<c<1/2: mean-sup O_c(log U), dyadic mean o(log U)⇔critical-scale clustering. All-stage Bessel–Szegő certificate⇔RH; log stages⇔inverse-log confinement. Energy Laplace abscissa=twice maximal depth. Holomorphic moments leave Jensen sharp; generic integer-moment data do not determine the log integral.
- **Open:** Actual all-window/all-stage certificate sign or uniform dyadic defect control. Little-o mean/clustering remains open and permits shallow/finite exceptions. Actual arithmetic log-mean control needs more than generic moment identities ([obstruction](rh-killed-routes.md#holomorphic-jensen)).
- **Sources:** CDG:LogScaleHeckeDefect/UnitWindowMinimumAndOscillation; CDG:LogScaleHeckeDefect/HalfGateClosureAndDensityEquivalence; CDG:SzegoCollision/HeckeDefectCorridorAndRHDoorOpener; CDG:SzegoCollision/WindowEnergyLaplace; CDG:SzegoCollision/LogStageBesselCertificate; R:WD/HolomorphicMomentsCannotBeatJensen; R:WD/MomentsDoNotDetermineTheLogMean.

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
- **Established:** Faithful ζ scattering divisor; Epstein/Eisenstein identification. For 0<Re w<1, Im w>0: positive core energy at zeros; Mellin strips (0,Re w) off zeros, (Re w−1,1) at zeros; u=0 convergence⇔ζ(w)=0; zero moments u=0,w equal ζ′(w). Actual Cauchy norm=central Gamma multiplier modulus: all-height strict contraction iff Re w≥1; uniform gap iff Re w>1. Spectrum=Gamma curve∪{0}; no bounded inverse.
- **Open:** Source-specific energy/charge control excluding off-line poles/cofinal escape, retaining 2ζ(w−1)/(w−1). Full-space Cauchy contraction cannot supply it in the critical strip; the Gamma spectrum is not a classification of Mayer eigenspaces.
- **Sources:** CP:TheEscapeCompletenessCriterion; RIT:GaussMayerScatteringVector; RIT:GaussMayerScatteringCharge; RIT:GaussMayerZeroMellinStrip; RIT:GaussMayerCoreZeroMoment; RIT:GaussMayerCauchySharpOperator; RIT:GaussMayerCauchySpectrum.

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

- **Path:** Complete atomic-family sign / horizon-layer asymptotic sign / late-lag bound → RH.
- **Established:** Full-family/horizon receivers; regular-bulk second-order limit and Gram/index transfer. Window-pencil index stabilizes to Weil index; families exhaust exactly the distinct right zeros.
- **Open:** Actual horizon sign or complete-family sign on the fixed Beurling schedule. Subtracting the explicit positive critical-scale correction leaves the open Weil sign.
- **Sources:** S:EveryWidthDecidesTheCriticalLine; SMAP:TheDyadicSignOfAPoleFreeGeneratorIsRH; AHD:TheHorizonCriterion; AHD:TheBulkDeterminesTheSecondOrderTerm; AHD:TheWindowIndexCountsTheRightZeros.

<a id="act"></a>
### ACT — Arithmetic criticality / single-shift variation

- **Path:** One fixed shift pays every even compact C² profile → odd Weil positivity → RH.
- **Established:** Exact single-shift receiver; explicit collar thresholds pay any fixed finite admissible family.
- **Open:** One shift uniform in profile/support, including exterior primes and signed/polar remainder.
- **Sources:** D:ShortProfilePoleFreeVariationInequality; I:ShiftedCollarsHaveExplicitPaymentThresholds.

<a id="aip"></a>
### AIP — Arithmetic incidence positivity

- **Path:** Prime incidence + plateau gauge → all-aperture global allocation → odd positivity → RH.
- **Established:** Allocation receiver; jump/incidence/shell decomposition; far-reserve costs absorbed below exponent1/8. Reduced divisor-jet operator bound with logarithmically weighted coefficients; growing-profile positivity: shared frontier.
- **Open:** Global allocation or RH-complete family sign. Pay remaining band–far coupling jointly with low-conductor, Gamma and polar costs.
- **Sources:** I:GlobalIncidenceAllocationCondition; I:GlobalSharedSurplusAllocation; CACT:CollectivePacketCoercivityAndLogarithmicConfinement.

<a id="lattice-sections"></a><a id="acs"></a>
### ACS — Arithmetic Castelnuovo–Severi effectivity

- **Path:** Arithmetic effectivity / Rosati heights / bounded Weil coupling → Hodge → RH.
- **Established:** Exact receivers; finite-grid-blind Künneth effectivity at every aperture. Prime-free h¹_prim≥‖f‖²/40 at radius≤1/64. Odd-characteristic hyperelliptic Frobenius calibration gives Hodge/Künneth positivity. All-profile arithmetic Künneth positivity through radius181/500. Shared atomic positivity below.
- **Open:** Arithmetic primitive effectivity at every aperture, paying constrained/mixed modes; alternatively dense-lattice or Gaussian-damped cone bounds ([SC](#sc)), or finite product-group tensor index. Undamped cone bounds admit off-line models even with zero exponent of convergence. Sharp genus upper law remains open.
- **Sources:** G:ExactArithmeticSourceEffectivity; LST:RiemannRochOutsideAFiniteDivisorAtEveryDegree; LST:TheExteriorJumpsOfAPrimeFreeCycle; LST:TheStepanovCountPaysThePrimitiveH1OverFiniteFields; G:TheGenusLawForcesSimpleZeros; SP:SemilocalPrimeTwoTrace/IntrinsicWeilTraceAndWindowCorollaries.

<a id="inter-tower-coupling"></a><a id="coupled-tower-signature"></a><a id="sc"></a>
### SC — Stokes/Witt–Krein / archimedean successor

- **Path:** Glued affine Weil index≤1 / bounded Gaussian-damped two-prime kernel coupling → RH.
- **Established:** Exact glued index=κ_ζ+1; complete-matrix/tensor receivers. For distinct primes p,q and fixed τ>0, Gaussian-damped kernel coupling is O(exp(σt)) iff width≤σ, σ≥0, t=m log p+n log q; bounded ℕ² coupling⇔RH, including unattained width. Full-prime Haar rows have horizon-independent mass-weighted decay.
- **Open:** Prime/archimedean bound for damped coupling, or glued index≤1/complete pole-hyperplane sign. Undamped exact-spline quartets retain positive unattained width and bounded coupling even when every positive inverse-power height sum converges.
- **Sources:** AKG:TheGluingFormulaAtEveryPlace; AKG:TowerCoupling/CoupledTowerSignatureFormula; ACPL:ConeBoundary/GaussianConeKernel; ACPL:ConeBoundary/PolynomialBoundaryRepulsion; ACPL:ConeMoments/ZeroExponentSplineQuartets; AID:FullPrimeWindowHaarDecay.

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
| <a id="w1c"></a>**W1C — Clifford–Dirac / centred Lee–Yang:** arithmetic operator or ferromagnetic limit → real-rooted Ξ. | Finite Lee–Yang theorem and Ising-limit receiver; explicit density/field constraints. PM supplies a faithful ζ scattering divisor. | Source-defined Ising couplings with centred slow-field convergence, or a positive/self-adjoint realization of the faithful divisor. A meromorphic resolvent alone does not locate poles on the line. | R:LeeYangIsingGraphDatum; R:IsingLawConvergenceRH; R:HermitianPencilEulerFactorObstruction; RIT:GaussMayerScatteringVector |
| <a id="wbf"></a>**WBF — Source certificates:** arithmetic stream → depth-uniform positive completion → Ξ. | Abstract genealogy Gram/Fredholm recovery and relative determinants; no arithmetic coupling. | Arithmetic certificate stream and source-faithful uniform-depth completion landing on Ξ/Weil positivity. | H:PaperGenealogyFredholmRecovery; H:PaperCriticalGenealogyCompletion |

## Shared frontier

<a id="first-overlap"></a><a id="relative-prime"></a><a id="physical-prime-defect"></a><a id="prime-centered-output"></a>
### Atomic positivity — RW, HF, SRT, AIP, ACS, SC

| Established | RH-complete target / obstacle |
|---|---|
| Tilted spline, eventually uniformly 1≤c≤(log N)^α, 0<α<1/9: full matrix≥κ/(2c⁷)I; W≥bc⁻⁸D_N. Deep stars inherit positivity. Spectral-floor sublevel has D_N≤C log(2c)‖x‖² [L]. | RH iff eventual full/pole-hyperplane sign at every 2K(log N)^(1/8), K>0. Close the full-space rate gap. |
| c_N→∞, c_N≤(log N)^α, α<1/8: for every ε>0, some X makes the entire growing conductor block e≤⌊c_N/X⌋ eventually ε-relative-close to Σ_e J(e)b_e² after c_N⁷ rescaling [L]. | Transition e≈c_N, larger conductors and mixed complement at every K(log N)^(1/8). Fixed-packet bulk weights do not select the line. Fixed mean-zero periodic horizon twists erase each fixed-zero contribution after c_N⁻¹ scaling [L]; no full-zero-sum limit follows. |
| Scalar scaling c⁷E_m(c)=J(m)R_m(c/m), J(m)=C J₈(m)/ϕ(m); J(m)/J(1)=#P⁷(ℤ/mℤ). 0≤R_m(x)≤Cx; R_m(x)→1 uniformly. Projective orbit/local-count laws hold over every finite commutative/local ring. Λ residue vanishes; every nonempty finite prime-flip set has indefinite residue [L]. | Full growing-conductor complement at RH overlap. Scalar/counting positivity does not give complete-matrix sign or classify infinite twists. |
| Nonzero C² profile on [0,1], Fourier-square decay p>4, s^βE₁(s)→J, β≥0: c_N^(β+1)/log N→K>0 gives c_N⁻¹Q_N→κQ_Weil(H)+(βJ/K)∫e^(−(β+1)y)H², H=e^(y/2)h, κ=(∫φ)²/∫φ². For κ>0, βJ≥0, finite-pencil index increases to Weil index; its supremum over families/K equals the number of distinct right zeros, possibly infinite [L]. | Actual Weil/index sign. Tilted spline threshold K*=7J(1)∫e^(−8y)H²/(κ abs(Q_Weil(H))) for negative windows; equality unresolved. Supercritical sign⇔RH; index exhaustion supplies no independent upper bound. |
| Window [−A,0]: Q=Ω(0)‖H‖²+J∞+Σw_n·fold_n−∫k_AH²+pole; symmetric k_A has mass 2∫₀ᴬψ₁/₂(eᵗ)dt. For log2≤A<log3, only the 2-fold acts; fold-symmetric/antisymmetric tests contribute ∓weighted end mass [S]. | First-prime and all-window sign remain open: pay canonical density, negative Ω(0) and signed pole by actual jump/fold energies. |
| Mid-band V_⌊N^θ⌋∩V_⌊(log N)^q⌋^⊥ coercive for α<1/4, q>3α, 0<θ≤1/4096. Packet overlap costs O_φ(c). Under conductor/overlap size bounds, reduced divisor-jet action has a divisor-mean bound weighted by (1+log R)Σ_m(1+log m)a_m² [L]. | Absorb retained jet/pole costs and band–far cross at the 1/8 rate. Removing the pole coefficient is not implied by orthogonality to V₁. |
| Prime-only conductor band √N<p≤N^θ, θ<1, log N≥1: ‖Σa_pv_p‖²≥(1−θ)Σa_p²/4. Exact Gram=diagonal+rank≤2 correction [S]. | This is a horizon-vector frame bound, not complete-Weil positivity. Composite conductors, low-band coupling and signed source costs remain. |
| Every nonzero C² profile on [0,1]: E_m(c)≥a_εexp(−εc/m), every ε>0. On V_⌊N^θ⌋, 0<θ<1/1080, 1≤c≤b_φloglog N: floor a_φexp(−Bc), universal B>0; a_φ,b_φ independent of θ [L]. Every polylog span positive through 1≤c≤Kloglog N, each fixed K>0 [L]. | Beyond log-log on fixed polynomial spans: remove the c log R/log N leakage/center loss. Full space also needs omitted bands and cross-terms. |
| L=loglog N: an explicit profile clock g(L)/L→∞, g(L)≤Llog L, gives floor (log N)^−η/4 on V_⌊exp(log N/L^κ)⌋, 0<η<1/2, κ>2, 1≤c≤g(L) [L]. Extension to every R_N=N^o(1), with cutoff-dependent clock C_N/L→∞, retains the same floor [S]. | Complete the complementary-space estimate. The integrated clock does not reach the Beurling receiver's 2L(log L)² schedule; the general extension remains unverified. |
| Tilted spline, 1≤c≤(log N)^α, 0<α<1/8: window/Gamma costs absorbed; V_⌊N^θ⌋^⊥ has floor b_θlog N/c⁷ for every θ>0. Every nonpositive subspace has dimension≤⌊N^θ⌋ [L]. | Join the conductor block to this far complement with paid cross-terms. Full-space positivity remains at α<1/9; a subpower index ceiling is not index0 or finite off-line support. |
| Zero-free logarithmic profile positive through explicit ε₀L(log L)², L=loglog N. Some reciprocal-floor budget with 0<α≤1/128 works at coefficient K iff K≤ε₀ [L]. | For this profile, reach every fixed positive multiple by stronger floor/residual estimates. Its positivity does not transfer to the Beurling profile. |
| One fixed smooth Beurling profile realizes every finite rational Gram as a positive-mass-weighted complete-matrix compression limit at c_N=2L(log L)², L=loglog N. RH iff eventual pole-hyperplane sign on this single schedule [L]. | Actual sign at c_N. Steklov-profile criterion requires all fixed K≥1; the Beurling criterion does not. |
| Smooth nonnegative unit-bump pole-hyperplane receiver at every α>0 [L]. | Prove actual sign at any positive-power overlap rate. |
| Prime-defect decomposition and sharp relative residual scale (log Q)²/log N. Coprime-successor window energy≥(K−Q(Q−1))×nonconstant packet mass for K≥Q(Q−1), gcd(p,Q!)=1 [L]. | Full Gamma/pole/row-potential comparison; successor/prime-defect gaps alone are not complete-Weil positivity. |

Sources:

- **Positivity/payment:** CACT:CollectivePacketCoercivityAndLogarithmicConfinement; CACT:EveryProfileIsPositiveAtLogLogOverlapOnPolynomialSpans; CACT:EveryPolylogConductorSpanIsPositiveAtLogLogOverlap; CACT:EveryCompactProfileIsPositiveBeyondLogLogOverlap; CACT:EverySubpolynomialSpanHasASuperLogLogPositivityClock [S]; CACT:ThePolynomialConductorComplementIsCoerciveBelowTheEighthRoot; CACT:TheReducedDivisorJetCostsItsDivisorMean; CACT:SharpenedMidBandAndCrossBounds; CAF:LargePrimeConductorsHaveDisjointHorizonSpikes [S]; CSAR:SharpPrimeResidualScale; CSAR:CoprimeSuccessorGap.
- **Horizon/counts:** AHD:TheCountLawOverEveryFiniteRing; AHD:TheHorizonCriterion; AHD:TheBulkDeterminesTheSecondOrderTerm; AHD:TheWindowIndexCountsTheRightZeros; AHD:TheTwistedHorizonLayerIsZeroBlind; CWS:TheWindowDatum [S]; CWS:TheFirstPrimeFold [S].
- **Receivers:** SSHA:EveryEighthRootMultipleReceivesTheTiltedSpline; RIT:TheZeroDensityEndpointHasTheConductorCriterion; TM:ReceiverRate/SharpLogarithmicOverlapBudget; TM:ReceiverRate/EveryFiniteGramFitsOneCriticalOverlap; RIT:TheHodgeIndexAtCriticalOverlap.

<a id="external-literature"></a>
### Scope guards

- RH-equivalent receivers are proved; their arithmetic positivity/cancellation inputs remain open.
- Finite off-line support is conditional, not established for ζ; it would not imply RH.
- Critical-line census: simple-critical proportion≥0.67250071−ε uses imported Zeta23 plus local IGP. Higher-proportion certificates still require actual signed prime surplus/moment estimates; model16/21 is not a ζ proportion.
- Fixed aperture/rank/scale and density-one control leave finite or shallow exceptions. No uniform positive ground-energy gap at unbounded aperture.

<a id="pw-b"></a><a id="hb--theta-cusp-hawking-causal-scattering"></a><a id="isc-polar"></a><a id="art"></a>
### Non-route labels

PW-B: [retired source-uniform extinction mechanism](rh-killed-routes.md#kr-pwb); surviving critical-line detector feeds PM/scattering. ISC-polar, BVI and ART: support, not independent live routes. [Other killed mechanisms and retired aliases](rh-killed-routes.md).

ADT: conductor degeneration supporting HF/ACS/SC; gluing determinant reformulates MC. AHD: horizon/index receivers within SRT/HF/SC. CWS: window locality/fold decomposition within HF/RW/ACS [S]; no positive realization supplied. See [shared frontier](#shared-frontier).

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
