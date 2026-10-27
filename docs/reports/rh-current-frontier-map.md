# RH proof-route frontier

**Status:** RH open. **31 live routes; 17 standalone candidates; PW-B candidate sub-branch.**
**Corpus checkpoint:** `80f251476ea993894a02165cf5394c6d127d0921` — committed corpus coverage; uncommitted evidence remains [S].

**Evidence:** [L] integrated Lean source at checkpoint, not a fresh kernel audit; [S] unintegrated/working source, not certified closure; [P] paper only. Statements retain their mathematical scope. An RH-equivalent receiver does not prove its arithmetic input.
**Classification:** live = source observable + proved RH-sufficient receiver + explicit open estimate; candidate = incomplete independent source mechanism/landing; support = tools feeding existing routes.

[Live routes](#live-routes) · [Candidates](#route-candidates) · [Supporting frameworks](#supporting-research-frameworks) · [Dead mechanisms](#dead-mechanisms--scope-boundaries) · [Source locator](#source-locator)

<!-- Maintenance: replace facts in place. Each route has Path, Proved, Open, Sources.
Keep only results that locate the current frontier. No theorem inventories, derivations,
chronology, work packages or progress notes. Scoped obstructions belong in rh-killed-routes.md. -->

## Find a route

| Family | Live routes | Candidates |
|---|---|---|
| Arithmetic incidence | [AIP](#aip) | — |
| Prime explicit formula / signed energy | [WL](#wl), [RW](#rw), [FU](#fu), [RP](#rp), [PA](#pa), [LI](#li), [JAS](#jas), [CTF](#ctf), [EWU](#ewu), [OWU](#owu), [PBM](#pbm), [RB](#rb), [ACT](#act) | [APF](#apf), [EGC](#egc), [EWJ](#ewj), [FEL](#fel) |
| Möbius cancellation | [MC](#mc) | [MSC](#msc) |
| Theta / heat / moments | [TT](#tt), [LA](#la), [TH](#th), [HCF](#hcf) | [HJ](#hj) |
| Zero visibility / localization | [SRT](#srt) | — |
| Causal hyperbolic–modular duality | [CHMD](#chmd) | — |
| Geometry / index / arithmetic rigidity | [TG](#tg), [HF](#hf), [GTA](#gta), [ACS](#acs) | [DR](#dr), [IRK](#irk) |
| Newton dynamics | [XN](#xn) | — |
| Renewal / singular comparison | [RN](#rn) | — |
| Ward / collision | [WD](#wd) | — |
| Suzuki / boundary limits | [SZ](#sz) | [SEC](#sec) |
| Physical realization | [PM](#pm) | [PTR](#ptr), [W1C](#w1c), [PW-B](#pw-b) |
| Singular source completion | — | [BSH](#bsh), [CDC](#cdc), [PCS](#pcs), [RFHM](#rfhm), [SC](#sc), [WBF](#wbf) |
| Deterministic recurrence | [BAG](#bag) | — |

## Shared frontier

| Established [L] unless marked [S] | Exact remaining boundary |
|---|---|
| Full Weil floor ≥‖f‖₂²/5000 through radius 3/10 [L], extended through 181/500 [S]; odd floor ≥‖f‖₂²/1000 through 181/500 [L]; smooth primitive floor ≥‖f‖₂²/1000 through (log2+1/50)/2. | All apertures with complete prime/Gamma/polar terms. At 181/500 only atom 2 is read; every weight with w(2)=log2 shares the full floor [S]. |
| Full/even/odd H¹ floors with VK saving; full/odd H¹ floor rate sets and critical-deficit energy rate sets are [zero width,∞), endpoint attained. | Arithmetic rate zero. Existing savings retain positive leading exponential growth. |
| RH ⇔ width zero ⇔ full/even/odd Hodge defect zero ⇔ cofinal damped-μ admission ⇔ vanishing Báez–Duarte residual ⇔ positive gauge mass for every actual subcritical cofactor limit. | Produce any one sufficient source estimate; equivalences alone close none. |
| Physical L² full and polar rates agree; form-norm/Birman–Schwinger infimal rates equal width. | Physical L² equality with positive width and form-norm endpoint attainment remain open. Do not exchange norms. |
| Fixed-aperture completion/sign transfer; collided-form L² coercivity at every fixed aperture; signed Weil Gårding bound and finite negative index. | Coercivity is for the positive collided form, not W. Finite negative index need not be zero. No uniform positive ground-energy gap at unbounded aperture. |
| Source RR, maximal positive blind ideals, boundary/collar forcing and simple-pole source rigidity. | Full-source sign/exhaustion and nonreal interior zero exclusion. Restricted positivity and source identification are not RH. |
| Re W=collided mass−off-line defect; RH iff W equals the collided form iff collided-form translation invariance. The collided form and its Hecke defect are computed by the Laplacian of log‖ξ‖ and by finite theta prefixes, without zero indexing. Section count with RR+Bézout, effectivity, integral Rosati heights and the one-sided ψ count are RH-equivalent. | Arithmetic construction of a form both positive and translation-equivariant, e.g. an upper bound forcing the computed Hecke defect to zero. Equivalences and computations supply no sign; positive kernel counts need not supply Rosati heights; subtracting ψ from the polar box destroys RI. |

**Sources:** D:ThreeTenthsSharpGaugeWeilPositivity; I:SchurLendingOddWindowThreeHundredSixtyTwoThousandths; G:AllParityCriticalDeficitAndEndpointSobolevLaws; O:TheWidthDictionary; C:UnconditionalBirmanSchwingerRateReadsTheZeroWidth; PL:TheOscillatoryCapacity; PL:HeckeInvarianceOfTheCollidedPolarizationIsRH; CP:ASectionCountIsTheSign; AE:NaiveHeightsAreTraces; AE:ThePolarBoxCount; CP:TheStepanovCountIsTheSign; PL:TheCollidedFormIsCoerciveAtEveryAperture; PL:WeilsFormHasFinitelyManyNegativeDirectionsAtEveryAperture; CDG:XiSourceCurrent; SP:LiouvilleOddWindowRefutationAndSelectiveFullPositivity [S].

## Live routes

<a id="wl"></a>
### WL — Weil lag function

- **Path:** Actual prime lag/deficit → one-sided bound or subexponential critical energy → RH.
- **Proved [L]:** Critical energy bounded ⇔ coprime cross-work bounded below ⇔ cumulative energy O(T) ⇔ RH; width-rate endpoints and O(1) high-zero tail. Eventual ψ(x)−x≤C√x(log x)² iff RH; horizon torsion=ψ(N), first Fourier=M(N). Linear prime-error log-energy budget forces RH and slope≥C₀=2+γ_E−log(4π). With damped prime-error energy integrable for every c>0, Abel slope→C₀ forces RH and simple critical zeros. Every finite critical-zero set costs Σ|mρ/ρ|²; successor shift preserves that cost. Renormalized torsion energy has no automatic sign.
- **Open:** Actual adverse-correlation/critical-energy bound, or all-c integrability and genus-saturating Abel slope. The latter is a sufficient stronger target, not a proved equivalence. RH-conditional zero-tail estimates and partial fractions do not control the full archimedean remainder/exterior energy.
- **Sources:** B:WeilLagCriticalDeficitEndpointAndLimitLaw; B:HighZerosCarryABoundedCriticalDeficit; CP:TheStepanovCountIsTheSign; AE:TheHorizonTorsion; CP:ThePrimeErrorBudgetDominatesTheArchimedeanGenus; CP:AnAbelSlopeAtTheGenusIsRHWithSimpleZeros; CP:TheSuccessorDefectIsABoundedHardyPerturbation; R:CramerZeroSumMeanSquare; CP:ThePrimeErrorSymbolSplitsAtTheZeros [S].

<a id="rw"></a>
### RW — Restricted Weil ground energy

- **Path:** Complete prime−Gamma−polar form → ground minimum μ(A)≥0 at every aperture → RH.
- **Proved [L]:** Completed-domain receivers, shell flux and prime-shell decomposition. μ strictly decreases; RH iff every finite-aperture μ>0, equivalently cumulative frozen-flow relaxation≤initial energy on the threshold ladder. Signed Gårding bound gives finite negative index at every fixed aperture, not index zero. Full ground-energy floor≥1/5000 through radius 181/500 [S]. Norm-specific rates: shared frontier.
- **Open:** Source-derived relative-step or cumulative-relaxation bound paying collars, low modes and complete polar energy. Telescoping supplies no bound; permanently frozen prime families eventually become negative.
- **Sources:** C:TheApertureFlowNeverStalls; C:ThePrimeShellBetaFunction; C:ThresholdVanishingAndCollarDominanceOfThePrimeShell; C:UnconditionalEqualityOfPolarAndFullGroundEnergyRates; PL:WeilsFormHasFinitelyManyNegativeDirectionsAtEveryAperture; SP:LiouvilleOddWindowRefutationAndSelectiveFullPositivity [S].

<a id="fu"></a>
### FU — CCM-FU signed prime scheduling

- **Path:** Signed prime/Möbius history → completed Abel moment A(M)/M bounded above → RH.
- **Proved [L]:** Receiver, prime-exhaustive schedules, graph realization with vanishing diagonal cost, exact clock kernels and narrow-window negative prime channel. Wide-window/cross-block analysis [S]; universal prime-channel nonpositivity fails on dyadic windows.
- **Open:** Control initial seed, inter-cutoff drift, earlier action, cross-block covariance and endpoints jointly. Isolated channel gain is not a complete-history bound.
- **Sources:** R:CCM/CCMFUSuzukiMobiusDivisorOneSided; A:TheLinearWindowOfTheCriticalPrimeChannel; A:CriticalPrimeChannelBeyondLinearWindows [S]; B:PrimeGraphClockCorrelationKernels.

<a id="rp"></a>
### RP — Route-P / SP-E history floor

- **Path:** Matched−quantile prime history → eventual linear defect floor → RH.
- **Proved [L]:** Exact floor criterion, signed hyperbola/centroid/square-debt identities and low-LCM payment. Native first clock jet has bounded noncompact synthesis and strong differentiation.
- **Open:** Full-history floor with high-LCM pairs, moving core and singular-domain transport controlled jointly. Positive damping-shell traces do not supply it.
- **Sources:** R:SPEQuantileRieszRoutePLinearFloorCriterion; R:RoutePLcmPairPayment; R:BurnolBaseFirstJetAdmission.

<a id="pa"></a>
### PA — Prime–archimedean source passivity

- **Path:** Exact prime−archimedean trace → current sign, subexponential Bernstein mismatch or positive signed compact moments → RH.
- **Proved [L]:** Source/trace recovery and exact receivers. Every fixed Hausdorff order is positive at sufficiently large shifts; finite order blocks share thresholds.
- **Open:** High-frequency current sign, every-positive-rate mismatch bound, or all-shift/all-order positivity. Order-dependent thresholds and positive saddle bands leave a signed complement.
- **Sources:** R:PrimeArchEndpointFrequencyAccretivity; R:SoninCoupledBernsteinMismatchRH; R:PrimeArchHausdorffFixedOrderLargeShiftPositivity; R:PrimeArchSignedCompactCompletionCollapse.

<a id="mc"></a>
### MC — Möbius cancellation at half power

- **Path:** Actual μ cancellation/subpower energy or square-sampled Chebyshev bound → RH; alternatively exclude every oscillating smooth-power probe below half damping.
- **Proved [L]:** Exact receivers, fixed-modulus/window cancellation and below-diagonal savings; diagonal dual norms do not pay the remainder. Prime-modulus character bound √p(1+log p). Torsion Fourier=M(N); every-strict-half-power bound iff RH; M=o(√x) is false. Linear Mertens log-energy budget forces RH, simple critical zeros and summable inverse-derivative residue squares. Finite-curve analogue: linear spectral Mertens budget iff purity plus simple spectrum, with exact repulsion-energy slope. Escaped-boundary growing-endpoint/single-dyadic rate laws [S]; Burgess moment, energy and averaged-shift estimates [S], not actual μ cancellation.
- **Open:** Actual moving-scale μ cancellation at every strict half-power, or cofinal subpower energy. The stronger linear log-energy budget is not produced. Uniform decay over all multipliers is impossible; the growing-endpoint formulation retains an RH-equivalent half-power target [S]. Typical-phase or relative twin cancellation does not select actual μ.
- **Sources:** R:MobiusHilbertFormEquivalence; T:OscillatingProbeSourceEstimatesEnergyGapAndCollarLimitations; V:TheDualNormIsMinorArcBelowTheDiagonal; V:TheDiagonalDualNormIsArchimedean; CP:TheMertensBudgetForcesASimpleCriticalSpectrum; CP:AMertensBudgetIsPurityWithASimpleSpectrum; CP:TheMertensBudgetOfACurveIsTheRepulsionEnergyOfItsSpectrum; SP:MoebiusEscapedPairingBoundaryLaw [S]; [effectivity support](#arithmetic-effectivity), [BVI](#bvi), [correlation support](#arithmetic-correlation).

<a id="tt"></a>
### TT — Theta-tail and heat–Cassini currents

- **Path:** Theta source → directed covariance/Wold decay or odd Weil sign → RH.
- **Proved [L]:** Exact theta seam/tail and Wold receivers; sharp boundedness threshold t<1/2; Φ-Doob/reflected-prime identities. Restricted current signs and continuum light-cone positivity.
- **Open:** Signed nonlocal covariance or complete odd/primitive positivity at every rapidity and test scale. Restricted signs do not orient the full reflected-prime form.
- **Sources:** R:XiHeatCassiniWoldNaturalSquareEnergySubhalf; R:PaperWoldDirectedCovarianceRH; R:WeilMarkovOddPositivity; [ACT](#act).

<a id="la"></a>
### LA — Line anchor

- **Path:** Theta source → all-height Laguerre/Jensen or heated coefficient sign → real-rooted Ξ → RH.
- **Proved [L]:** Exact coefficient receivers; real-axis finite-head nonnegativity; coefficient-positive complementary tail and lossless head-to-full transfer. Gaussian/heat tail limits, sharp local repair laws and uniform high-order heated positivity. Real-axis sign is not coefficient sign.
- **Open:** All-height/all-degree finite-head coefficient positivity, especially remaining low orders and near-double off-line pairs. No actual-divisor repairing-factor supply theorem.
- **Sources:** R:XiSliceGaussianFiniteHeadPositivity; R:XiSliceHeatOrderUniformPositivity; R:XiSliceHeatSignIndex; ALDG:SourceLocalFactors; [WD](#wd).

<a id="tg"></a>
### TG — Topological sub-unit gate

- **Path:** Euler/Gaussian source → positive-residual transgression + integer trace<1 → RH.
- **Proved [L]:** Winding/index and cubic-transgression identities; exact central-gap receivers. Gaussian integer weights have nonpositive coprime-divisibility covariance.
- **Open:** Matrix-complete E_base=E_residual+Tr T_D with E_residual≥0 and integer trace<1 on every disc, or a zero-rate central-gap bound. Indicator covariance does not control arbitrary signed/Euler-inverted combinations.
- **Sources:** R:FormationAnchoredCubicSpecialization; R:RestrictedProjectionIndexOperatorNormCriterion; R:GaussianCentralGapExplicitCriterion; R:GaussianDivisibilityCorrelation.

<a id="hf"></a>
### HF — Positive Hodge form on arithmetic cohomology

- **Path:** Full source Weil/cohomological positivity, full-positive weight, defect D<2 or collided-form Hecke invariance → RH.
- **Proved [L]:** Source/divisor surfaces agree; distinct-right-zero defect D is even when finite, RH iff D<2. Effectivity/Tate/height receivers. Re W=collided mass−off-line defect; RH iff defect zero iff collided translation invariance iff one-shift similitude. Collided form is L²-coercive at every fixed aperture. Explicit finite integer theta prefixes recover collided/depth moments uniformly for sourceTestSize(f)≤1, support radius a, |τ|≤n/2 and a+j|L|≤2log(n+1), after normalization by 4^j. Prefixes still use continuous source integrals, not finite quadrature.
- **Open:** Source-derived full sign/D<2, bounded-error integral Rosati heights bounded below or midpoint-convex, or collided-form translation invariance. Coercivity and finite-prefix convergence compute the positive mass/Hecke defect; neither bounds the defect above by zero.
- **Sources:** R:WeilPositivityPrimeBlindDuality; J:TheIndexExit; AE:TatesLimitLaw; AE:NaiveHeightsAreTraces; AE:TheConvexityOfCounts; PL:HeckeInvarianceOfTheCollidedPolarizationIsRH; PL:TheCollidedFormIsCoerciveAtEveryAperture; CDG:FiniteThetaMetric; CDG:FiniteThetaApertureMetric; [polarization](#arithmetic-polarization), [depth support](#conjugate-diagonal), [ACS](#acs).

<a id="chmd"></a>
### CHMD — Causal Hyperbolic–Modular Duality

- **Path:** Complete causal prime/Möbius wave bound or odd theta-Doob half-threshold bound → RH.
- **Proved [L]:** Exact wave/Doob/nodal receivers. Supported maximal graph equals completed real aperture core; sharp cuts preserve the domain. Expanding windows recover full signed energy and primitive defect; cut commutator is uniformly bounded.
- **Open:** Full one-sided wave bound or odd Doob/nodal inequality. Pay reflected-prime interaction and primitive oneL defect; localization and convergence supply no sign.
- **Sources:** R:CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion; R:CHMDOddSectorCriterion; R:CHMDSharpWindowNodalConvergence; R:CHMDSharpGeneratorDomain.

<a id="th"></a>
### TH — Theta moment positivity

- **Path:** Theta/prime−Gamma moments → all-degree Hankel/Bezoutian positivity → RH.
- **Proved [L]:** Low-order signs; all-rank strict positivity for nonzero nonnegative coefficient vectors on a common small positive-time interval; finite-rank stable-polynomial regions.
- **Open:** Arbitrary signed coefficients at every degree under one common positive heat time, or equivalent full phase/current sign. Orthant positivity is insufficient.
- **Sources:** R:ThetaCuspSteinCertificates; R:XiHeatHankelFormOrthantPositivity; R:XiHeatStableTestPositivity.

<a id="rn"></a>
### RN — Theta renewal and singular comparison

- **Path:** Theta renewal/connection source → divisor-faithful winding or directed boundary-work sign → RH.
- **Proved [L]:** Green/BV solvers, multiplicity-exact packets and fixed-Gaussian realization; compact cone-positive renewal operator with exact regularized determinant/resonances.
- **Open:** Mixed prime+Gamma≥pole, retaining cusp/seam terms and directed current. Cone positivity does not imply real spectrum; unregularized synthesis has a topology obstruction.
- **Sources:** R:PaperThetaNativeResolvent; R:ThetaRenewalPositiveFredholm; R:ThetaRenewalFredholmSpectrum; R:PaperThetaUnregularizedExtensionObstruction.

<a id="wd"></a>
### WD — Ward orientation and horizontal collision

- **Path:** Directed source current → vanishing negative-cross cap/collision mass or collision charge<2 → RH.
- **Proved [L]:** Exact Ward/collision receivers; integrable nonnegative cap vanishing iff RH. Actual finite-head/tail and heated-tail error laws. Sharp Hermite barrier, attained extremizers, heat threshold and asymptotics are formalized; not remaining paper gaps.
- **Open:** Actual cap/collision mass zero, divisor-independent Euler–Stieltjes saturation, or all-height finite-head coefficient sign at arbitrarily small heat. Tail control and optimal model extremizers do not orient actual coefficients.
- **Sources:** R:XiWardGlobalCapAndFiniteHeadArithmetic; R:DeBruijnCollisionMassAndCriticalHeat; R:XiSliceHeatFiniteHeadReduction; ALDG:HermiteHeatRootBarrier; [LA](#la).

<a id="li"></a>
### LI — Paired Li and prime–Gamma balances

- **Path:** Literal prime−Gamma history → signed lower floor → Li positivity → RH.
- **Proved [L]:** Exact paired histories; every-positive-rate actual-clock lower floors iff RH. Unconditional reciprocal-depth rate≤1/431; this rate is not raw zero width.
- **Open:** Actual subexponential lower floor, or stronger finite lower bound for the literal primitive, retaining first-crossing and outside correlations.
- **Sources:** R:LiEvenCrossActualClockGrowthLaw; R:LiSignAlongSquares; R:PaperLiNegativeOperator.

<a id="sz"></a>
### SZ — Suzuki screw and shifted-kernel limits

- **Path:** Complete signed boundary pairing → screw nonnegativity or shifted-Ξ confinement → RH.
- **Proved [L]:** Full compact-L² first variation, including infinite primary energy; literal high-dyadic source deficit and RW sign transfer. Moving-primary Fatou lower bound and arithmetic finite-head convergence. Noncompact/high-scale families retain their scope.
- **Open:** Complete first-variation sign on an RH-complete family, especially low/mixed modes. Source-dependent small-shift neighborhoods and restricted high-scale positivity do not exhaust the receiver cone.
- **Sources:** R:Suzuki/SuzukiCriticalL2FirstVariation; R:Suzuki/SuzukiCriticalLiteralFamilyContraction; R:Suzuki/SuzukiCriticalMovingPrimaryEnergy; R:Suzuki/SuzukiCriticalMovingWindowDeficit.

<a id="pm"></a>
### PM — Physical-model Haar approximation (FZZ-P)

- **Path:** Global dyadic Haar approximation or cofinal signed-damping admission at ε↓0 → RH; alternatively positive gauge mass for every actual subcritical cofactor limit. [PW-B](#pw-b) remains a candidate sub-branch.
- **Proved [L]:** Complete-energy/gauge-mass receivers, half-damping admission and escape alternative. Hardy-to-literal energy transfer: Eε(T)≤Cκ(T+1)^κ for every κ>max(0,2Θ−2ε−1), Θ=zero abscissa; actual dominance at an attained rightmost zero is discharged. Simple-pole atoms and finite residue-capacity bounds; Abel cofactor Gram formula. Effective higher-pole order=max(ordρζ−ord_(ρ−ε)ζ,0); exact compact-window maximal-order atom laws and unbounded-order infinite-height escape.
- **Open:** Cofinal complete-energy bound as ε↓0, or positive gauge mass for every actual subcritical limit. Endpoint energy bounds, exterior mass/tightness and exclusion of infinite-height escape remain open. Finite-atom Gram limits still need exterior o(1/e); compact higher-pole laws do not supply it. Paid-cofactor synthesis/coercivity and sharp-horizon transfer remain open.
- **Sources:** R:FermiNymanHaarApproximationEquivalence; CP:TheEscapeCompletenessCriterion; CP:TheReceiverEnergyGrowthAtTheZeroAbscissa; CP:TheAbelCofactorGramsSelectTheDominantZeros; CP:TheEscapeEnergyAtTheAbscissaPaysTheResidues; CP:CompactReceiverWindowsSelectTheMaximalVisibleOrder; CP:UnboundedVisibleOrdersForceAbelEscapeToInfiniteHeight; ACG:RHIsTheVisibilityOfEveryEscapeState; [ADR](#adr), [BVI](#bvi).

<a id="jas"></a>
### JAS — Joint ancestry

- **Path:** Level-one prime-product Weil positivity or finite-power square-shell subpower Riesz bound → RH.
- **Proved [L]:** Exact level-one, torus-density and finite-power receivers. Gamma–theta source admitted at all finite supports/phases/grades. Unconditional positivity reaches a growing logarithmic prime budget.
- **Open:** Sign at the y^(1/2) level-one budget, all-amplitude damped-shell positivity, or every-exponent subpower bounds on m<k≤m+m/log(m+1). Admission does not close the logarithmic-to-power budget gap.
- **Sources:** R:JointAncestryLevelOneCapstones; R:JointAncestrySquareShellFinitePowerCriterion; R:JointAncestryEndpointBudgetProducer.

<a id="ctf"></a>
### CTF — Chronological tail / Báez–Duarte approximation

- **Path:** Bounded chronological Bose/Möbius rows or finite Báez–Duarte dilates → L² error→0 → RH.
- **Proved [L]:** Approximation/dual-sampling receivers; residual=(1−Λ-readout)²+centered pronic energy. Literal −μ_N aligns the readout; exact Rayleigh/cofactor identities and logarithmic lower floors.
- **Open:** Bounded rows with complete error→0, or arithmetic dual-sampling bound. Control centered energy jointly with moving cutoffs/small damping; readout alignment and diagonal control are insufficient.
- **Sources:** R:ChronologicalRiemannEquivalence; R:ChronologicalDualSamplingCriterion; V:VonMangoldtReadoutFormOfTheBaezDuarteCriterion; V:TheDualProblemRayleighQuotientAndCofactorCuspLaws.

<a id="hcf"></a>
### HCF — Gaussian heat trace / critical feature variance

- **Path:** Exact arch−prime heat trace → one-sided vertical growth or all-degree positivity on both prime-log grids → RH.
- **Proved [L]:** Centered Gaussian explicit formula, fixed-rank signs and multiplicity-exact inertia. Positivity on both literal log2/log3 grids with polar cancellation iff RH; one grid admits aliases. Arbitrary-zero detector formalized via SRT; alternative centered-heat derivation [P].
- **Open:** Both actual grid signs at every degree/height, or one-sided vertical/prime-chirp bound. Finite ranks and one-grid offsets do not suffice.
- **Sources:** R:XiGaussianHeatRouteCapstone; R:XiGaussianHeatTwoPrimeSourceSampling; R:HeatGridAliasingBoundary; S:SmoothWeilDetectorPolynomialAperture.

<a id="xn"></a>
### XN — Xi Newton invariant discs

- **Path:** Xi first jets → line-centered Newton self-map discs covering every zero → RH.
- **Proved [L]:** Coverage/self-map criterion and exact nonnegative Laplacian of interior margin. Polynomial pole repair preserves reflection/root jets, not self-mapping.
- **Open:** Cover every zero with discs having nonnegative interior margin. Boundary sign does not pay the curvature Green potential; scalar damping offers only trivial repair.
- **Sources:** R:XiNewtonSchwarzPickCriticalLine; R:XiNewtonDiscSourceMargin; R:XiNewtonDiscCurvature; R:XiNewtonScalarDamping.

<a id="bag"></a>
### BAG — Deterministic zeta self-return

- **Path:** Fixed-base ζ recurrence throughout the right strip, or cutoff-uniform positive Haar mass of target-ζ twists → RH.
- **Proved [L]:** Strong/local recurrence and positive-Haar-mass receivers; weak recurrence ladders collapse to RH. Finite-head approximation retains target-zero exceptions.
- **Open:** Actual recurrence near every right-strip point at every tolerance. Zero-free-target universality, conull recurrence and cofactor returns do not remove possible actual-zero exceptions.
- **Sources:** R:ZetaStrongRecurrenceReceiver; R:ZetaWeakRecurrenceLadderCollapse; R:PaperZetaReturnSpectralCriterion.

<a id="ewu"></a>
### EWU — Even pole-weight uniqueness

- **Path:** Actual even blind minimum≥0 at every aperture → even positivity → λ=Λ → RH.
- **Proved [L]:** Weight rigidity; attained aperture-antitone minima with exact RH criterion. Full positivity for sufficiently high dyadic/polynomial windows and separated lacunary unions; dense-window estimates retain high-energy dominance. Full/even compact C² floor≥‖f‖₂²/5000 through radius 181/500 [S]; this local floor also holds for every weight with w(2)=log2.
- **Open:** All-aperture minimum≥0, or full-positive weights at every finite aperture. Pay low/mixed modes on an RH-complete cone; restricted-family positivity does not pass through arbitrary tent approximation or polar-nonclosed limits.
- **Sources:** R:EvenSectorPoleWeightUniqueness; R:EvenSectorBlindVariationalAttainment; A:DenseScaleWindowsAndMultiWindowPositivity; A:FromTheCriticalFamilyToTheReceiver; A:SourceSelectionInTheFullWeilCone; SP:LiouvilleOddWindowRefutationAndSelectiveFullPositivity [S].

<a id="gta"></a>
### GTA — Transverse Schur charge

- **Path:** Actual theta-stage positive quartic Schur charge → rank-uniform transverse decay → RH.
- **Proved [L]:** Exact late-stage decay criterion; strong finite-truncation convergence, positive charge and compact/ideal diagnostics.
- **Open:** Rank-uniform arithmetic transverse-energy decay independent of zero data. Strong finite-prefix convergence is insufficient.
- **Sources:** R:Hedenmalm/HedenmalmThetaSchurQuarticSpectralDecayEquivalence; R:PaperThetaSchurModeCharge; R:PaperThetaSchurCompactGap.

<a id="owu"></a>
### OWU — Odd Weil-weight uniqueness

- **Path:** Actual-Λ odd positivity, or odd-positive weight plus all-scale dilation-ray sign → RH.
- **Proved [L]:** Odd/polar-hyperplane criteria, local floors and twisted full EF transport. At radius 181/500, edge mass≤‖F‖₂²/1961 implies Liouville-twin positivity; any negative witness must exceed it. First-prime twist comparison retains Gamma/pole corrections; multi-prime repulsion prevents exact vacuum alignment. Smooth odd radius-181/500 witnesses separate actual Λ positively from both its Liouville twin and the single-atom-2 sign flip negatively [S]. At radius 23/40, where atoms 2 and 3 are read and the {2,3} flip is not a height twist, one smooth odd witness has W_Λ>‖F‖₂²/25 and W_λ<−(3/10)‖F‖₂² [S].
- **Open:** All-aperture actual-Λ odd sign or full reflected-prime/polar payment. Companion-forcing certificate and conductor horizon have no common aperture for 0≤δ≤1/2; need stronger signed estimates or a different detector, then companion-cluster exclusion. Local twin separation supplies neither global positivity nor full prime-phase selection.
- **Sources:** B:OddSectorPolarHyperplaneAndPoleWeightSynthesis; R:WeilMarkovOddPositivity; R:WeilDilationRayCriterion; R:OddSectorBlindVariationalAttainment; CP:TheFirstGaugeChargedWindowOffTheEdge; BGG:MultiPrimeDiophantineRepulsion; CDG:TheConductorForcingGap; SP:LiouvilleOddWindowRefutationAndSelectiveFullPositivity [S]; SP:TwoPrimeCatalanSeparationAndContinuumTowerObstruction [S].

<a id="pbm"></a>
### PBM — Regularized prime/log-ζ abscissa

- **Path:** Fixed pole-regularized coefficients → Dirichlet convergence at every real σ>1/2 → RH.
- **Proved [L]:** Either series Σ(1_ℙ(n)−1/log n)n^(−σ) or Σ((Λ(n)−1)/log n)n^(−σ), over n≥2, gives an exact RH criterion. Weaker prime-gap continuation available.
- **Open:** Actual coefficient cancellation to the critical abscissa. Regularization supplies no cancellation; prime-gap alternative also needs exponent≤1/2 and zero-freeness.
- **Sources:** R:RegularizedLogZetaAbscissa; R:PaperPrimeRegularizedIdeal; R:PrimeGapDirichletContinuation.

<a id="rb"></a>
### RB — Robin/Nicolas divisor-sum criterion

- **Path:** Extremal divisor sums/primorial Mertens product → eventual Robin/Nicolas inequality → RH.
- **Proved [L]:** Exact eventual criteria; reduction to colossally abundant integers; fixed k-free/exponent-defect margins. Large counterexamples require growing lcm cores and small moving valuation defects.
- **Open:** Square-root-scale remainder inequality on increasingly prime-saturated extremizers/primorials. Necessary divisibility constraints are not a contradiction.
- **Sources:** R:RobinCriterionRiemann; R:NicolasInequalityRiemannConverse; R:RobinColossallyAbundantReduction; B:RobinMovingValuationDefect.

<a id="srt"></a>
### SRT — Prime-side one-parameter lag localization

- **Path:** Any fixed 0<w<log2/2: explicit spline prime–archimedean difference-bump sign at sufficiently late lags → RH.
- **Proved [L]:** Every-width receiver, exact rates, orbit/index laws and polynomial-aperture detection. One prime/all short tests or one shift/unrestricted supports suffices. Twisted sinh detector is σγ-odd; sign+local-count+depth dominance forces a companion. Conductor-horizon positivity requires C+(4+ε)e^a+2≤log(1+|γ|/8) and both derivative-tail bounds. Prime-symbol recurrence forbids uniform eventual power savings, not full Weil positivity.
- **Open:** Actual-Λ late-lag lower bound at every positive exponential slack, zero-rate orbit bound or sufficient horizon containment. Pay cross-window correlation at unbounded separation. Existing companion forcing requires e^(2δa)>768A log(|γ|+3), incompatible with the conductor horizon for 0≤δ≤1/2, A≥1. Need improved signal/cost or independent full detector sign, not this splice.
- **Sources:** S:EveryWidthDecidesTheCriticalLine; S:ZetaLagFamilyVinogradovKorobovEnvelope; S:SmoothWeilDetectorPolynomialAperture; G:OneSidedLefschetzBoundsAtOnePrimeAreTheStrip; PL:TheForcingHalfOfEllipticLocalization; PL:ThePriceOfEllipticLocalization; A:SingleHeightPhaseSelectiveApertureAndPowerSaving; CDG:TheConductorForcingGap.

<a id="act"></a>
### ACT — Arithmetic criticality / single-shift variation

- **Path:** One fixed theta shift a>0 → D_a(u)≤2S_a(u)+V_a(u) for every even compact C² profile → odd Weil positivity → RH.
- **Proved [L]:** Exact ground-state variation/receiver; continuum light-cone positivity; fixed-support subunit reflected-prime collar paid at sufficiently large shift. Small-window floors and signed-moment identities.
- **Open:** One fixed a paying every support/profile, including exterior primes and signed/polar remainder. Support-dependent absorption does not give this uniform inequality.
- **Sources:** D:ShortProfilePoleFreeVariationInequality; D:SignChangingTwoMomentAndAtomPoleIntegralLaw; D:RestrictedWeilGroundEnergyCriticalAtInfinity.

<a id="aip"></a>
### AIP — Arithmetic incidence positivity

- **Path:** Actual prime incidence + plateau gauge → all-aperture GlobalIncidenceAllocation → odd positivity ↔ RH.
- **Proved [L]:** Full incidence identity; allocation iff RH; shared-resource laws, lattice Schur reduction and odd floor through 181/500. Finite gauge conjugacy/successor selection; log-cell remainder controlled by weighted coefficient variation. Full-form radius-181/500 Λ/Liouville and single-atom-2 separation [S] shows finite-lattice gauge conjugacy does not extend to the complete Gamma/polar form. Raw continuum prime towers have negative edge energy of order e^A, excluding sub-half exponential H¹ floors [S].
- **Open:** Joint full-continuum prime/Gamma/pole payment with signed remainder. Raw-tower no-go does not apply to the pole-neutralized full odd form. Off-diagonal terms cancel the apparent linear diagonal reserve; no reserve reuse. Finite phase selection and cell bounds supply neither a prime-summed remainder budget nor full-form sign.
- **Sources:** I:GlobalIncidenceAllocationCondition; I:GlobalSharedSurplusAllocation; S:TheIncidenceLedgerGradedByTheZeroWidth; M:TheCompensatedRemainderOfTheFullLedger; BGG:EuclideanCellRemainderAndPolarNeutralCollapse; SP:TwoPrimeCatalanSeparationAndContinuumTowerObstruction [S]; SP:LiouvilleOddWindowRefutationAndSelectiveFullPositivity [S].

<a id="acs"></a>
### ACS — Arithmetic Castelnuovo–Severi effectivity

- **Path:** Arithmetic effectivity/bounded-error Rosati heights → Hodge → RH; equivalently all-ordinate positive-deformation chirality or rational/positive central-vanishing ceilings.
- **Proved [L]:** Source RR, restricted Meyer RR+Bézout and effectivity/Tate/height receivers; faithful degree needs RH+simple zeros. Positive chirality at every nonzero ordinate and rational/positive central ceilings each iff RH. Positive prime-mass rigidity at γ iff no ξ zero has ordinate γ; full two-sided scalar rigidity fails at every ξ-zero ordinate and is unproved at zero-free ordinates. Under horizontal off-critical exclusion and no central drop, prime-deficit abscissa≤1/2 with zero Abel residue forces coefficient equality/scalar proportionality; strict sub-half deficit suffices. A central excess forces deficit abscissa≥1/2 with Abel residue≥the excess. For completed ζ^d deformations, sub-half deficit and κ≤d force κ=d and F=Kζ^d on Re s>1 without horizontal zero exclusion. These are source-class rigidity, not actual Hodge sign.
- **Open:** Actual arithmetic h⁰ with quadratic RI+degree-zero subquadratic growth, bounded-error Rosati heights, or source-derived all-ordinate chirality/central ceiling. The deformation equivalences do not prove their input. Deficit/rigidity theorems retaining horizontal zero exclusion cannot discharge it. Positive coupled counts and theta heights remain nonselective.
- **Sources:** G:ExactArithmeticSourceEffectivity; AE:TheEffectivityCalculus; AE:NaiveHeightsAreTraces; BGG:PositiveCoupledRigidityAndTheCriticalTransferLaw; BGG:StrongMultiplicityOneBelowTheSquareRootDeficit; BGG:TheDeficitResidueBoundsTheCentralExcess; BGG:StrongMultiplicityOneForPowersOfZeta; [effectivity support](#arithmetic-effectivity), [BGG](#biarithmetic-gauge), [APD](#apd).

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
| <a id="ptr"></a>**PTR — Photonic source:** prime-faithful lossless stack → real-rooted Ξ limit. | Finite lossless real-rooted stacks; Ξ-limit criterion. Existing converse uses unknown Ξ zeros; continuum port has unit gap. | Independent nonlocal prime-faithful port preserving exact Ξ, or zero-loss mechanism overcoming that gap. | R:PhotonicLosslessProductPortRH; R:PaperPoissonCompletionGap |
| <a id="rfhm"></a>**RFHM — Support grade:** faithful phase/depth source → non-inverse-covariant wall law. | Full finite-support/phase/grade admission, forward creation and strong cutoff exhaustion. | Source-defined symmetry-breaking phase/depth/compound law with arithmetic wall orientation. Reversible sewing remains inverse-covariant. | R:GammaThetaFullSupportSource; R:PaperRFHMSurvivalInformation |
| <a id="sc"></a>**SC — Stokes/Witt−Krein:** cross-fibre indefinite invariant → orientation. | Rigged fibres, Fourier reconstruction and finite Witt/Selberg coordinates. | Source-fixed cross-fibre restriction/index selecting the wall; canonical polarization is wall-singular. | R:PaperKreinWallFourierCompletion; V:WittSelbergReceiverCoordinates |
| <a id="sec"></a>**SEC — Adjacent prime seam:** exact compactness/Fock boundedness → seam jump zero. | Essential norm=seam jump; exact vanishing and time-one factorial-Fock criteria. | Pre-divisor proof of exact eventual compactness or Fock boundedness at actual zeros. Asymptotic seam smallness is nonselective. | R:XiPrimeSeamAdjacentEssentialNormNoGo; R:TimeOneGammaJetFockRHCriterion |
| <a id="w1c"></a>**W1C — Clifford–Dirac / centred Lee–Yang:** arithmetic operator or ferromagnetic limit → real-rooted Ξ. | Finite Lee–Yang theorem and Ising-limit receiver; explicit density/field constraints. | Source-defined couplings converging to Riemann's measure with centred slow-field law, or faithful arithmetic scattering denominator. | R:LeeYangIsingGraphDatum; R:IsingLawConvergenceRH; R:HermitianPencilEulerFactorObstruction |
| <a id="wbf"></a>**WBF — Source certificates:** arithmetic stream → depth-uniform positive completion → Ξ. | Abstract genealogy Gram/Fredholm recovery and relative determinants; no arithmetic coupling. | Arithmetic certificate stream and source-faithful uniform-depth completion landing on Ξ/Weil positivity. | H:PaperGenealogyFredholmRecovery; H:PaperCriticalGenealogyCompletion |
| <a id="pw-b"></a>**PW-B — Physical cusp forcing:** PM sub-branch; cusp response → zero-damping exclusion. | Native two-response action, positive-damping admission and principal/forced limits. | Remove XiZeroCopy indexing; complete-energy ceiling and action→optical magnitude→ordered cap→all-divisor extinction. | R:ThetaCusp/ThetaCuspHawkingBMPWNativeTwoResponseAction; R:ThetaCusp/ThetaCuspHawkingBMPrincipalSmallDamping |

## Supporting research frameworks

Not routes/candidates. Entries identify tools and unresolved transfer; route-specific conclusions belong above.

| Framework | Feeds | Established contribution / boundary | Source entry points |
|---|---|---|---|
| <a id="bvi"></a>**BVI — Bézout–valuation incidence** [L/S] | MC, PM, CTF | Λ readout/pronic decomposition; fixed-modulus and below-diagonal cancellation; exact kernels and diagonal estimates. Balanced/centred-prime band power saving iff Θ<1 [L], not an actual saving. Whole moving-scale signed estimate remains open. | V:TheBalancedStatisticIsTheQuasiRiemannHypothesis; V:TheMoebiusTailStatisticAtLargeModuli; V:TheMeanValueIsTheLeadingCoefficientOfTheReceiver |
| **ArithmeticCompensationTheory (ACCC)** [L] | AIP, MC, RW, ACT | Exact compensated identities and norm-specific rate dictionaries; no arithmetic zero-rate producer. | M:TheCompensatedRemainderOfTheFullLedger; O:TheWidthDictionary |
| **SignedArithmeticEnergyIncidence (SAEI)** [L] | AIP, MC, PM, CTF | Graph/frustration, packed-path payment and receiver coordinates. Local PSD/payment does not prove full continuum sign. | SAEI:FrustrationIsPaidAlongCanonicalPaths; SAEI:CycleHolonomyDecidesBalance |
| **SignChangingScrewGauge (SCG)** [L] | AIP, ACT | Signed gauges, folded potentials and moment cancellation; middle-region/remainder sign open. | D:SignChangingTwoMomentAndAtomPoleIntegralLaw |
| **ArithmeticOrientationTheory** [L] | HF, ACS, AIP, PM, MC | Section/rate dictionaries and paid-quotient diagnostics; no independent orientation or index ceiling. | O:TheEffectivityConeFromSections; O:TheWidthDictionary |
| <a id="aog"></a>**ArithmeticOrientationGeometry (AOG)** [L] | HF, ACS, WD, SRT, PM | Source/configuration equality, orbit/index/rate laws, theta h⁰ and finite-Euler invariance; source sign open. | J:TheScalingDatumOfAConfiguration; J:TheOrientationOfACycle; J:TheIndexExit |
| <a id="adr"></a>**ArithmeticDefectRigidity (ADR)** [L] | PM, MC | ζ/η symbols, exact residual kernel, bounded-energy Mellin holomorphy and translated-zero escape classifications in their stated finite-rank/nonresonant classes. Actual escape completeness and inverse coercivity open. | [corpus](../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/) |
| <a id="biarithmetic"></a>**BiarithmeticGeometry** [L/S] | WL, HF, ACS, AIP, PM, MC | Degree-minus-log-torsion identity, affine/source-domain calibration and exact escaped-boundary accounting. Finite affine rigidity and normalization freedom do not produce arithmetic sign. | BG:ArithmeticEulerCharacteristic; BG:HorizonBoundaryCalculus; BG:SharedBudgetDescent |
| <a id="biarithmetic-gauge"></a>**BiarithmeticGaugeGeometry (BGG)** [L] | AIP, OWU, ACS, HF | Lattice anchors, multi-prime repulsion, positive/rational deformation laws. Abel-negligible boundary errors suffice for the positive-definite divisor-jump law. Height-coupled zero-Abel-residue rigidity retains horizontal zero exclusion; ζ^d sub-half-deficit rigidity with κ≤d does not. At Re s=1, zero-residue deficit yields d≤κ and 2Σ_(t∈Z)ord_(1+it)Λ≤κ−d for every finite Z⊂(0,∞); κ≤d+1 excludes nonreal boundary zeros, not interior zeros. For finitely moving positive deformations of ζ_γ without off-critical zeros at γ, the central drop is at least twice the net number of created critical zeros [S]. | BGG:TheAbelGramLawOfPositiveDeformations; BGG:StrongMultiplicityOneBelowTheSquareRootDeficit; BGG:StrongMultiplicityOneForPowersOfZeta; BGG:TheBoundaryCapacityOfDeformationsOfPowersOfZeta; BGG:TheCriticalConservationLaw [S] |
| <a id="mpg"></a>**MPG — Multiplicative positivity geometry** [L] | ACS | Boundary capacity/profile realization and integer-family classifications; sharp finite-cosine forcing limits. Boundary positive weights are not a completed Euler/FE system or RH-strength interior estimate. | [corpus](../../formal/GaloisForLFunctions/MultiplicativePositivityGeometry/); MPG:ExactFejerBarrier; MPG:GrowthToForcing |
| <a id="apd"></a>**APD — Arithmetic positive duality** [L] | ACS, HF | Positive-measure theta/FE rigidity; Bochner/GNS and affine spectral classification. Every nonzero L² wave, and every finite dilation measure with nonzero absolutely continuous part, admits a visible affine extension. Atomic spectrum stays blind; singular-continuous necessity unclassified. Real dilation-orbit extension and weak GNS integration do not construct actual source-compatible mixed positivity. | APD:PositiveMeasureHamburgerRigidity; APD:EverySquareIntegrableWaveHasAVisibleSuccessor; APD:EveryDensityHasAVisibleAffineExtension; APD:TheArchimedeanDilationOrbitExtendsToRealScales; APD:TheGNSRepresentationInheritsWeakMeasurability |
| <a id="acp"></a>**ACP — ArithmeticCorrespondencePositivity** [L/S] | ACS, HF, WL, MC, PM, OWU | Literal energy/zero-abscissa and compact effective-pole/escape laws [L]. Prime-error linear budget forces RH and genus floor; all-c integrability plus genus Abel slope forces RH+simple zeros. Finite-curve Mertens budget iff purity+simple spectrum; exact repulsion slope, elliptic full-reciprocal budget iff strict Hasse in the noncancelled class [L]. RH-conditional prime-error partial fractions [S] do not prove actual budget/saturation or exterior tightness. | CP:AnAbelSlopeAtTheGenusIsRHWithSimpleZeros; CP:AMertensBudgetIsPurityWithASimpleSpectrum; CP:TheMertensBudgetOfAnEllipticCurveIsStrictHasse; CP:CompactReceiverWindowsSelectTheMaximalVisibleOrder; CP:UnboundedVisibleOrdersForceAbelEscapeToInfiniteHeight; CP:ThePrimeErrorSymbolSplitsAtTheZeros [S] |
| <a id="arithmetic-polarization"></a>**ArithmeticPolarization** [L/S] | ACS, HF, OWU, PM, RW | Faithful collided form, one-shift similitude⇔RH, depth rates and logarithmic Weyl growth. Signed Weil Gårding bound, finite negative index and collided L² coercivity at every fixed aperture [L]. Section positivity and commensurable Fejér–Riesz coupling [L]. Local convolution bound [S], not yet a declared log-Sobolev norm equivalence. No translation invariance or zero negative index follows. | PL:TheCollidedFormIsAPolarization; PL:TheDepthProfileCarriesTheGlobalCollision; PL:OneVerticalSectionDecidesPositivity; PL:PositiveLatticeLinesAreCouplings; PL:TheCollidedFormSamplesHighFrequencies; PL:TheCollidedFormIsCoerciveAtEveryAperture; PL:WeilsFormHasFinitelyManyNegativeDirectionsAtEveryAperture; PL:TheCollidedFormIsTheLogarithmicSobolevNorm [S] |
| <a id="conjugate-diagonal"></a>**ConjugateDiagonalGeometry** [L/S] | HF, ACS, OWU, SRT | Positive ξ-curvature/current; explicit finite integer theta prefixes recover collided/depth moments uniformly over sourceTestSize≤1 and a+j\|L\|≤2log(n+1), \|τ\|≤n/2, after 4^j normalization [L]. Error≤B exp(−n⁴+68n²+66)+O(log n/n). Finite theta sum, still continuous integrals; no quadrature or defect upper sign. Fixed-horizontal-strip cutoff with height-independent derivative bounds [S], not a polynomial-prefix metric theorem. | CDG:XiSourceCurrent; CDG:FiniteThetaMetric; CDG:FiniteThetaApertureMetric; CDG:TwoScaleDepthRigidity; CDG:TheConductorForcingGap; CDG:StripSourceCutoff [S] |
| <a id="arithmetic-effectivity"></a>**ArithmeticEffectivityTheory** [L/S] | ACS, HF, WL, SRT, MC | Effectivity/Tate/height receivers; polar-box RI iff Hodge; torsion=ψ and first Fourier=M [L]. Every squarefree odd-degree hyperelliptic curve over any odd-characteristic finite field, split or not, supplies unitary curve data, extension Hasse–Weil and bounded-error heights; elliptic Hasse for every odd-characteristic finite field [L]. Burgess moments, multiplicative energy and averaged-shift inequality [S]; no final classical short-sum bound or actual μ estimate. | AE:TheEffectivityCalculus; AE:NaiveHeightsAreTraces; AE:ThePolarBoxCount; AE:TheHyperellipticCalibration; R:HyperellipticDescent; R:EllipticCurveHasseBound; AE:TheBurgessMoment [S]; AE:TheBurgessEnergy [S]; AE:TheBurgessBound [S] |
| <a id="sbwf"></a>**StripBochnerWeilForcing (SBWF)** [L] | ACS, MPG | Completed-system shrinking collars and real-zero budgets. Simple-pole class exactly real nonzero multiples of ζ, d=1; κ=2 admits off-critical models. Source identification and real-zero contraction do not exclude nonreal interior zeros at κ=1. | SB:SharpHalfPoleCollar; SB:StripReflectionRigidity; SB:TheSimplePoleClassIsZeta |
| <a id="arithmetic-kunneth"></a>**ArithmeticKunnethTheory** [L] | HF, ACS | Total-support depth bound, diagonal product moments and Künneth–Adams count positivity. Golden impure datum satisfies the entire positive-count hierarchy. Actual signed product/trace mechanism missing. | AK:ProductReceiversSeeDepthOnlyThroughTotalLength; AK:KunnethPositivityIsPointCountPositivity |
| <a id="arithmetic-correlation"></a>**ArithmeticCorrelationGeometry** [L] | MC, PM, HF, ACS | Gauge classification/averaging, a.e. square-root and successor cancellation, Pell moments and escape spectral measures. μ exceptions are comeager/Haar-null; actual gauge point not selected. Positive mass/actual signed estimates remain open. | ACG:AlmostEveryGaugePointCancelsToTheSquareRoot; ACG:TheMoebiusExceptionalSetIsComeagerAndNull; ACG:RHIsTheVisibilityOfEveryEscapeState |
| <a id="aldg"></a>**ALDG — ArithmeticLocalDivisorGeometry** [L] | LA, WD | Actual finite-head coordinates; local repair cones, universal reflectors, sharp Hermite/heat barriers, attained extremizers and asymptotics. Model optimality does not supply actual all-height coefficient sign. | ALDG:SourceLocalFactors; ALDG:SourceDivisorGeometry; ALDG:HermiteHeatRootBarrier; ALDG:MaskedPairHeatThreshold |
| <a id="ssa"></a>**SignedSuccessorArithmetic** [L] | MC, PM, BVI | Sharp odd-shift/lag-2 logarithmic floors 1/3 and 1/4; successor cocycles, finite-field moments and signed half-damping endpoint. Twin extremizers prevent generic floors from proving actual μ/Liouville cancellation. | SSA:TheShiftFloorsAreExact; SSA:TheHypercubeFormIsBoundedAtHalfDamping; SSA:TheSizeTruncatedHypercubeFormIsTheReceiver |
| **TransThresholdPairCorrelation** [L/S] | HF, ACS | Actual certificate N₀*≥(29/36−ε)N−surplus; proper powers=o(N), not absolute o(1). β≤1/18 would give 3/4, not RH. Parity-blind adversarial brackets cannot pay coalescent budgets beyond bandwidth one [S]; actual phase/parity-sensitive prime correlation remains open. | P:SmoothWeightedCertificateAtFourThirds; P:CoalescentPrimeReductionAndParitySieve; P:RamanujanDirichletCoalescentTransfer; SP:ParityLobeObstructionAndEscapeLaplaceSplit [S] |
| **SelectivePositivityAndThresholdLaws** [S] | AIP, OWU, EWU, RW, SRT, MC, HF, ACS | Short-cycle/escaped-μ receivers, theta box RR, Jacobi-height models and parity/raw-tower obstructions. Full real/complex floor 1/5000 through radius 181/500; odd Λ-positive witnesses negative for Liouville and single-atom-2 twins at that radius; some nonzero shifted-pair even witness negative there. Higher primes remain unseen when 2A<log3. At radius 23/40 one odd witness is Λ-positive (>‖F‖₂²/25) and Liouville-negative (<−(3/10)‖F‖₂²); the full ζ floor there is not certified. Support, not independent route; all-aperture sign open. | SP:JacobiHurwitzTorsionInflationAndShortCycleHeights; SP:MoebiusEscapedPairingBoundaryLaw; SP:SerreDualScalingCohomologyAndLargeSieveSections; SP:TwoPrimeCatalanSeparationAndContinuumTowerObstruction; SP:LiouvilleOddWindowRefutationAndSelectiveFullPositivity |
| <a id="closed-cycle-tools"></a>**Controlled closed-cycle recovery** [L] | HF, EWU | Source derivative/collar bounds and finite-cycle recovery with explicit conditioning/tail losses; reconstruction, not signed Weil positivity. | B:ControlledClosedCycleRecovery; B:ClosedCycleDataResiduals |
| **Finite-window incidence / concrete certificates** [L] | PM, BVI; shared | Sharp finite variance/coercivity, finite sieve realization and finite source/receiver examples. Constants grow with horizon; no cofinal admission or global positivity. | B:FiniteWindowVariance; B:WeightedDoublingIncidence; O:ConcreteSourceDictionaries |
| **Analytic large-value / zero-density tools** [L] | WL, ACS; shared | Guth–Maynard/Heath–Brown, sharp S₂, zero-density and frequency-averaged floors. Exceptional frequencies/zeros and actual unfiltered energy remain uncontrolled. | R:ZetaZeroDensityThirtyThirteenths; R:Sieve/HeathBrownPairSumAllLengths; B:ZeroDensityFilteredCriticalDeficitLaw; G:ZeroDensityFilteredWeilPositivityAndCoercivity |
| **Producer / clock / node-phase calibration** [L] | FU, EWU, HF, CHMD, PM | Source mass/energy convergence, finite clock decomposition and phase-sensitive receivers; no full signed cone or prescribed arithmetic phase selection. | B:CompensatedPhysicalProducerFormLimits; B:ProducerCompletionAndPrimeClockKernelSynthesis; B:NodeCriticalityPhaseSensitivityAndCalibrationSynthesis |
| **Critical Nyquist finite-part tools** [L] | EWU; shared | Quantitative primitive/tail limits and mean-zero versus positive-mean source classification; no full Weil sign or polar-neutrality transfer. | B:NyquistCriticalSourceClassification; B:NyquistCriticalSourceQuantitative |
| **Spectral-realization synthesis** [L] | RW, EWU, PTR | Determinant/operator constraints, packet decoupling and Sonin cutoff boundaries. Growth/Poisson-balance inputs remain; no constructed Ξ operator. | A:SpectralRealisationAndOperatorConstraints |
| **Gaussian / TP₂ tools** [L] | TG; shared | Gaussian integer log-concavity and coprime divisibility covariance; no arbitrary signed/Euler-inverted form control. | R:GaussianIntegerLogConcavity; R:GaussianDivisibilityCorrelation |
| **ReflectiveDirichletPolynomialS2** | MC, BVI | Reflection/S₂/dispersion transfers; RH-strength balanced cancellation open. | [corpus](../../formal/GaloisForLFunctions/ReflectiveDirichletPolynomialS2/) |
| **ReverseTwistedArcPoleCompression** | RW, OWU | Pole-receiver reformulation; independent sign producer missing. | [corpus](../../formal/GaloisForLFunctions/ReverseTwistedArcPoleCompression/) |

## Dead mechanisms / scope boundaries

**Authoritative catalogue:** [rh-killed-routes.md](rh-killed-routes.md). Each obstruction has its scope, positive survivor and remaining replacement problem. No obstruction below retires an entire live route unless the catalogue says so.

| Lookup | Contents |
|---|---|
| [Named dead mechanisms](rh-killed-routes.md#dead-mechanisms) | 44 named mechanisms, exact failures and survivors. |
| [Retired labels](rh-killed-routes.md#retired-labels) | 19 retired labels; not extra live routes/candidates. |
| [Route-class obstructions](rh-killed-routes.md#route-class-obstructions) | Information, realization, norm and sign-transfer limits. |
| [ULF obstructions](rh-killed-routes.md#ulf-obstructions) · [endpoint no-gos](rh-killed-routes.md#endpoint-no-gos) | Restricted forcing and endpoint failures. |
| [Scoped catalogue](rh-killed-routes.md#scoped-catalogue) | Local/model mechanisms; do not generalize beyond stated hypotheses. |

## Source locator

`K:Module` = `formal/GaloisForLFunctions/<directory>/Module.lean`. Entry points, not exhaustive theorem inventories. Search exact names with `scripts/formal_tools.py research "<name>" --mode lexical`; inspect Lean statements for full scope.

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
| SP | SelectivePositivityAndThresholdLaws | — | — |

## Alias lookup

BVI→[support](#bvi); C1→RW; CCM-FU→FU; CLG/TTF,K-RVM,S6F,TCD,UEB→TH; CSB,STC,U,MPLF,RHist,BPC,TQFQ,WS2,SQB→RN; D2,Q,RG,RG-ETA,TK→PA; E,EDQ,L,HDL,PSRC→MC; FZZ-P→PM; PW-B→[candidate](#pw-b); G,HC→WD; O→WL/RW (genus mechanism dead); P,SP-E→RP; SV2,RG-HF→SZ; T1,T2,Route T→TT; Route T successor/ULF sub-unit anchor→TG; Deninger→HF. [Retired labels](rh-killed-routes.md#retired-labels).
