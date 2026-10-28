# RH proof-route frontier

**RH open. 31 live routes; 17 standalone candidates; PW-B candidate sub-branch.**
**Corpus checkpoint:** `f61abdc4d4750cf10e6c73da732a88289483d98b`.

**Evidence:** [L] integrated Lean source at checkpoint, not a fresh kernel audit; [S] working/unintegrated/unfinished source, not certified closure; [P] paper only; [E] external claim, not locally validated.
**Classes:** live = source observable + proved RH-sufficient receiver + explicit open estimate; candidate = missing independent source mechanism/landing; support = tools feeding routes. A receiver does not prove its input.

[Find a route](#find-a-route) · [Live](#live-routes) · [Candidates](#route-candidates) · [Shared tools](#supporting-research-frameworks) · [Killed mechanisms](rh-killed-routes.md) · [Sources](#source-locator)

<!-- Replace facts in place. Preserve mathematical scope and evidence labels.
No chronology, work packages, theorem inventories or progress notes. -->

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

| Established | Still required |
|---|---|
| Full Weil floor≥mass/5000 and odd floor≥mass/1000 through radius 181/500 [L]. Only prime atom 2 is visible there. | All-aperture sign with complete prime/Gamma/polar terms; local floors are not source selection. |
| RH ⇔ width zero ⇔ full/even/odd Hodge defect zero ⇔ cofinal damped-μ admission ⇔ vanishing Báez–Duarte residual ⇔ positive mass of every actual subcritical gauge limit [L]. | One actual arithmetic estimate; equivalences close none. |
| H¹ floor-rate and critical-deficit energy-rate sets are [zero-divisor width,∞), endpoint attained. Physical L² full/polar rates agree; form-norm/Birman–Schwinger infimal rates equal width [L]. | Rate zero; physical L² equality with positive width and form-norm endpoint attainment. Norms are not interchangeable. |

Sources: SP:LiouvilleOddWindowRefutationAndSelectiveFullPositivity; O:TheWidthDictionary; G:AllParityCriticalDeficitAndEndpointSobolevLaws; C:UnconditionalBirmanSchwingerRateReadsTheZeroWidth.

## Live routes

Done = [L] unless marked otherwise. All routes remain open.

<a id="wl"></a>
### WL — Weil lag function

- **Path:** Actual prime lag/deficit → one-sided bound or subexponential critical energy → RH.
- **Done:** Critical energy/cross-work and linear prime-error energy criteria; bounded high-zero tail. Genus Abel slope characterizes RH plus simple zeros.
- **Open:** Prove actual signed-correlation or linear prime-error energy bound. Genus saturation is stronger than RH.
- **Sources:** B:WeilLagCriticalDeficitEndpointAndLimitLaw; CP:TheAbelSlopeOfThePrimeErrorIsTheArchimedeanGenus.

<a id="rw"></a>
### RW — Restricted Weil ground energy

- **Path:** Complete prime−Gamma−polar form → ground minimum μ(A)≥0 at every aperture → RH.
- **Done:** Completed minima; μ strictly decreasing; RH iff μ(A)>0 at every finite aperture. Signed Gårding gives finite index; small-aperture floors proved.
- **Open:** Bound cumulative relaxation, paying low modes, collars and complete polar energy. No uniform positive gap at unbounded aperture.
- **Sources:** C:TheApertureFlowNeverStalls; C:ThePrimeShellBetaFunction; [Gamma reserve](#touching-mixed).

<a id="fu"></a>
### FU — CCM-FU signed prime scheduling

- **Path:** Signed prime/Möbius history → completed Abel moment A(M)/M bounded above → RH.
- **Done:** Exact receiver, prime-exhaustive schedules, clock kernels and narrow-window negative prime channel [L]. Wide-window channel can be positive [S].
- **Open:** Joint bound for seed, drift, prior action, cross-block covariance and endpoints.
- **Sources:** R:CCM/CCMFUSuzukiMobiusDivisorOneSided; B:PrimeGraphClockCorrelationKernels.

<a id="rp"></a>
### RP — Route-P / SP-E history floor

- **Path:** Matched−quantile prime history → eventual linear defect floor → RH.
- **Done:** Exact history-floor criterion; hyperbola/centroid/square-debt identities; low-LCM payment; native first-clock-jet admission.
- **Open:** Pay high-LCM pairs, moving core and singular-domain transport in one complete-history floor.
- **Sources:** R:SPEQuantileRieszRoutePLinearFloorCriterion; R:RoutePLcmPairPayment.

<a id="pa"></a>
### PA — Prime–archimedean source passivity

- **Path:** Exact prime−archimedean trace → current sign, subexponential Bernstein mismatch or positive signed compact moments → RH.
- **Done:** Exact source/trace receivers. Each fixed Hausdorff order is positive at sufficiently large shifts.
- **Open:** All-order/all-shift positivity, high-frequency current sign, or every-positive-rate mismatch bound; order-dependent thresholds leave a signed complement.
- **Sources:** R:PrimeArchEndpointFrequencyAccretivity; R:PrimeArchHausdorffFixedOrderLargeShiftPositivity.

<a id="mc"></a>
### MC — Möbius cancellation at half power

- **Path:** Actual μ cancellation/subpower energy or square-sampled Chebyshev bound → RH; alternatively exclude every oscillating smooth-power probe below half damping.
- **Done:** Half-power/rate/strip dictionaries; fixed-modulus and below-diagonal savings; uniform escaped-μ VK decay in endpoint M=(N−b)/a, not uniformly in N over all multipliers.
- **Open:** Actual moving-scale cancellation at every strict half-power, or cofinal subpower energy. VK supplies no fixed power saving; M=o(√x) is false.
- **Sources:** R:MobiusHilbertFormEquivalence; V:UnconditionalEscapedMoebiusDecayAndCrossRouteBridge; [BVI](#bvi).

<a id="tt"></a>
### TT — Theta-tail and heat–Cassini currents

- **Path:** Theta source → directed covariance/Wold decay or odd Weil sign → RH.
- **Done:** Theta seam/tail and Wold receivers; sharp t<1/2 boundedness threshold; Φ-Doob identities retaining reflected primes; restricted current/light-cone signs.
- **Open:** All-test directed covariance or complete odd/primitive positivity, including signed reflected-prime interaction.
- **Sources:** R:PaperWoldDirectedCovarianceRH; R:WeilMarkovOddPositivity; [ACT](#act).

<a id="la"></a>
### LA — Line anchor

- **Path:** Theta source → all-height Laguerre/Jensen or heated coefficient sign → real-rooted Ξ → RH.
- **Done:** Exact coefficient receivers; finite-head/tail transfer; uniform high-order heated positivity [L]. Ordinary ξ coefficients are Turán [L], Lorentzian [S].
- **Open:** All-height/all-degree finite-head coefficient signs, including low orders and near-double off-line pairs. Ordinary-coefficient Lorentzianity is not factorial-normalized Jensen real-rootedness.
- **Sources:** R:XiSliceGaussianFiniteHeadPositivity; R:XiSliceHeatOrderUniformPositivity; [Lorentzian scope](#turan-layer).

<a id="tg"></a>
### TG — Topological sub-unit gate

- **Path:** Euler/Gaussian source → positive-residual transgression + integer trace<1 → RH.
- **Done:** Winding/index and cubic-transgression identities; central-gap receivers; Gaussian coprime-divisibility covariance.
- **Open:** Matrix-complete decomposition E_base=E_residual+Tr T_D with nonnegative residual and integer trace<1 on every disc, or zero-rate central-gap bound.
- **Sources:** R:FormationAnchoredCubicSpecialization; R:GaussianCentralGapExplicitCriterion.

<a id="hf"></a>
### HF — Positive Hodge form on arithmetic cohomology

- **Path:** Full-source sign / zero Hecke defect / subquantum arithmetic work → Hodge → RH.
- **Done:** Source/divisor and Hodge/Hecke-defect receivers; complete-cell transfer, separated-atom error control and restricted even-power + odd-mixed finite index [L]. Critical-work criterion [S].
- **Open:** Full signed-form nonnegativity or RH-threshold arithmetic work ceiling. Remaining prime blocks, polar terms and infinite low-generator orbits need joint control.
- **Sources:** J:TheIndexExit; PL:HeckeInvarianceOfTheCollidedPolarizationIsRH; [shared signed frontier](#signed-hodge).

<a id="chmd"></a>
### CHMD — Causal Hyperbolic–Modular Duality

- **Path:** Complete causal prime/Möbius wave bound or odd theta-Doob half-threshold bound → RH.
- **Done:** Wave/Doob/nodal receivers; completed core, exact radical, projection/Schur transport, physical Haar approximation and restricted even-power + odd-mixed index bound [L].
- **Open:** Full one-sided wave or odd/nodal bound. Pay reflected primes and poles; control signed form on infinite low-generator orbits. Finite generator count is not compactness.
- **Sources:** R:CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion; R:CHMDOddSectorCriterion; [Haar](#balanced-haar).

<a id="th"></a>
### TH — Theta moment positivity

- **Path:** Theta/prime−Gamma moments → all-degree Hankel/Bezoutian positivity → RH.
- **Done:** Low-order signs and all-rank strict positivity on nonnegative coefficient vectors at one common small positive heat time.
- **Open:** Arbitrary signed coefficients at every degree under one common heat time. Orthant positivity does not suffice.
- **Sources:** R:XiHeatHankelFormOrthantPositivity; R:XiHeatStableTestPositivity.

<a id="rn"></a>
### RN — Theta renewal and singular comparison

- **Path:** Theta renewal/connection source → divisor-faithful winding or directed boundary-work sign → RH.
- **Done:** Green/BV realization, multiplicity-exact packets and compact cone-positive renewal operator with exact regularized determinant/resonances.
- **Open:** Directed mixed prime+Gamma≥pole, retaining cusp/seam terms. Cone positivity does not imply real spectrum; native unregularized synthesis has a topology obstruction.
- **Sources:** R:ThetaRenewalPositiveFredholm; R:ThetaRenewalFredholmSpectrum.

<a id="wd"></a>
### WD — Ward orientation and horizontal collision

- **Path:** Directed source current → vanishing negative-cross cap/collision mass or collision charge<2 → RH.
- **Done:** Ward/collision receivers; attained extremizers and sharp Hermite asymptotics; shifted shallow-Cauchy energy E_(1/log T)=O(T log²T) and joint shallow/deep budget [L]. Finite off-line support iff uniformly bounded nonreal heat counts [S].
- **Open:** Actual cap/collision mass zero, or all-height finite-head sign at arbitrarily small heat. Scaled shifted energy hE_h=O(N) is not extinction; horizon exp(c/t) gives no uniform heat count or finite off-line support.
- **Sources:** R:XiWardGlobalCapAndFiniteHeadArithmetic; ALDG:HermiteHeatRootBarrier; R:DeBruijnNonrealCountRightLimit; [shallow energy](#shallow-cauchy).

<a id="li"></a>
### LI — Paired Li and prime–Gamma balances

- **Path:** Literal prime−Gamma lower floor → Li positivity → RH; equivalently actual Cayley–Li ladder nonpositive on coefficient-sum-zero vectors.
- **Done:** Exact histories and clock-rate receivers [L]. Actual Cayley–Li ladder primitive nonpositivity iff RH; actual couplings do not decay [S].
- **Open:** Arithmetic proof of primitive ladder sign or subexponential history floor, retaining first-crossing/outside correlations.
- **Sources:** R:LiEvenCrossActualClockGrowthLaw; ALG:RHIsReflectionPositivityOfTheCayleyLadder.

<a id="sz"></a>
### SZ — Suzuki screw and shifted-kernel limits

- **Path:** Complete signed boundary pairing → screw nonnegativity or shifted-Ξ confinement → RH.
- **Done:** Complete compact-L² first variation and RW transfer [L]. Full first-variation sign on factorial/grid tent families iff RH [S].
- **Open:** Sign on these complete families, especially low/mixed modes. Restricted high-scale positivity does not exhaust the receiver.
- **Sources:** R:Suzuki/SuzukiCriticalL2FirstVariation; R:Suzuki/SuzukiCriticalRHCompleteFamilyTransfer.

<a id="pm"></a>
### PM — Physical-model Haar approximation (FZZ-P)

- **Path:** Global dyadic Haar approximation or cofinal signed-damping admission at ε↓0 → RH; alternatively positive gauge mass for every actual subcritical cofactor limit. [PW-B](#pw-b) remains a candidate sub-branch.
- **Done:** Complete-energy/gauge-mass receivers; half-damping admission, escape alternative and compact effective-pole-order laws.
- **Open:** Cofinal complete-energy bound as ε↓0 or positive gauge mass for every actual subcritical limit. Exterior tightness and exclusion of infinite-height escape remain open.
- **Sources:** CP:TheEscapeCompletenessCriterion; ACG:RHIsTheVisibilityOfEveryEscapeState; [ADR](#adr).

<a id="jas"></a>
### JAS — Joint ancestry

- **Path:** Level-one prime-product Weil positivity or finite-power square-shell subpower Riesz bound → RH.
- **Done:** Exact receivers; Γ–theta admission at every finite support/phase/grade; positivity at growing logarithmic prime budget.
- **Open:** Reach square-root power budget, all-amplitude shell positivity, or every-exponent subpower square-shell bounds. Admission does not supply budget growth.
- **Sources:** R:JointAncestryLevelOneCapstones; R:JointAncestrySquareShellFinitePowerCriterion.

<a id="ctf"></a>
### CTF — Chronological tail / Báez–Duarte approximation

- **Path:** Bounded chronological Bose/Möbius rows or finite Báez–Duarte dilates → L² error→0 → RH.
- **Done:** Approximation/dual-sampling receivers; residual=(1−Λ-readout)²+centered pronic energy. Literal −μ aligns the readout.
- **Open:** Complete error→0 under moving cutoffs/small damping, or arithmetic dual-sampling bound. Readout alignment does not control centered energy.
- **Sources:** R:ChronologicalRiemannEquivalence; V:VonMangoldtReadoutFormOfTheBaezDuarteCriterion.

<a id="hcf"></a>
### HCF — Gaussian heat trace / critical feature variance

- **Path:** Exact arch−prime heat trace → one-sided vertical growth or all-degree positivity on both prime-log grids → RH.
- **Done:** Exact heat explicit formula; fixed-rank signs/inertia; positivity on both log2/log3 grids with polar cancellation iff RH. Arbitrary-zero detector [L]; alternative centered-heat derivation [P].
- **Open:** Both actual grid signs at every degree/height, or one-sided vertical/prime-chirp bound. One grid aliases.
- **Sources:** R:XiGaussianHeatTwoPrimeSourceSampling; R:HeatGridAliasingBoundary.

<a id="xn"></a>
### XN — Xi Newton invariant discs

- **Path:** Xi first jets → line-centered Newton self-map discs covering every zero → RH.
- **Done:** Coverage/self-map criterion and exact nonnegative Laplacian of interior margin.
- **Open:** Cover every zero by line-centered discs with nonnegative interior margin. Boundary sign does not pay curvature; scalar damping gives only trivial repair.
- **Sources:** R:XiNewtonSchwarzPickCriticalLine; R:XiNewtonDiscCurvature.

<a id="bag"></a>
### BAG — Deterministic zeta self-return

- **Path:** Fixed-base ζ recurrence throughout the right strip, or cutoff-uniform positive Haar mass of target-ζ twists → RH.
- **Done:** Strong/local recurrence and positive-Haar-mass receivers; weak ladders collapse to RH. Finite-head approximation retains target-zero exceptions.
- **Open:** Actual returns near every right-strip point at every tolerance, including possible zeros. Zero-free-target universality is insufficient.
- **Sources:** R:ZetaStrongRecurrenceReceiver; R:ZetaWeakRecurrenceLadderCollapse.

<a id="ewu"></a>
### EWU — Even pole-weight uniqueness

- **Path:** Actual even blind minimum≥0 at every aperture → even positivity → λ=Λ → RH.
- **Done:** Even-weight rigidity; attained aperture-antitone blind minima; restricted high-window signs and local floors.
- **Open:** Nonnegative actual minimum at every aperture, including low/mixed modes. Arbitrary tent approximation and polar-nonclosed limits do not transport restricted positivity.
- **Sources:** R:EvenSectorPoleWeightUniqueness; R:EvenSectorBlindVariationalAttainment.

<a id="gta"></a>
### GTA — Transverse Schur charge

- **Path:** Actual theta-stage positive quartic Schur charge → rank-uniform transverse decay → RH.
- **Done:** Exact transverse-charge decay criterion; positive charge and strong finite-prefix convergence.
- **Open:** Rank-uniform arithmetic transverse-energy decay independent of zero data. Finite-prefix convergence alone is insufficient.
- **Sources:** R:Hedenmalm/HedenmalmThetaSchurQuarticSpectralDecayEquivalence; R:PaperThetaSchurModeCharge.

<a id="owu"></a>
### OWU — Odd Weil-weight uniqueness

- **Path:** Actual-Λ odd positivity, or odd-positive weight plus all-scale dilation-ray sign → RH.
- **Done:** Odd/polar RH criteria, local floors, and smooth odd witnesses separating Λ positively from Liouville/prime-flip twins at radii 181/500 and 23/40.
- **Open:** All-test/all-aperture odd sign with reflected-prime/polar payment. Companion-forcing certificate and conductor horizon are incompatible; need stronger signed estimates or a different detector.
- **Sources:** R:WeilMarkovOddPositivity; SP:TwoPrimeCatalanSeparationAndContinuumTowerObstruction; CDG:TheConductorForcingGap.

<a id="pbm"></a>
### PBM — Regularized prime/log-ζ abscissa

- **Path:** Fixed pole-regularized coefficients → Dirichlet convergence at every real σ>1/2 → RH.
- **Done:** Convergence of either pole-regularized prime/log-ζ Dirichlet series at every σ>1/2 is equivalent to RH.
- **Open:** Actual coefficient cancellation to critical abscissa. Regularization alone supplies none.
- **Sources:** R:RegularizedLogZetaAbscissa; R:PaperPrimeRegularizedIdeal.

<a id="rb"></a>
### RB — Robin/Nicolas divisor-sum criterion

- **Path:** Extremal divisor sums/primorial Mertens product → eventual Robin/Nicolas inequality → RH.
- **Done:** Robin/Nicolas eventual criteria; colossally abundant reduction; fixed exponent-defect margins. Large counterexamples require growing prime cores.
- **Open:** Square-root-scale remainder inequality on growing prime-saturated extremizers/primorials. Necessary divisibility conditions are not exclusion.
- **Sources:** R:RobinColossallyAbundantReduction; B:RobinMovingValuationDefect.

<a id="srt"></a>
### SRT — Prime-side one-parameter lag localization

- **Path:** Actual prime−archimedean late-lag lower bound, or full atomic-family sign → RH.
- **Done:** Every-width lag receiver and arbitrary-zero detector; full atomic RH receivers at widths (log log N)^α/N for every α>1 [L]; work/index criterion [S].
- **Open:** Actual signed late-lag/full-family estimate or subquantum work bound. Neither synthesis nor multiplicative submaximal prime gap supplies full positivity; α=1 and bounded overlap remain uncovered.
- **Sources:** S:EveryWidthDecidesTheCriticalLine; SSHA:TheDenjoyCarlemanProfiles; [atomic synthesis](#levy-approximation); [gap obstruction](#counting-positivity).

<a id="act"></a>
### ACT — Arithmetic criticality / single-shift variation

- **Path:** One fixed theta shift a>0 → D_a(u)≤2S_a(u)+V_a(u) for every even compact C² profile → odd Weil positivity → RH.
- **Done:** Exact single-shift ground-state variation receiver; light-cone signs; fixed-support reflected-prime collar paid at sufficiently large shift.
- **Open:** One fixed shift paying every profile/support, including exterior primes and signed/polar remainder. Support-dependent absorption is insufficient.
- **Sources:** D:ShortProfilePoleFreeVariationInequality; D:RestrictedWeilGroundEnergyCriticalAtInfinity.

<a id="aip"></a>
### AIP — Arithmetic incidence positivity

- **Path:** Actual prime incidence + plateau gauge → all-aperture GlobalIncidenceAllocation → odd positivity ↔ RH.
- **Done:** Allocation/odd-sign receiver; local floors, complete-cell/atomic transfer, separated-atom error control and restricted even-power + odd-mixed finite index [L]. Pole-complement/affine reduction [S].
- **Open:** Full overlapping-form sign: pay remaining prime blocks, touching-level work, coarse error and true poles with one reserve; establish both primitive sign and affine floor.
- **Sources:** I:GlobalIncidenceAllocationCondition; I:GlobalSharedSurplusAllocation; [shared signed frontier](#signed-hodge).

<a id="acs"></a>
### ACS — Arithmetic Castelnuovo–Severi effectivity

- **Path:** Full-source effectivity / bounded-error Rosati heights / all-ordinate chirality → Hodge → RH; complete-cell index payment is a source target.
- **Done:** Source RR/effectivity/height/chirality receivers; complete-cell transfer, separated-atom error control and restricted even-power + odd-mixed finite index [L].
- **Open:** Full-source quadratic RI plus degree-zero subquadratic growth, Rosati-height lower bound, or complete-cell index zero. Abstract effectivity existence is an RH-equivalent input, not its construction.
- **Sources:** G:ExactArithmeticSourceEffectivity; AE:TheEffectivityCalculus; [shared signed frontier](#signed-hodge).

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

Tools feeding live routes; none is an additional route/candidate. Details live in Lean, not this ledger.

| Framework | Feeds | Established | Missing / scope | Entry points |
|---|---|---|---|---|
| <a id="high-cell-remainder"></a>**Complete-cell transfer** | HF, ACS, AIP, SRT | Full W and every finite mixed Gram recovered by fixed-support smooth cell refinement; both pole moments preserved [L]. | Prove complete-cell sign/index bound; fixed-support convergence gives no growing-aperture estimate. | G:CompleteWeilSourceTransfer; G:PolePreservingSmoothing |
| <a id="section-descent"></a>**Closed-section projection** | HF, ACS, AIP, SRT, CHMD | Bounded Weil projection and exact signed residual retain every negative square [L]; finite completed index attained by actual smooth Grams [S]. | Residual nonnegativity or index ceiling; projection existence/convergence is closed. | AID:TheClosedSectionHasABoundedWeilProjection; AID:TheCompleteCellsCaptureEveryFiniteIndex [S] |
| <a id="signed-hodge"></a><a id="balanced-haar"></a>**Haar / remaining signed prime blocks** | HF, ACS, AIP, CHMD | Coarse Γ+logarithmic detail reserve paid with one coarse-mass error. Root plus generators a<A at every level approximate physical cell sources with squared L² error≤32Γ/(1+log A) [L]. Entire even-power source S₂ retains δΓ+(γ_E/2)mass after half-mean-square correction; adding both odd k≥3 mixed correlations gives index(Γ−S₂−M_odd)≤A+1 uniformly [L]. | Pay k=1, odd-power diagonal blocks, finite heads, coarse error and actual polar/archimedean mass. Restricted form is not W. Low-generator translation orbits remain infinite/noncompact; L² approximation is not signed-form control. | SAHT:FiniteGeneratorOrbitsApproximateThePhysicalCellSource; SAHT:CompactDetailsDoNotMakeTranslationOrbitsCompact [L]; AID:SquaresAndOddHigherMixedPowersHaveUniformFiniteIndex [L] |
| <a id="touching-mixed"></a>**Touching levels / Gamma reserve** | RW, HF, ACS, AIP, CHMD | Ordered W splits into centered Chebyshev work and exact Gamma square reserve. Boundary norm π/2 is sharp, unattained; no uniform positive relative reserve [S]. Touching interaction bounded [L]. | Signed Chebyshev payment and touching cost below available margin, jointly across apertures. | AID:TheOrderedWeilSourceIsACenteredChebyshevDefect [L]; AID:TheOrderedWeilSourceRetainsItsGammaSquareReserve [S] |
| <a id="renormalized-potential"></a><a id="tower-finite-part"></a><a id="ramanujan-quasimodes"></a>**RAPT — prime gap and spectrum** | HF, ACS, AIP | Sharp pole-complement prime gap 2log2; Liouville gap 0; bounded-energy finite Ramanujan approximation [L]. Actual bounded-window counts/eigenlines converge to adjunction E_m=γ+log m+tameDifferent(m); fixed-sieve operator has compact inverse [S]. | Full Gamma/pole and growing-conductor mixed-family control. Bounded-energy vectors escape every fixed integer window [L]; prime spectrum is not ξ spectrum. | RAPT:TheSpectralGapOfThePrimeFormIsTwoLogTwo [L]; RAPT:TheBoundedPrimeSpectrumIsTheAdjunctionSpectrum [S]; SAHT:BoundedPrimeEnergyEscapesEveryFixedIntegerWindow [L] |
| **Separated-atom / trial-energy control** | HF, ACS, AIP | At width c/N, 0<c<1: horizon-uniform cross→center quadratic error and bounded pole residual; collar paid by top-atom potential +3 masses; simple/proper trial energies. Periodic mean-zero signed inverse-distance rows are uniformly bounded [L]. | Bounded error is not vanishing error or sign. Need growing-conductor mixed estimates, complete overlap and full-operator spectral identification. | RAPT:TheAtomCrossReplacementHasUniformErrors; RAPT:TheCenterCollarIsPaidByTheTopAtoms; RAPT:TheCompleteWeilTrialEnergiesAreSimpleAndProper; H:FiniteShiftedHarmonicAbelBounds [L] |
| <a id="counting-positivity"></a>**ACP — arithmetic counting / gap selection** | HF, ACS, AIP, SRT | Gap≥2log2·c_N²; prime flips have c_N→(p−1)/(p+1). Every submaximal gap permits multiplicative, polar-matched flips with negative full Weil tests. Fixed-conductor harmonic Ramanujan coordinates are Möbius transforms; conductors m>1 coprime to flipped p have limit zero [L]. | Exact maximal gap for p≥11 flips claimed [P], not Lean-closed. Actual eigenline bridge and full source sign remain open. | ACP:PrimeParityPairing; ACP:PrimeParityRamanujanCoordinates; ACP:NearMaximalGapsDoNotForceWeilPositivity [L]; [maximal-gap claim](../drafts/pipeline/2-fully-proven/arithmetic-counting-maximal-gap-rigidity.md) [P] |
| <a id="smap"></a><a id="nonratio-lags"></a>**SMAP — full source selection** | AIP, HF, ACS, SRT | Under abs(λ)≤Λ, full overlapping-atom positivity iff RH and λ=Λ. Finite sign-gauge flips can preserve maximal prime gap; non-ratio overlaps retained [L]. Dyadic lag-rigidity/perturbation exclusion source [S]. | Actual signed cross-level/polar control. Interval bound requires 1≤a≤b; Liouville-twin capstone absent. Perturbations need not preserve abs(λ)≤Λ. | SMAP:PositivityAtEveryRootSelectsTheVonMangoldtWeight; SSHA:TheGaugeEntersThroughNonRatioLags [L]; SMAP:TheDyadicSignIsRigid [S] |
| <a id="atomic-stability"></a><a id="levy-approximation"></a><a id="atomic-dirichlet"></a>**SSHA — atomic synthesis** | SRT, AIP, HF, ACS | Full W continuity; every fixed-width spline family is RH-complete. Shrinking widths (log log N)^α/N, every α>1, also give full receivers. Exact reflected Dirichlet-polynomial factorization [L]. | Arithmetic sign on overlapping families; α=1/bounded-overlap exhaustion remains open. Factorization is not a bandlimit or sign theorem. | SSHA:UnboundedOverlapIsTheRiemannHypothesis; SSHA:TheDenjoyCarlemanProfiles; SSHA:TheAtomicFamilyIsADirichletPolynomial |
| <a id="spacing-scale"></a><a id="interaction-stability"></a><a id="arithmetic-sections"></a>**Positive narrow sections** | HF, ACS, AIP | Universal Markov stability at a small fraction of spacing; full positive independent-profile sections [L/S]. Markov stability fails for e/(2π)<width/spacing<1 [L]. | Narrow positive sections are gapped, not source-complete. Negative Markov directions do not refute full pole-paid positivity. | SSHA:TheSpacingScaleLawIsUniversal; G:ArithmeticSectionsPayThePole; SSHA:TheMarkovFormFailsInsideTheSeparatedRegime |
| <a id="lorentzian"></a><a id="polar-gluing"></a><a id="frobenius-repair"></a>**ALG — form reductions / repairs** | HF, ACS, AIP, LI | Metzler below spacing and subspacing Hodge [L]; no nonnegative unitary gauge above overlap ratio 1 [S]. At every width, full W≥0 iff primitive Markov sign plus pole-corrected affine floor [S]. Polar/Frobenius repairs classified [S]. | Prove both inequalities on complete families; identify/pay any correction in original W. A corrected positive form is not the original. | ALG:TheHodgeIndexIsAGapOnThePoleComplementAndOneScalar; ALG:TheHalfDefectIsTheOptimalHodgeRepair [S] |
| <a id="turan-layer"></a><a id="local-factors"></a><a id="aldg"></a>**Polynomial / local-divisor tools** | LA, WD; HF, ACS | Ordinary ξ coefficients Turán; sharp Hermite barriers/attained extremizers [L]. Lorentzian closure and half-line Laguerre inequality [S]. ξ=P·g near 2+iT: degree P=O(log T), g zero-free on radius 8, g′/g=O(log T) on radius 7 [S]. | Actual finite-head signs/Jensen real-rootedness. Factoring zeros does not locate them. Positive local Ramanujan+Lorentzian factors force Weil-bound equality, incompatible with prime integrality [S]. | R:XiTaylorCoefficientsLogConcave; ALDG:HermiteHeatRootBarrier [L]; R:XiZeroFreeCofactorNearAnOrdinate; ALG:RamanujanAndLorentzianMeetOnlyAtTheWeilBound [S] |
| <a id="outward-field"></a><a id="index-descent"></a>**AES / AID — energy and index** | HF, ACS, SRT | RH iff transverse ℰ<1; ℰ finite iff finite off-line support [L]. For damped source work W(R), F(R)=R²(W(2R)−W(R))↑E₂; E₂ finite iff finite support; RH iff E₂≤q*=3·431349/2000 [S]. | Arithmetic upper bound at sufficient threshold. Neither finiteness nor RH follows from energy/index classification. | AES:TheTransverseEnergyOfTheZeroDivisor [L]; AID:TheCriticalSourceRateHasACanonicalEnergy [S] |
| <a id="hecke-krein"></a>**HKT — group-kernel index** | HF, ACS | Positive-definite kernel + κ hyperbolic pairs has index≤κ; equality for nonzero weights and one element separating all 2κ nodes off the unit circle. One nonunitary pair has index exactly 1 regardless of positive part; unitary pair with Re(weight)≥0 has index 0 [S]. | General finite-index decomposition and actual arithmetic kernel/positive remainder not supplied. No arithmetic index ceiling. | HKT:KernelsOnGroupsAndTheirNegativeIndex; HKT:HyperbolicPairsAndTheIndexFormula [S] |
| <a id="arithmetic-polarization"></a><a id="conjugate-diagonal"></a>**Polarization / theta detectors** | HF, ACS, OWU, SRT, RW | Collided form computed from log abs(ξ) and theta prefixes; its translation invariance iff RH. Fixed-aperture log-Sobolev comparison, signed Gårding and finite index. Quantitative theta/divisor detectors [L]. | Actual Hecke-defect upper bound or full sign; collided positivity and detector accuracy do not give either. | PL:HeckeInvarianceOfTheCollidedPolarizationIsRH; PL:WeilsFormHasFinitelyManyNegativeDirectionsAtEveryAperture; CDG:PolynomialThetaLocalSelection |
| <a id="bvi"></a>**BVI — cancellation / rate dictionaries** | MC, CTF, PM, HF | Exact escaped-μ, receiver, Hecke-defect, zero-strip and integer-theta rate dictionaries; uniform VK decay. Fixed-modulus/below-diagonal savings [L]. | RH-strength subpower readings/half-power cancellation; no fixed Vaughan power saving supplied. | V:UnconditionalEscapedMoebiusDecayAndCrossRouteBridge; V:SingleScaleThetaPrefixTransferAndVKCeiling |
| <a id="adr"></a><a id="acp"></a>**Escape / ArithmeticCorrespondencePositivity** | PM, MC, WL, HF, ACS | Residual kernels, compact pole-order/Gram laws and escape classification. Prime-error energy iff RH; genus slope iff RH+simple zeros [L]. | Exterior tightness, positive gauge mass, inverse coercivity or actual energy estimate; compact laws do not exclude infinite-height escape. | CP:CompactReceiverWindowsSelectTheMaximalVisibleOrder; CP:TheAbelSlopeOfThePrimeErrorIsTheArchimedeanGenus; [ADR corpus](../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/) |
| <a id="arithmetic-correlation"></a><a id="ssa"></a>**Gauge averages / successor arithmetic** | MC, PM, HF, ACS, AIP | A.e. square-root cancellation, exact shift floors, escape measures and quantitative charged-cell growth [L/S]. | Select actual μ; obtain matching-profile signed estimates. Typical gauges, relative/twin cancellation and growing cell counts supply no all-test sign. | ACG:AlmostEveryGaugePointCancelsToTheSquareRoot; SSA:TheShiftFloorsAreExact; ACG:SubProgressionStabilizerInversionAndCellHolonomyGrowth |
| <a id="aog"></a><a id="biarithmetic"></a><a id="biarithmetic-gauge"></a><a id="arithmetic-effectivity"></a>**Arithmetic geometry / effectivity** | HF, ACS, WL, MC, AIP | Source/index/rate and degree–torsion dictionaries; RR/effectivity/height/chirality receivers; torsion=ψ, first Fourier=M; finite-curve calibrations, Burgess and least-nonresidue bounds [L/S]. | Actual source positivity/Rosati heights; character estimates do not supply μ cancellation. | J:TheIndexExit; AE:TheEffectivityCalculus; BGG:TheCriticalConservationLaw; BG:ArithmeticEulerCharacteristic |
| <a id="apd"></a><a id="mpg"></a><a id="sbwf"></a>**Positive duality / multiplicative geometry** | HF, ACS | Positive-measure theta/FE rigidity; affine/GNS realization; boundary-capacity and finite-frequency laws [L/S]. Simple-pole completed class identifies ζ [L]. | Source-compatible mixed positivity/interior sign. Rigidity needs its full analytic/moment inputs; source identification is not Weil positivity. | APD:PositiveMeasureHamburgerRigidity; MPG:GrowthToForcing; SB:TheSimplePoleClassIsZeta |
| <a id="renormalized-biarithmetic"></a><a id="arithmetic-intersection"></a><a id="horizon-renormalization"></a>**Renormalization / intersection** | HF, ACS, AIP, MC, OWU | Exact periodic/Ramanujan survival, prime-tower and counterterm laws; collided moment reconstruction [L]. Residue/character finite parts and fixed-field gauge means [S]. | Signed mass-relative/growing-sieve control with full Gamma/poles; local tower bounds cannot be summed as a global ℓ² ceiling. | RBG:TheRenormalizationSurvivalLaw; AIT:TheLocalFormsDoNotSum [L]; RAPT:TheFinitePartOnResidueClasses [S] |
| <a id="artin-mertens"></a>**Artin–Mertens / Hecke foundations** | RAPT; number-field support | Fixed-field ideal count and Frobenius Mertens law. For fixed field/modulus, ray-class counts κ_m x+O(x^(1−1/n)) uniformly across classes; nontrivial ray-class character coefficient sums O(x^(1−1/n)) [S]. | Hecke continuation/FE and strip control; arbitrary Frobenius conjugacy classes, convergent finite parts and field/modulus-uniform estimates. | AM:TheFrobeniusDensityTheoremWithBoundedError; HLF:ConePointsOfARayClassAreLatticeCosets; HLF:IdealsAreEquidistributedInRayClasses [S] |
| <a id="arithmetic-kunneth"></a>**Counts / local payment tools** | HF, ACS, AIP, MC, PM | Künneth positive-count hierarchy; packed-path frustration payment; compensated dispersion and finite-window incidence [L]. Golden impure data pass positive counts. | Signed trace/RR mechanism and cofinal full-source estimate; no reuse of shared reserves. | AK:KunnethPositivityIsPointCountPositivity; SAEI:FrustrationIsPaidAlongCanonicalPaths; M:MultiModulusKloostermanDispersionAndPrimeRowTransfer |
| <a id="pair-schur-slack"></a>**Critical-line census / IGP** | HF, ACS | Imported Zeta23 plus local disjoint-pair slack gives simple-critical proportion≥0.67250071−ε [L]. Trans-threshold certificate yields (29/36−ε)N−S; proper powers=o(N). | Need S≤(1/18+o(1))N on the same profiles. No unconditional 75% on-line theorem; ≥3/4 within 4/log T is near-line, not on-line. | IGP:CriticalLineZeroProportion; P:SmoothWeightedCertificateAtFourThirds; R:Zeta23SimpleOffLineNearLine |
| <a id="analytic-large-values"></a>**Large values / density / value moments** | HF, WL, ACS, SRT, OWU | Zero-ordinate second moments and power-saving prime-detector counts [L]. Reflected-pair model gives corrected abs(S₁)²≤(C+2P)(Re S₂+D). Generic CGG on the codimension-≤2p off-line annihilator and rank–trace bound after removing a block [L]. | Displacement-sensitive arithmetic input and individual-zero exclusion; density/average bounds leave exceptions. Model configurations are not ζ counterexamples. | AES:HigherMomentsAtZeroOrdinates; R:ValueMomentsCannotSeparateReflectedPairs; R:OffLineAnnihilatingWeightsCountCriticalZeros; R:RankTraceBoundAfterRemovingABlock |
| <a id="shallow-cauchy"></a>**Shallow Cauchy / Poisson energy** | WD; zero census; HF, ACS | Eventually in T, strict-right zeros in [T,2T] at depth≤h have shifted energy hE_h≤C max(κ,2h log T)T log T, 0<h≤1/64. At h=1/log T: E_h=O(T log²T), squared-multiplicity and K/log T close-pair bounds. For every ε>0, some α gives deep count≤εN(T,2T) and combined shallow/deep budget O_ε(N) [L]. | No subcritical/vanishing collision budget, unshifted-energy bound, finite off-line support or improved on-line proportion. Shift and exact multiplicities cannot be dropped. | SCP:MultiscaleLorentzL2; SCP:ShallowCauchyEnergyBound; SCP:ShallowCauchyImplications [L] |
| <a id="closed-cycle-tools"></a>**Reconstruction / auxiliary transport** | EWU, HF, FU, CHMD, PM, TG | Controlled cycle recovery, clock/phase calibration, Nyquist limits, spectral constraints and Gaussian covariance [L]. Reflection/S₂ and reverse-twisted pole transfers are support only. | Signed source selection; reconstruction and restricted covariance do not give positivity. | B:FiniteNetDerivativeRecovery; B:ProducerCompletionAndPrimeClockKernelSynthesis; A:SpectralRealisationAndOperatorConstraints |

<a id="external-literature"></a>
## Dependency / external-claim scope

| Input | Local status / limit |
|---|---|
| Zeta23 (Alpöge–Furman), pinned imported Lean dependency | Critical-line census relies on it; local IGP extension is [L]. Published-literature standing is separate. |
| [Quasi-RH manuscript](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf) | Claims Dirichlet zero-freeness Re s>7/8 [E], not RH. R:ChenGuptaLi* contains detector/density components, no zero-free capstone; continuation/contour step open. Local horizontal-collision no-go blocks an RH endpoint, not the 7/8 claim. |
| [Ordinary two-point correlation manuscript](https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf) | Fixed-form Liouville logarithmic saving claimed [E]; not power saving or growing-shift/modulus uniformity. Distinct from [logarithmic two-point theorem](https://arxiv.org/abs/1509.05422) and from local formalization. |

## Dead mechanisms / scope boundaries

[44 named failed mechanisms and 19 retired labels](rh-killed-routes.md). Scoped no-gos do not retire the live routes above. Key boundaries: fixed-aperture/fixed-rank tests are incomplete; finite index need not vanish; uniform positive aperture gaps fail; multiplicativity + polar matching + any fixed gap below 2log2 does not select ζ.

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
| SP | SelectivePositivityAndThresholdLaws | AES | ArithmeticElectrostatics |
| RBG | RenormalizedBiarithmeticGeometry | AIT | ArithmeticIntersectionTheory |
| RAPT | RenormalizedArithmeticPotentialTheory | ALG | ArithmeticLorentzianGeometry |
| SSHA | SpacingScaleHarmonicAnalysis | IGP | IncommensurableGaborPinching |
| AID | ArithmeticIndexDescent | SAHT | SignedArithmeticHodgeTheory |
| SMAP | SelectiveMultiscaleArithmeticPositivity | AM | ArtinMertens |
| HLF | HeckeLFunctions | ACP | ArithmeticCountingPositivity |
| HKT | HeckeKreinToeplitz | SCP | ShallowCauchyPrimeEnergy |

## Alias lookup

BVI→[support](#bvi); C1→RW; CCM-FU→FU; CLG/TTF,K-RVM,S6F,TCD,UEB→TH; CSB,STC,U,MPLF,RHist,BPC,TQFQ,WS2,SQB→RN; D2,Q,RG,RG-ETA,TK→PA; E,EDQ,L,HDL,PSRC→MC; FZZ-P→PM; PW-B→[candidate](#pw-b); G,HC→WD; O→WL/RW (genus mechanism dead); P,SP-E→RP; SV2,RG-HF→SZ; T1,T2,Route T→TT; Route T successor/ULF sub-unit anchor→TG; Deninger→HF. [Retired labels](rh-killed-routes.md#retired-labels).
