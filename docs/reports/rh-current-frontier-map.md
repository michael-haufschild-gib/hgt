# RH proof-route frontier

**RH open. 31 live routes; 17 standalone candidates; PW-B candidate sub-branch.**

**Corpus checkpoint:** `26f9564ae52220c2bbe6c76ec17e1c9a14a6cd60`.

**Evidence:** [L] integrated Lean source inspected, not a fresh kernel audit; [S] working/unintegrated/unfinished source, not certified closure; [K] individual Lean check and transitive-axiom audit with only standard axioms; [P] paper only; [E] external claim, not locally validated.
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
| Finite off-line support ⇒ zeros approach the line ⇔ Lindelöf hypothesis + finitely many nonreal zeros of every cos(hD)Ξ, h>0 ⇒ fixed zero-free half-plane [L]. Finite off-line support ⇔ finite Weil-kernel index (on ℚ_{>0}^× or any two-prime lattice) ⇔ uniformly bounded heat counts N(t) ⇔ all zeros above some height critical [S]. | Every finite-support receiver (finite ℰ/E₂, bounded complete-cell or tower index, subtracted lag, uniform heat count) is at least LH-strength; none is supplied. |

Sources: SP:LiouvilleOddWindowRefutationAndSelectiveFullPositivity; O:TheWidthDictionary; G:AllParityCriticalDeficitAndEndpointSobolevLaws; C:UnconditionalBirmanSchwingerRateReadsTheZeroWidth; R:LindelofCosineFiniteDefectDepth; HKT:TheFiniteIndexStratumOfZetaIsLindelofDeep [S].

## Live routes

Done = [L] unless marked otherwise. All routes remain open.

<a id="wl"></a>
### WL — Weil lag function

- **Path:** Actual prime lag/deficit → one-sided bound or subexponential critical energy → RH.
- **Done:** Critical energy/cross-work and linear prime-error energy criteria; bounded high-zero tail. Genus Abel slope characterizes RH plus simple zeros. Upper and lower one-sided √x log²x Chebyshev bounds each characterize RH [S].
- **Open:** Prove actual signed-correlation or linear prime-error energy bound. Genus saturation is stronger than RH.
- **Sources:** B:WeilLagCriticalDeficitEndpointAndLimitLaw; CP:TheAbelSlopeOfThePrimeErrorIsTheArchimedeanGenus; [count precision](#count-precision).

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
- **Done:** Exact history-floor criterion: RH iff the normalized history is eventually ≥−B(K+2). Unconditionally it drops below −δ(K+2) cofinally for some δ>0, so no sublinear floor exists. Hyperbola/centroid/square-debt identities; low-LCM payment; native first-clock-jet admission.
- **Open:** Pay high-LCM pairs, moving core and singular-domain transport in one complete-history floor at linear scale.
- **Sources:** R:SPEQuantileRieszRoutePLinearFloorCriterion; R:SPEQuantileRieszRoutePLinearHistoryEscape; R:RoutePLcmPairPayment.

<a id="pa"></a>
### PA — Prime–archimedean source passivity

- **Path:** Exact prime−archimedean trace → current sign, subexponential Bernstein mismatch or positive signed compact moments → RH.
- **Done:** Exact source/trace receivers. Each fixed Hausdorff order is positive at sufficiently large shifts.
- **Open:** All-order/all-shift positivity, high-frequency current sign, or every-positive-rate mismatch bound; order-dependent thresholds leave a signed complement.
- **Sources:** R:PrimeArchEndpointFrequencyAccretivity; R:PrimeArchHausdorffFixedOrderLargeShiftPositivity.

<a id="mc"></a>
### MC — Möbius cancellation at half power

- **Path:** Actual μ/Liouville cancellation, square-sampled Chebyshev bound or harmonic–exponential odd-parity upper count → RH; alternatively exclude every oscillating smooth-power probe below half damping.
- **Done:** Half-power/rate/strip dictionaries; fixed-modulus/below-diagonal savings; escaped-μ VK decay in endpoint M=(N−b)/a [L]. Chebyshev precision exponent=sup Reρ; both unweighted Liouville parity upper counts ⇔ RH; one harmonic–exponential odd-class upper count alone ⇔ RH ⇔ ζ-kernel index zero [S].
- **Open:** Produce actual moving-scale half-power cancellation, cofinal subpower energy or the odd-class upper bound. VK/PNT/short-interval laws alone supply no square-root precision; general-weight countermodels preserve them [S]. M=o(√x) is false.
- **Sources:** R:MobiusHilbertFormEquivalence; V:UnconditionalEscapedMoebiusDecayAndCrossRouteBridge; AKLT:TheParityFormOfTheGlobalLaw [S]; [count precision](#count-precision).

<a id="tt"></a>
### TT — Theta-tail and heat–Cassini currents

- **Path:** Theta source → directed covariance/Wold decay or odd Weil sign → RH.
- **Done:** Theta seam/tail and Wold receivers; sharp t<1/2 boundedness threshold; Φ-Doob identities retaining reflected primes; restricted current/light-cone signs.
- **Open:** All-test directed covariance or complete odd/primitive positivity, including signed reflected-prime interaction.
- **Sources:** R:PaperWoldDirectedCovarianceRH; R:WeilMarkovOddPositivity; [ACT](#act).

<a id="la"></a>
### LA — Line anchor

- **Path:** Theta source → all-height Laguerre/Jensen or heated coefficient sign → real-rooted Ξ → RH.
- **Done:** Exact coefficient receivers; finite-head/tail transfer; uniform high-order heated positivity. Ordinary ξ coefficients are Turán [L], Lorentzian [S]. Local ξ/heat factorization; uniform shrinking-depth transfer at t log X≤c d²; for 0<t≤1/8, heated zeros real and simple beyond 2π exp((2/3+ε)/t) [L].
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
- **Done:** Source/divisor, Hecke-defect and complete-cell receivers; Haar pole payment, Gamma cross-error O(mass), W(R)=O(R log²R), separated matrix positivity and logarithmic Gram floor [L]. All-prime cubes-and-higher approximation [K]. Haar occupation with nonnegative completion cost; full even-power source/head error; touching archimedean entries and width-uniform o(1) nonratio-prime error; actual ζ index/decomposition [S].
- **Open:** Full signed-form sign or RH-threshold work ceiling. Pay valuation-completion and Gamma boundary costs jointly, control Gamma of projected head/tail, then first-prime/coarse mixing and polar moments. Touching errors are bounded, not a positive floor; overlap/exhaustion remains open. O(R log²R) is not bounded work.
- **Sources:** J:TheIndexExit; PL:HeckeInvarianceOfTheCollidedPolarizationIsRH; [signed frontier](#signed-hodge); [prime spectrum / complete matrix](#renormalized-potential).

<a id="chmd"></a>
### CHMD — Causal Hyperbolic–Modular Duality

- **Path:** Complete causal prime/Möbius wave bound or odd theta-Doob half-threshold bound → RH.
- **Done:** Wave/Doob/nodal receivers; core, radical, Schur transport, physical Haar approximation and Gamma cross-error O(mass) [L]. All-level finite-prime and all-prime exponent≥3 approximation [K]. Actual heads preserve mean; tails mean-zero and L²-orthogonal. Full even-prime-power source-minus-head error≤ε(Γ(head)+Γ(tail))+C_εΓ(f)/(1+log A) [S].
- **Open:** Full wave or odd/nodal sign. Bound Γ(head)+Γ(tail) by original energy to close even-power head approximation; first-prime payment, coarse/polar moments and infinite retained-orbit sign remain. Divergent absolute prime/square coefficient masses forbid that absolute-payment shortcut, not signed compensation.
- **Sources:** R:CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion; R:CHMDOddSectorCriterion; [Haar](#balanced-haar); [actual generator heads](#generator-heads).

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
- **Done:** Ward/collision receivers; extremizer attainment/Hermite asymptotics; shifted budgets. Zero displacement≤d and deep dyadic copies≤C log X·N(t) for t log X≤c d², uniformly in 0<d≤1/2. Reality horizon 2π exp((2/3+ε)/t), 0<t≤1/8; local forces, forward simplicity and collision-continuous energy [L]. Compact-region forward simplicity even after a multiple collision; small-time collision mass counts index plus multiplicity excess; uniformly bounded N(t) iff finite off-line support [S].
- **Open:** Arithmetic cap/collision extinction or all-height finite-head sign. No polynomial N(t) bound; local force/continuity tools do not yet give a localized energy evolution bound. Finite N(t) at each t>0 does not give uniform count or RH.
- **Sources:** R:XiWardGlobalCapAndFiniteHeadArithmetic; ALDG:HermiteHeatRootBarrier; R:Heat/HeatUniformDepthZeroDensity; R:KiKimLeeTwoThirdsHorizon; HKT:HeatCollisionsCountTheIndex [S]; [local heat tools](#local-factors).

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
- **Done:** Even-weight rigidity; attained aperture-antitone blind minima; restricted high-window signs and local floors. RH iff at every aperture some real weights (any sign/growth) make ζ's full Weil functional nonnegative up to that aperture; the obstruction dual is a blind test.
- **Open:** Nonnegative actual minimum at every aperture, including low/mixed modes. Arbitrary tent approximation and polar-nonclosed limits do not transport restricted positivity.
- **Sources:** R:EvenSectorPoleWeightUniqueness; R:EvenSectorBlindVariationalAttainment; R:WeilPositivityFiniteLevelExistenceDecidesRH.

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

- **Path:** Actual signed late-lag bound, complete atomic-family sign or all-generator one-prime tower sign → RH.
- **Done:** Every-width atomic receivers at (log log N)^α/N, α>1; every arbitrarily small pole-free C² generator's towers on any prime are positive iff RH [L]. Fixed-width integer windows and some shrinking-width schedule capture full index; all-generator tower index zero selects RH and λ=Λ without weight-domination assumptions [S].
- **Open:** Actual signed late-lag/full-family or all-generator tower bound. Generator support does not bound tower aperture. Explicit shrinking schedules' full-index capture and α=1/bounded-overlap sign exhaustion remain open; Gevrey≤1 obstruction kills only that profile construction.
- **Sources:** S:EveryWidthDecidesTheCriticalLine; SMAP:TheDyadicSignOfAPoleFreeGeneratorIsRH [L]; HKT:ShrinkingAtomsCarryTheWholeIndex; HKT:IndexZeroSelectsTheVonMangoldtWeight; HKT:TheReceiversEndAtTheQuasiAnalyticBoundary [S]; [prime-pattern selection](#counting-positivity).

<a id="act"></a>
### ACT — Arithmetic criticality / single-shift variation

- **Path:** One fixed theta shift a>0 → D_a(u)≤2S_a(u)+V_a(u) for every even compact C² profile → odd Weil positivity → RH.
- **Done:** Exact single-shift ground-state variation receiver; light-cone signs; fixed-support reflected-prime collar paid at sufficiently large shift.
- **Open:** One fixed shift paying every profile/support, including exterior primes and signed/polar remainder. Support-dependent absorption is insufficient.
- **Sources:** D:ShortProfilePoleFreeVariationInequality; D:RestrictedWeilGroundEnergyCriticalAtInfinity.

<a id="aip"></a>
### AIP — Arithmetic incidence positivity

- **Path:** Actual prime incidence + plateau gauge → all-aperture GlobalIncidenceAllocation → odd positivity ↔ RH.
- **Done:** Allocation/odd-sign and complete-cell receivers; Haar pole payment, Gamma cross-error O(mass), complete subcritical occupation identity with nonnegative boundary cost; eventual complete-matrix positivity at each fixed 0<c<1 and logarithmic Gram floor [L]. All-prime exponent≥3 approximation [K]. Exact complete-matrix entries through c=1 and actual nonratio-matrix/source identity; nonratio-prime error o(1) uniformly for 0<c≤1; charge-defect reserve [S].
- **Open:** Full overlapping-form sign with one reserve. Pay valuation/Gamma boundary costs, first-prime/coarse mixing and head/moment terms. Charge reserve has a possibly negative mass floor; bounded touching errors do not prove endpoint positivity, c↑1-uniform horizon or RH-complete exhaustion.
- **Sources:** I:GlobalIncidenceAllocationCondition; I:GlobalSharedSurplusAllocation; [signed frontier](#signed-hodge); [prime spectrum / complete matrix](#renormalized-potential).

<a id="acs"></a>
### ACS — Arithmetic Castelnuovo–Severi effectivity

- **Path:** Full-source effectivity / bounded-error Rosati heights / all-ordinate chirality → Hodge → RH; complete-cell index payment is a source target.
- **Done:** Effectivity/height/chirality and complete-cell receivers; Haar pole payment, Gamma cross-error O(mass), complete Haar occupation identity with nonnegative completion cost, W(R)=O(R log²R), separated positivity/logarithmic Gram floor [L]. Higher-prime-power approximation; actual elliptic-zeta continuation/poles and both simple affine coefficient poles [K]. Full even-power head-error bound and width-uniform touching corrections [S]. Sharp 16/21 matrix certificate; actual ζ moments only below threshold [L].
- **Open:** Full-source quadratic RI with degree-zero subquadratic growth, Rosati-height bound or actual index zero. Pay boundary/coarse/mixed costs; prove touching/overlap sign and RH-strength work control. Census needs wider-frequency signed ζ moments/column normalization. Finite-field coefficient poles still need actual Eisenstein unfolding and noncancellation under summation; no characteristic-zero bridge.
- **Sources:** G:ExactArithmeticSourceEffectivity; AE:TheEffectivityCalculus; [signed frontier](#signed-hodge); [prime–polar cancellation](#prime-polar-cancellation); [complete matrix](#renormalized-potential); [kernel index](#hecke-krein); [census](#pair-schur-slack).

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
| <a id="sc"></a>**SC — Stokes/Witt−Krein:** cross-fibre indefinite invariant → orientation. | Rigged fibres, Fourier reconstruction and Witt/Selberg coordinates [L]; actual orbit-kernel converse, finite-pair tower detection, off-discriminant index continuity and minimal exceptional-wave count [S]. | Source-fixed cross-fibre sign/index selecting the wall. Finite-pair membership, separating tower and actual bound remain inputs; classification supplies none. | R:PaperKreinWallFourierCompletion; V:WittSelbergReceiverCoordinates; [kernel index](#hecke-krein); [index scope](#aklt) |
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
| <a id="signed-hodge"></a><a id="balanced-haar"></a>**Haar / signed source payment** | HF, ACS, AIP, CHMD | Individual Haar W≥mass/10; divisor-square defect D_H≥log(2)·mass/12; original poles give D_H+P≥D_H/8 and ≥mass/144 [L]. For every signed Haar vector, abs(Γ(h)−Σd_a²Γ(h_a))≤exact boundary cost≤e^(1/2)Σwidth_a d_a²≤16e^(1/2)mass(h), with no removed head [L]. Joint full-detail/nonfirst-mixed/entire-even payment retains restricted index≤A+2 [S]. | Pay the exact Gamma boundary cost and D_H’s logarithmic/outgoing potential together, plus first-prime/coarse mixing and head/sinh/mean terms. The O(mass) error bound is not small enough by itself to spend the positive mass reserve; full Haar-span sign remains open. | G:TheHaarArithmeticReservePaysBothPoles; G:TheHaarGammaCrossTermsCostOnlyMass [L]; AID:TheFullNonfirstSourceRetainsAlmostAllGamma; AID:TheEntireSquareSourceSharesTheFullDetailReserve [S] |
| <a id="haar-occupation"></a>**Subcritical Haar occupation** | HF, ACS, AIP | x_a=d_a/√(2a+1), cell weight≥1/2; cross-kernel Λ(n/m)/(n/m). For every finite signed Haar source, D_H+B=½Σ_e occupation_e+R, R≥0. B=½Σ_a(EulerOffset−outgoing_a)x_a²≥0; each outgoing row is a subseries of the complete source-prime ladders, EulerOffset=Σ_p log p/(p²−1). Complete basis, original-domain membership and full summability proved [L]. | Pay B jointly with original Gamma/polar costs; B≥0 does not permit dropping it from an upper bound. Zero original root coordinate is not transformed-ground orthogonality; occupation positivity is not full-Weil positivity. | G:TheHaarDivisorFormHasSubcriticalPrimeWeights; G:TheHaarDivisorReserveControlsValuationOccupation; RAPT:TheInversePrimeNumberOperatorHasOccupationEnergy [L] |
| <a id="generator-heads"></a>**Actual generator heads / even-power error** | CHMD, HF, ACS, AIP | Finite logarithmic-cell cutoffs are stopping-cell weighted averages; head preserves mean, tail mean-zero, head⊥tail in L²; tail mass≤32Γ(f)/(1+log A). Both mixed error and full even-power source-minus-head error≤ε(Γ(head)+Γ(tail))+C_εΓ(f)/(1+log A), uniformly in finite source size. Centered even-power diagonal costs arbitrarily little Gamma plus a constant times square mass on compact BV sources [K]. | Control projected Gamma by original Γ(f); pay first-prime/coarse/polar terms and retained-orbit sign. Mean preservation/L² orthogonality alone do not supply Gamma stability or preserve the two exponential Weil moments; the even-power source includes every even exponent. | SAHT:EveryGeneratorCutoffStopsAtAnActualDyadicCell; SAHT:GeneratorCutoffsAreLogarithmicBlockAverages; SAHT:ActualGeneratorHeadsPreserveTheSourceMean; SAHT:TheSquareSourceHeadErrorHasOnlyAGammaStabilityCost [K] |
| **All-level Euler approximation** | HF, ACS, AIP, CHMD | Every lag has head error≤96Γ/(1+log A); finite prime sets have the corresponding coefficient-mass bound. For all primes and k≥3, H=Σ2log(p)/p^(k/2)<∞ and sum of absolute errors≤96HΓ/(1+log A), uniformly in source horizon, levels and every finite selection [K]. | Prime/square coefficient masses diverge; signed compensation remains possible. Need projected-Gamma/pole control and retained-orbit sign; general BV sources retain noncell components. | SAHT:FiniteEulerFactorsHaveAllLevelGeneratorApproximation; SAHT:AllHigherPrimePowersHaveAllLevelGeneratorApproximation; SAHT:CriticalEulerCoefficientMassStartsAtCubes [K] |
| <a id="touching-mixed"></a>**Mixed Gamma / reserve** | RW, HF, ACS, AIP, CHMD | Mixed Γ coupling²≤128e^(1/2)Γ(g)·mass(h); exact interval and balanced-Haar energies. Finite disjoint mean-zero interval families, including touching endpoints, have absolute Gamma off-diagonal error paid once by boundary remainders; Haar specialization costs O(mass) [L]. Ordered square reserve and sharp unattained norm π/2 [S]. | Joint signed arithmetic payment using actual boundary reserve; O(mass) does not establish a positive remaining floor. No uniform positive relative reserve. | G:GammaCouplingUsesOnlyDetailMass; G:GammaFiniteMeanZeroOffDiagonal; G:TheHaarGammaCrossTermsCostOnlyMass [L]; AID:TheOrderedWeilSourceRetainsItsGammaSquareReserve [S] |
| <a id="prime-polar-cancellation"></a>**Full prime–polar cancellation** | RW, HF, ACS, AIP, CHMD | For every ε>0, eventually R, every real compact BV f supported in [−R,R]: abs(primeSum(f)−P(f))≤ε exp(R)(Γ(f)+mass(f)). All prime powers and both poles retained; no derivative norm [S]. Smooth-cutoff frequency bounds [L]; square boundary ζ′/ζ(1+it)=o(log abs(t)) [L]. | exp(R) loss prevents aperture-uniform relative smallness, index ceiling or sign. | M:ThePrimePolarCutoffHasUniformFrequencyBounds; R:Sieve/ZetaLogDerivIsSublogarithmic [L]; AID:TheFullPrimePolarSourceCancelsInGammaNorm [S] |
| <a id="renormalized-potential"></a><a id="tower-finite-part"></a><a id="ramanujan-quasimodes"></a>**RAPT — prime / complete-Weil spectra** | HF, ACS, AIP | Prime gap 2log2; bounded prime spectrum/simple eigenlines→E_m=γ_E+log m+tameDifferent(m) [L]. For fixed C² profile φ on [0,1], ∫φ²>0, width c/N, 0<c<1: complete-W bounded counts/eigenlines converge to arithmetic spectrum. Every fixed finite Ramanujan packet has identity Gram and diagonal complete energy F_φ(c)+E_m−γ_E+α·1_(m=1), α=c(∫φ)²/∫φ². Both poles select conductor one; Markov has −α instead of +α [S]. | Overlapping/RH-complete families, growing conductor/energy and full sign. Fixed separated packet limits are not operator-norm convergence or ξ spectrum; coercivity degenerates as c↑1. | RAPT:TheBoundedPrimeSpectrumIsTheAdjunctionSpectrum [L]; RAPT:TheBoundedCompleteWeilSpectrumIsTheAdjunctionSpectrum; RAPT:TheCompleteWeilFormIsDiagonalOnFiniteRamanujanPackets; RAPT:TheMarkovAndWeilPacketFormsHaveOppositePoleShifts [S] |
| **Touching errors / charge reserve** | HF, ACS, AIP | C² profile on [0,1], mass>0: cross error≤4C_φc²‖x‖²; exact complete-matrix entries retain literal primes and both poles for 0<c≤1. At every width, normalized nonratio prime matrix equals actual nonratio source form. Nonratio prime correction O_φ(log N/N) uniformly in c, hence one smallness horizon for all 0<c≤1; at c=1 only n=N, km=N+1 survives. With q=(∫φ)²/∫φ²<1, energy≥a‖x‖²+(1−q)·primeDefect/4 eventually at each 0<c<1, same a∈ℝ [S]. | a may be negative; positive-floor horizon still depends on c; reserve→0 as q→1. Uniformly vanishing nonratio term and bounded cross error do not prove complete touching/overlap sign. | CACT:TheActualArchimedeanMatrixReachesTouching; CACT:TheNonRatioMatrixIsTheActualPrimeCorrection; CACT:TheBoundaryPrimeStarVanishesAfterNormalization; CACT:TheChargeDeficitKeepsAUniformPrimeReserve [S] |
| **Growing Ramanujan frames** | HF, ACS, AIP | For Q≥2 and all real conductor coefficients: actual pole-profile Gram≥(H_N−H_{Q(Q−1)})Σd_m²≥log((N+1)/(Q(Q−1)+1))Σd_m²≥(log(N+1)−2log Q)Σd_m². Window square-mass discrepancy≤Q(Q−1)Σd_m² [L]. | Complete-Weil signed energy and complement control at growing Q; positive Gram floor for N+1>Q² is not sign or full-index exhaustion. | CACT:GrowingRamanujanFamiliesHaveASquareRootHorizon [L] |
| <a id="counting-positivity"></a>**ACP — finite prime gap selection** | HF, ACS, AIP, SRT | All finite flip sets: exact conductor weights, full resolvent limit and greatest gap from secular signs. Single-prime gap=min(r_p,2log2), below ceiling iff p<11. Interior gaps strictly decrease under proper inclusion. Maximal base gap plus exact untwisted dyadic-probe lower bound selects the empty flip set [L]. | Finite sign-flip class only; no full Weil sign or arbitrary-weight selector. Every fixed probe tolerance admits remote nontrivial flips. | ACP:TheFinitePrimeSecularSignsDetermineTheGap; ACP:TheParitySecularRootDeterminesTheGap; ACP:OneDyadicProbeSelectsTheFinitePrimeSource; ACP:ConductorMassBoundsGapLossAndProbePrecision [L] |
| **ACP — infinite patterns / exhaustion** | HF, ACS, AIP, SRT | Every pattern has Euler density c_P and actual conductor coordinates. Bounded-energy mass converges to counted mass; c_P=0 iff mass escapes every bounded window. Full actual resolvent converges for every 0<s<2log2, to zero when c_P=0 [L]. Every pattern has an attained greatest gap; for c_P>0 secular signs classify it exactly, and finite-prime cutoff gaps decrease to it [S]. Sparse infinite flips retain prescribed submaximal gaps; cofinite flips have gap zero [L]. | Zero-density greatest-gap classification; infinite-pattern maximal-gap/source selection; full signed Gamma/pole payment. A zero limiting resolvent alone gives no eventual sign. | ACP:EveryPrimePatternHasActualConductorCoordinates; ACP:PrimeCountsDetermineEveryBoundedSpectralMass; ACP:EveryPrimePatternHasItsFullArithmeticResolvent; ACP:CofinitePrimeFlipsHaveZeroGap [L]; ACP:PositiveDensityTransfersTheExactCutoffGap [S] |
| <a id="smap"></a><a id="nonratio-lags"></a>**SMAP — full source selection** | AIP, HF, ACS, SRT | Full overlapping-atom positivity selects RH and λ=Λ under abs(λ)≤Λ [L]. All C² compact generators on any one prime's towers select RH and λ=Λ without domination [S]. Λ and Liouville twin cannot both be tower-positive along a nonnegative nonzero generator at any spacing [L]. | Prove actual Λ sign for every generator/window. Pair exclusion does not identify the positive weight; one preselected generator is insufficient. | SMAP:PositivityAtEveryRootSelectsTheVonMangoldtWeight; SMAP:TheDyadicSignIsRigid [L]; HKT:IndexZeroSelectsTheVonMangoldtWeight [S] |
| <a id="atomic-stability"></a><a id="levy-approximation"></a><a id="atomic-dirichlet"></a>**SSHA — atomic synthesis** | SRT, AIP, HF, ACS | Full W continuity; every fixed-width spline family and widths (log log N)^α/N, α>1, are RH-complete [L]. Integer windows at every fixed width capture full index; some shrinking schedule does too [S]. | Actual overlapping-family sign; explicit shrinking full-index schedule and α=1/bounded-overlap exhaustion. Nonzero compact Gevrey profiles exist iff order>1 [S]; this alone does not refute endpoint atomic completeness. | SSHA:UnboundedOverlapIsTheRiemannHypothesis; SSHA:TheDenjoyCarlemanProfiles [L]; HKT:ShrinkingAtomsCarryTheWholeIndex; HKT:TheReceiversEndAtTheQuasiAnalyticBoundary [S] |
| <a id="spacing-scale"></a><a id="interaction-stability"></a><a id="arithmetic-sections"></a>**Positive separated sections** | HF, ACS, AIP, SRT | Markov fails for e/(2π)<width/spacing<1 [L]. Smooth plateau Robin integral, mass and charge→1; completed shape→2. For every b<2−log(2π), ε>0, one profile of mass>1−ε gives every complete-Weil eigenvalue≥b eventually at each fixed 0<c<1; hence full quadratic-form floor b‖x‖² [L]. | Horizon may depend on c; no c↑1 uniformity, touching/overlap sign or RH-complete exhaustion. | SSHA:TheMarkovFormFailsInsideTheSeparatedRegime [L]; CACT:ThePlateauShapeAndChargeHaveTheirIndicatorLimits; CACT:SmoothPlateausMakeTheSeparatedCompleteWeilMatrixPositive [L] |
| <a id="lorentzian"></a><a id="polar-gluing"></a><a id="frobenius-repair"></a>**ALG — form reductions / repairs** | HF, ACS, AIP, LI | Metzler below spacing and subspacing Hodge [L]; no nonnegative unitary gauge above overlap ratio 1 [S]. At every width, full W≥0 iff primitive Markov sign plus pole-corrected affine floor [S]. Polar/Frobenius repairs classified [S]. | Prove both inequalities on complete families; identify/pay any correction in original W. A corrected positive form is not the original. | ALG:TheHodgeIndexIsAGapOnThePoleComplementAndOneScalar; ALG:TheHalfDefectIsTheOptimalHodgeRepair [S] |
| <a id="turan-layer"></a><a id="local-factors"></a><a id="aldg"></a>**Polynomial / local heat tools** | LA, WD; HF, ACS | Ordinary ξ coefficients Turán; Hermite barriers/attainment. Uniform shrinking-depth transfer; local cofactors, exterior forces O(log X), forward simplicity, collision-continuous energy and gap-independent pair flux [L]. Simple-zero velocity/local branch and compact-region forward simplicity after arbitrary positive-time collisions [S]. | Localized energy evolution and small-time N(t) bound; all-height finite-head signs. Ordinary-coefficient Lorentzianity is not Jensen real-rootedness; positive Ramanujan+Lorentzian Euler factors force impossible prime equality [S]. | R:Heat/HeatUniformDepthZeroDensity; R:Heat/HeatExteriorForce; R:Heat/HeatZeroSumContinuity; R:Heat/LocalizedHeatPairForce [L]; R:Heat/HeatLocalizedEnergyEvolution; ALG:RamanujanAndLorentzianMeetOnlyAtTheWeilBound [S] |
| **ζ growth / heat horizon** | LA, WD | μ(11/18)≤1/9 via A·B·A²B and interpolated profiles. Heated zeros real/simple beyond R=max(X₀,2π exp((2/3+ε)/t)); nonreal count and collision mass≤C(R+1)log(2+3(R+1)) [L]. | Still exponential in 1/t; no polynomial upper count, uniform total count or extinction. | R:ZetaElevenEighteenthsLineBound; R:ZetaElevenEighteenthsProfiles; R:KiKimLeeTwoThirdsHorizon [L] |
| <a id="outward-field"></a><a id="index-descent"></a>**AES / AID / CACT — source work and index** | HF, ACS, SRT | RH iff ℰ<1; ℰ finite iff finite off-line support. Actual completed W(R)≤64R L_R(L_R+1), abs(W_N(R))≤128R L_R(L_R+1), L_R=C+log(R+4), R≥4, uniformly in taper N [L]. R²(W(2R)−W(R))↑E₂; E₂ finite iff finite support; RH iff E₂≤3·431349/2000. Annular increment≤39/50 eventually iff finite support; at every R≥4 iff RH [S]. | Bounded work, subquantum annular increment or critical-energy ceiling. O(R log²R) retains all exterior interactions but proves none of these targets. | AES:TheTransverseEnergyOfTheZeroDivisor; CACT:TheCompletedSourceWorkHasALogarithmicCeiling [L]; AID:TheCriticalSourceRateHasACanonicalEnergy; AID:EveryOffLineQuartetCostsAStrictScaleQuantum [S] |
| <a id="hecke-krein"></a>**HKT — actual kernel index** | HF, ACS, SRT, WD; SC | Actual ζ spline-kernel κ=#distinct right zeros, even; RH iff κ≤1; finite κ iff finite off-line support iff orbit Krein–Langer decomposition. Integer/two-prime/all-width families carry κ; prime tower counts distinct p^(ρ−1/2), with exact Nyquist alias bound; at most κ(κ−1)/2 blind primes, and positivity on infinitely many towers forces κ=0 for positive-plus-finitely-many-pairs kernels. Global law: κ=0 iff eventually ψ(x)−x≤C√x log²x; for curve data over 𝔽_q, κ=0 iff the one-sided square-root point count. κ tied exactly to critical energy and small-time collision mass [S]. | Independent arithmetic index/energy/growth ceiling or a producer of the one-sided count. Classification supplies no finiteness; explicit shrinking-width full-index schedule remains open. | HKT:TheConverseKreinLangerTheoremForOrbitKernels; HKT:EveryReceiverAtEveryWidthIsBoundedByTheIndex; HKT:TheNyquistLawOfAPrimeTower; HKT:AllButFinitelyManyPrimesSeeTheWholeIndex; HKT:TheGlobalLawIsTheOneSidedSquareRootCount; HKT:IndexIsEnergy; HKT:HeatCollisionsCountTheIndex [S] |
| **HKT — decomposition / atomic margin** | HF, ACS, AIP, SRT; SC | Arbitrary Hermitian kernel κ≤m iff PSD after adding m squares; finite-index witness attained. Exact finite-exponential/Bohr index laws. Atomic Dδ₁−P has window index 0/1/≥2 across log N−γ and log N−γ−2log2; sign gauges preserve index, not pole carrier. Every fixed D gives infinite whole-lattice index [S]. | General covariant character decomposition remains distinct from positive-minus-finite-rank decomposition. Growing-counterterm finite-window margin is not an actual ζ index ceiling; Stepanov annihilation is a receiver, not an arithmetic compressor. | HKT:FiniteIndexIsPositiveMinusFiniteRank; HKT:TheIndexOfAFiniteExponentialSum; HKT:TheIndexOfABohrSeries; HKT:TheMarginIsTheWidthOfTheIndexOneWindow; HKT:StepanovCompressionsAndTheAnnihilationLaw [S] |
| <a id="aklt"></a>**AKLT — cyclic/tower detection** | HF, ACS, SRT; SC | PSD+finitely many distinct nonunitary pairs: all cyclic restrictions PSD ⇒ index zero. If nonunitarity and node separation fail on only finitely many towers, almost every tower carries full index; infinitely many PSD towers force zero. Logarithmic spectra satisfy this on prime towers [S]. | Actual arithmetic restriction signs and finite-pair membership. Coordinate axes can miss index 2; outside this class every cyclic restriction can be PSD while the full kernel is not [S]. | AKLT:CyclicSubgroupsDecideTheKreinLangerClass; AKLT:TowerFaithfulSpectraAreDecidedByAlmostEveryTower [S] |
| **AKLT — index stability / exceptional waves** | HF, ACS, SRT; SC | Finite Hermitian limit index is an eventual lower bound under pointwise convergence. For PSD+κ pairs with nonzero limiting weights and nodes separated/nonunitary at one element, index eventually equals κ. On a separating tower, least number of exponential waves whose subtraction leaves a bounded count is exactly κ; outer nodes attain it [S]. | Actual finite-pair representation and arithmetic count bound remain unproved inputs. Index can drop under vanishing weights, collisions or unit-circle contact; generic wave theorem is not an unconditional ζ finite-support bound. | AKLT:TheIndexIsContinuousOffTheDiscriminant; AKLT:TheIndexIsTheNumberOfExceptionalWaves [S] |
| **AKLT — local index / twist completion** | HF, ACS, SRT; SC | On ℤ^S, finite card(S)≥2, axis-supported kernels have index 0 or ∞; positive-weight axis sums of δ₀−r^abs(n), r>0, have index∞. Euler Poisson kernels/twists are PSD. For finite curve data, quadratic twist preserves index; one uniform square-root upper count across twists of every 2^j base change ⇔ unitary spectrum [S]. | Finite nonzero index requires off-axis interaction. One twist alone fails for an abstract four-eigenvalue datum, not an actual curve. Need actual complete-source/count producer; Gamma is not axis-supported. | AKLT:LocalConstituentsMeetOnlyAtTheIdentity; AKLT:TheTwistTowerCompletesTheUpperCount [S] |
| <a id="count-precision"></a>**Square-root count / parity** | WL, MC, HF, ACS, SRT | Count_Λ: ψ−x=O(√x log²x) ⇔ RH; either one-sided bound separately ⇔ RH; precision exponent=sup Reρ. Count is invariant under finite changes and finite prime-tower rescaling. Λ+εn^(−η), ε≠0, η≥0, satisfies Count iff RH and η≥1/2; nontrivial scaling/Liouville mixtures and eventual λΛ tails fail Count. With H(t)=Σe^(−nt)/n, O(t)=Σ_{λ(n)=−1}e^(−nt)/n: RH iff for every 0<ε<1/2, O(t)≤(H(t)+C_εt^(1/2−ε))/2 near 0 [S]. | Produce actual Count_Λ or odd-class bound. PNT and all short-interval laws at 17/30<α<1 survive 0<η<1/2 perturbations that fail Count; these general-weight countermodels need not preserve prime support. No new route or source uniqueness. | ASRP:TheCountIsTheRiemannHypothesis; ASRP:TheBatteryOfTheCount; ASRP:TheDecidingInputTheorem; AKLT:TheParityFormOfTheGlobalLaw [S] |
| <a id="arithmetic-polarization"></a><a id="conjugate-diagonal"></a>**Polarization / theta detectors** | HF, ACS, OWU, SRT, RW | Collided form computed from log abs(ξ) and theta prefixes; its translation invariance iff RH. Fixed-aperture log-Sobolev comparison, signed Gårding and finite index. Quantitative theta/divisor detectors [L]. | Actual Hecke-defect upper bound or full sign; collided positivity and detector accuracy do not give either. | PL:HeckeInvarianceOfTheCollidedPolarizationIsRH; PL:WeilsFormHasFinitelyManyNegativeDirectionsAtEveryAperture; CDG:PolynomialThetaLocalSelection |
| <a id="bvi"></a>**BVI — cancellation / rate dictionaries** | MC, CTF, PM, HF | Exact escaped-μ, receiver, Hecke-defect, zero-strip and integer-theta rate dictionaries; uniform VK decay. Fixed-modulus/below-diagonal savings [L]. | RH-strength subpower readings/half-power cancellation; no fixed Vaughan power saving supplied. Balanced-regime short-window Möbius/prime power saving ⇔ quasi-RH; strip [1/4,3/4] ⇔ Chebyshev Cesàro mean-square energy ≪N^{3/2+ε} [L]: further dictionaries, no producer. | V:UnconditionalEscapedMoebiusDecayAndCrossRouteBridge; V:SingleScaleThetaPrefixTransferAndVKCeiling; RDP:ShortWindowDispersionAtSeventeenThirtieths; R:QuasiRHNormalizedChebyshevCesaroAndMertensActionAbscissaLaw |
| <a id="adr"></a><a id="acp"></a>**Escape / ArithmeticCorrespondencePositivity** | PM, MC, WL, HF, ACS | Residual kernels, compact pole-order/Gram laws and escape classification. Prime-error energy iff RH; genus slope iff RH+simple zeros [L]. | Exterior tightness, positive gauge mass, inverse coercivity or actual energy estimate; compact laws do not exclude infinite-height escape. | CP:CompactReceiverWindowsSelectTheMaximalVisibleOrder; CP:TheAbelSlopeOfThePrimeErrorIsTheArchimedeanGenus; [ADR corpus](../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/) |
| <a id="arithmetic-correlation"></a><a id="ssa"></a>**Gauge averages / successor arithmetic** | MC, PM, HF, ACS, AIP | A.e. square-root cancellation, exact shift floors, escape measures and quantitative charged-cell growth [L/S]. | Select actual μ; obtain matching-profile signed estimates. Typical gauges, relative/twin cancellation and growing cell counts supply no all-test sign. | ACG:AlmostEveryGaugePointCancelsToTheSquareRoot; SSA:TheShiftFloorsAreExact; ACG:SubProgressionStabilizerInversionAndCellHolonomyGrowth |
| <a id="aog"></a><a id="biarithmetic"></a><a id="biarithmetic-gauge"></a><a id="arithmetic-effectivity"></a>**Arithmetic geometry / effectivity** | HF, ACS, WL, MC, AIP | Source/index/rate and degree–torsion dictionaries; RR/effectivity/height/chirality receivers; torsion=ψ, first Fourier=M; finite-curve calibrations, Burgess and least-nonresidue bounds [L/S]. | Actual source positivity/Rosati heights; character estimates do not supply μ cancellation. | J:TheIndexExit; AE:TheEffectivityCalculus; BGG:TheCriticalConservationLaw; BG:ArithmeticEulerCharacteristic |
| <a id="apd"></a><a id="mpg"></a><a id="sbwf"></a>**Positive duality / multiplicative geometry** | HF, ACS | Positive-measure theta/FE rigidity; affine/GNS realization; boundary-capacity and finite-frequency laws [L/S]. Simple-pole completed class identifies ζ [L]. | Source-compatible mixed positivity/interior sign. Rigidity needs its full analytic/moment inputs; source identification is not Weil positivity. | APD:PositiveMeasureHamburgerRigidity; MPG:GrowthToForcing; SB:TheSimplePoleClassIsZeta |
| <a id="renormalized-biarithmetic"></a><a id="arithmetic-intersection"></a><a id="horizon-renormalization"></a>**Renormalization / intersection** | HF, ACS, AIP, MC, OWU | Exact periodic/Ramanujan survival, prime-tower and counterterm laws; collided moment reconstruction [L]. Residue/character finite parts and fixed-field gauge means [S]. | Signed mass-relative/growing-sieve control with full Gamma/poles; local tower bounds cannot be summed as a global ℓ² ceiling. | RBG:TheRenormalizationSurvivalLaw; AIT:TheLocalFormsDoNotSum [L]; RAPT:TheFinitePartOnResidueClasses [S] |
| <a id="artin-mertens"></a>**Artin–Mertens / Hecke foundations** | RAPT; number-field support | Global continuation; Re s≥1 nonvanishing away from trivial pole; fixed-field/modulus Mertens bounds. Unique finite primitive conductor. At primitive modulus, actual theta Fourier coefficient is nonzero iff its integral dual-frequency ideal is coprime to modulus; norm²=N(modulus) there, otherwise 0. Nonzero supported frequencies exist, including unit modulus; nonunit conductor kills zero mode. Exact inverse ray-residue covariance and unit-base transfer [L]. | Full unit/class reindexing, global dual character/epsilon factor and completed L-functional equation assembly; field/modulus-uniform bounds and interior zero exclusion. Arithmetic Fourier support and covariance alone do not assemble the global equation. | HLF:HeckeLFunctionsHaveGlobalContinuation; HLF:HeckeLFunctionsDoNotVanishOnTheLineReOne; HLF:HeckeCharactersSatisfyMertensBounds; HLF:HeckeFiniteCharactersHavePrimitiveConductors; HLF:HeckeFourierSupportIsIdealCoprimality; HLF:HeckeFourierCoefficientsScaleByRayResidues [L] |
| **Lattice Poisson / theta foundations** | Theta families; BAG; Hecke support | Affine Schwartz/parity Gaussian Poisson on intrinsic lattices. Actual ideal trace dual, covolume=N(I)√abs(discriminant), reciprocal place scaling, theta inversion and uniform exponential tails [L]. | Normalization tools, not RH-selective sign or identification with the Hecke L-functional equation. | H:IntrinsicParityPoisson; H:NumberFieldIdealTraceDuality; H:NumberFieldIdealCovolume; H:NumberFieldScaledIdealTheta [L] |
| **Elliptic base fields / pole transfer** | Geometry / effectivity calibration | Square complex torus has transcendence degree/genus one [L]. Actual y²=x³−x over 𝔽₃: differential dimension one, zeta numerator degree 2g=2 and roots of modulus 1/√3. Point-count series continues to Z(T); shifted quotient cancels T=1, has poles T=1/3 and scaled numerator roots with exact multiplicity. Arithmetic poles have Re s=−1/2; both simple affine coefficient products inherit genuine poles [K]. | Arithmetic Eisenstein coset sum/unfolding and noncancellation after summation; characteristic-zero source/RR bridge. Coefficient poles do not prove poles of a full Eisenstein series or Riemann ζ positivity. | H:PositiveGenusBaseField [L]; AE:FiniteFieldPositiveGenusBase; AE:FiniteFieldEllipticZetaPoles; AE:FiniteFieldEllipticZetaContinuation; H:LoopEisenstein/AffineA1FiniteFieldCoefficients [K] |
| **Affine Weyl / loop-group foundations** | Automorphic foundations | Affine A₁ completed-ζ coefficients and convergent rotated Weyl sum [L]. Tame central extension/root lifts; h₀(a)=z(a)h₁(a⁻¹), injective Cartan; degree rotation, exact SL₂(F[[X]]) splitting and faithful rational→real loop map [K]. Positive Iwahori Gauss coordinates; unique central/finite-torus/completed-unipotent coordinates on positive Borel; unipotent tame cocycle trivial [S]. | Actual arithmetic quotient/coset sum, measures, Iwasawa decomposition, convergence and constant-term identification; RH arithmetic bridge. Algebraic Borel coordinates are not full-group Iwasawa decomposition or source sign. | H:LoopEisenstein/AffineA1WeylSum [L]; H:LoopEisenstein/AffineA1Coroots; H:LoopEisenstein/RealDegreeRotation; H:LoopEisenstein/PositiveLoopSplitting; H:LoopEisenstein/LoopSL2FieldMap [K]; H:LoopEisenstein/PositiveBorelCoordinates [S] |
| <a id="arithmetic-kunneth"></a>**Counts / local payment tools** | HF, ACS, AIP, MC, PM | Künneth positive-count hierarchy; packed-path frustration payment; compensated dispersion and finite-window incidence [L]. Golden impure data pass positive counts. | Signed trace/RR mechanism and cofinal full-source estimate; no reuse of shared reserves. | AK:KunnethPositivityIsPointCountPositivity; SAEI:FrustrationIsPaidAlongCanonicalPaths; M:MultiModulusKloostermanDispersionAndPrimeRowTransfer |
| <a id="pair-schur-slack"></a>**Critical-line census / IGP** | HF, ACS | Imported Zeta23 + local slack: simple-critical≥0.67250071−ε; simple-or-critical≥0.8876. Trans-threshold (29/36−ε)N−S certificate; E(1/9)≤4 would give 70%. In the c=2 rank–trace capacity 2−κ, 3/4 iff κ≤5/4; at bandwidth 4/3 the diagonal+archimedean+pole constant 43/36 is unconditional and a prime surplus ≤N/18 gives 75% simple critical zeros. Zero-side spectral slack: (H(λ)−ε)N+slack≤N₀* for λ<1; slack≤(λ−H(λ)+ε)N refutes the 3/4 slack hypothesis for every λ<3/4; displaced pairs reach slack N/12 iff η≥1/6. Sine-kernel Gram moments (1,4/3,2,13/4) and sharp quartic model 16/21; cubic blind spot 2/3 [L]. | Actual normalized signed Gram moments and column bound near bandwidth 1, or S≤(1/18+o(1))N / E(1/9)≤4, or a displacement-sensitive zero-side slack bound near λ=1. Neither sine integrals nor below-threshold Lorentzian moments prove unconditional 3/4 or 16/21 ζ proportion. | IGP:CriticalLineZeroProportion; P:SmoothWeightedCertificateAtFourThirds; P:NarrowStripClosePairEnergyAndExchangeRate; G:HigherInertiaCertifiesSixteenTwentyFirsts; G:TheSineKernelFourthMomentIsThirteenQuarters; G:BreakingTheCoalescenceBlindSpotAndThreeQuarters; G:SpectralSlackConservationAndTheHyperbolicDisplacementThreshold [L] |
| **Actual ζ higher form factors** | Census; HF, ACS | For all-zero Lorentzian S: triple integral=o(T log T) for α,β>0, α+β<1; mixed fourth∼αβT log²T/16 for 0<α<β, α+β<1; diagonal fourth∼α²T log²T/8 for 0<α<1/2 [L]. | Wider-frequency signed Gram cycles/column normalization; these actual ζ moments do not establish the census moments at bandwidth near 1. | R:MontgomeryTripleFormFactorVanishes; R:MontgomeryFourLevelFormFactorFactorizes [L] |
| <a id="analytic-large-values"></a>**Large values / density / value moments** | HF, WL, ACS, SRT, OWU | Zero-ordinate second moments and power-saving prime-detector counts [L]. Reflected-pair model gives corrected abs(S₁)²≤(C+2P)(Re S₂+D). Generic CGG on the codimension-≤2p off-line annihilator and rank–trace bound after removing a block [L]. Guth–Maynard Theorem 1.1 proved unconditionally: N(σ,T)≪T^{(30/13)(1−σ)+ε} for σ∈[1/2,5/6], primes in (x,x+x^{17/30+ε}] with the asymptotic, almost all intervals of length x^θ, θ>2/15 [L]; the density hypothesis on σ≥5/6 [L]; Vinogradov–Korobov zero-free region [L]. Density envelopes never drop below 1 [L]. | Displacement-sensitive arithmetic input and individual-zero exclusion; density/average bounds leave exceptions and cannot force a zero-free strip; short-interval asymptotics have relative error o(1), not a power saving. Model configurations are not ζ counterexamples. | AES:HigherMomentsAtZeroOrdinates; R:ValueMomentsCannotSeparateReflectedPairs; R:OffLineAnnihilatingWeightsCountCriticalZeros; R:RankTraceBoundAfterRemovingABlock; R:Sieve/GuthMaynardTheoremOneOne; R:GuthMaynardCorollariesUnconditional; R:ZetaZeroDensityHypothesisFiveSixths; R:Sieve/VinogradovKorobovZeroFree; R:DensityEnvelopeNoGo |
| <a id="shallow-cauchy"></a>**Shallow Cauchy / Poisson energy** | WD; zero census; HF, ACS | Eventually in T, strict-right zeros in [T,2T] at depth≤h have shifted energy hE_h≤C max(κ,2h log T)T log T, 0<h≤1/64. At h=1/log T: E_h=O(T log²T), squared-multiplicity and K/log T close-pair bounds. For every ε>0, some α gives deep count≤εN(T,2T) and combined shallow/deep budget O_ε(N) [L]. | No subcritical/vanishing collision budget, unshifted-energy bound, finite off-line support or improved on-line proportion. Shift and exact multiplicities cannot be dropped. The majorant is the Lorentzian pair sum over all zeros of the window; 70% needs hE_h+R_deep≤3N/20 at h≍1/log T. | SCP:MultiscaleLorentzL2; SCP:ShallowCauchyEnergyBound; SCP:ShallowCauchyImplications [L] |
| <a id="closed-cycle-tools"></a>**Reconstruction / auxiliary transport** | EWU, HF, FU, CHMD, PM, TG | Controlled cycle recovery, clock/phase calibration, Nyquist limits, spectral constraints and Gaussian covariance [L]. Reflection/S₂ and reverse-twisted pole transfers are support only. | Signed source selection; reconstruction and restricted covariance do not give positivity. | B:FiniteNetDerivativeRecovery; B:ProducerCompletionAndPrimeClockKernelSynthesis; A:SpectralRealisationAndOperatorConstraints |

<a id="external-literature"></a>
## Dependency / external-claim scope

| Input | Local status / limit |
|---|---|
| Zeta23 (Alpöge–Furman), pinned imported Lean dependency | Critical-line census relies on it; local IGP extension is [L]. Published-literature standing is separate. |
| Guth–Maynard large values theorem (published) | Formalized locally and unconditionally (R:Sieve/GuthMaynardTheoremOneOne) [L]; feeds the 30/13 density and 17/30 short-interval corollaries. Counts exceptions; supplies no zero exclusion. |
| [Quasi-RH manuscript](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf) | Claims Dirichlet zero-freeness Re s>7/8 [E], not RH. R:ChenGuptaLi* contains detector/density components, no zero-free capstone; continuation/contour step open. Local horizontal-collision no-go blocks an RH endpoint, not the 7/8 claim. |
| [Ordinary two-point correlation manuscript](https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf) | Fixed-form Liouville logarithmic saving claimed [E]; not power saving or growing-shift/modulus uniformity. Distinct from [logarithmic two-point theorem](https://arxiv.org/abs/1509.05422) and from local formalization. |

## Dead mechanisms / scope boundaries

[44 named failed mechanisms and 19 retired labels](rh-killed-routes.md). Scoped no-gos do not retire the live routes above. Key boundaries: fixed-aperture/fixed-rank tests are incomplete; finite index need not vanish; uniform positive aperture gaps fail; multiplicativity + polar matching + any gap up to the maximal 2log2 does not select ζ [L].

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
| RDP | ReflectiveDirichletPolynomialS2 | CACT | CriticalArithmeticCorrelationTheory |
| AKLT | ArithmeticKreinLangerTheory | ASRP | ArithmeticOfSquareRootPrecision |

## Alias lookup

BVI→[support](#bvi); C1→RW; CCM-FU→FU; CLG/TTF,K-RVM,S6F,TCD,UEB→TH; CSB,STC,U,MPLF,RHist,BPC,TQFQ,WS2,SQB→RN; D2,Q,RG,RG-ETA,TK→PA; E,EDQ,L,HDL,PSRC→MC; FZZ-P→PM; PW-B→[candidate](#pw-b); G,HC→WD; O→WL/RW (genus mechanism dead); P,SP-E→RP; SV2,RG-HF→SZ; T1,T2,Route T→TT; Route T successor/ULF sub-unit anchor→TG; Deninger→HF. [Retired labels](rh-killed-routes.md#retired-labels).
