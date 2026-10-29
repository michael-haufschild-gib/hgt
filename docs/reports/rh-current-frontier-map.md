# RH proof-route frontier

**RH open. 31 live routes; 17 standalone candidates; PW-B candidate sub-branch.**

**Corpus checkpoint:** `7f191801a37d81888855535db96bad2d6ae0fbce`.

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
| Complete ζ-Weil matrix on atomic families eventually positive definite at every fixed overlap 0<c≤1+10⁻¹⁸ for one plateau, past the Metzler threshold [L]; Liouville twin negative there for c≥1/2 [S]. RH ⇔ eventual atomic positivity at overlap c_N=(log log N)(log log log N)^β, β>2, for one Steklov profile [L]. | Overlap growth from bounded c to c_N→∞; positivity at every fixed c; bounded-overlap completeness. Selectivity against single prime flips at fixed overlap is untested. |

Sources: SP:LiouvilleOddWindowRefutationAndSelectiveFullPositivity; O:TheWidthDictionary; G:AllParityCriticalDeficitAndEndpointSobolevLaws; C:UnconditionalBirmanSchwingerRateReadsTheZeroWidth; R:LindelofCosineFiniteDefectDepth; HKT:TheFiniteIndexStratumOfZetaIsLindelofDeep [S]; TM:TransMetzlerPositivity; TM:SuperGevreyCriticalGrowth [L]; TM:LiouvilleTwinSelectivity [S].

## Live routes

Done = [L] unless marked otherwise. All routes remain open.

<a id="wl"></a>
### WL — Weil lag function

- **Path:** Actual prime lag/deficit → one-sided bound or subexponential critical energy → RH.
- **Done:** Critical energy/cross-work and linear prime-error energy criteria; bounded high-zero tail. Genus Abel slope characterizes RH plus simple zeros. Either one-sided √x log²x count bound characterizes RH; an upper count for any Λ-majorant or lower count for any Λ-minorant suffices. Exact Chebyshev transform identifies Λ. Count-preserving sign/torus gauges classified; exponentially small auxiliary sup norms force rational zeros, not the integral estimate [L]. Bounded monotone errors invert with Mertens precision [S].
- **Open:** Prove actual signed-correlation or linear prime-error energy bound. Genus saturation is stronger than RH. Chebyshev/Stirling inversion needs cancellation for its specific error, not a generic size estimate.
- **Sources:** B:WeilLagCriticalDeficitEndpointAndLimitLaw; CP:TheAbelSlopeOfThePrimeErrorIsTheArchimedeanGenus; [count precision](#count-precision); [monotone inversion](#monotone-inversion); [integrality](#integrality-precision).

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
- **Done:** Half-power/rate/strip dictionaries; fixed-modulus/below-diagonal savings; escaped-μ VK decay [L]. Count, integrality and curve precision exponents identified; Liouville odd harmonic–exponential upper count ⇔ RH ⇔ ζ-kernel index zero. Twin partial sums are torsion-ratio logarithms. Sign/torus gauges preserve Count exactly at O(√x log²x) weighted prime deficit [L/S]. Nonnegative perturbations with abscissa<1/2 preserve an existing Count; >1/2 destroys it [L]. Uniform inversion of bounded monotone errors at every exponent 1/2+δ, δ>0, ⇔ RH; exponents<1/2 impossible. Tower positivity selects coefficients exactly, unlike Count [S].
- **Open:** Produce actual moving-scale half-power cancellation, cofinal subpower energy or the odd-class upper bound. VK/PNT/short-interval laws alone supply no square-root precision; general-weight countermodels preserve them. Exact Chebyshev/Stirling identities require signed inversion control, not error size alone [S]. M=o(√x) is false.
- **Sources:** R:MobiusHilbertFormEquivalence; V:UnconditionalEscapedMoebiusDecayAndCrossRouteBridge; AKLT:TheParityFormOfTheGlobalLaw [S]; [count precision](#count-precision); [monotone inversion](#monotone-inversion); [source selection](#smap); [integrality](#integrality-precision).

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
- **Done:** Source/divisor, Hecke-defect and complete-cell receivers; Haar pole/occupation identities and full W+G=D+P+ΣV u² with G≥0, V signed; W(R)=O(R log²R), logarithmic Gram floor. One explicit plateau has eventual complete-Weil positivity at every fixed 0<c≤1+10⁻¹⁸; one-profile super-Gevrey RH receiver [L]. Liouville-twin rejection [S]. Uniform original-Γ even-power approximation [K]. Profile-uniform touching floor, ζ index, prime-edge Γ reserve/negative entries, conductor-normalized primitive curvature and fixed-conductor prime limits [S].
- **Open:** Full signed-form sign or RH-threshold work ceiling. Extend fixed bounded-overlap positivity to an RH-complete family; pay non-arithmetic Gamma edges, signed potential, first-prime/coarse and both poles jointly. Primitive-curvature/operator transfer remains open. O(R log²R) is not bounded work.
- **Sources:** J:TheIndexExit; PL:HeckeInvarianceOfTheCollidedPolarizationIsRH; [signed frontier](#signed-hodge); [prime spectrum / complete matrix](#renormalized-potential); [overlap positivity](#first-overlap).

<a id="chmd"></a>
### CHMD — Causal Hyperbolic–Modular Duality

- **Path:** Complete causal prime/Möbius wave bound or odd theta-Doob half-threshold bound → RH.
- **Done:** Wave/Doob/nodal receivers; core, radical, Schur transport, Haar approximation and Gamma cross-error O(mass) [L]. Higher-power approximation/full even-power head error [K]. Actual heads are local stopping-cell means; zero padding gives Γ(head)≤32e²Γ(f) and Γ(head)+Γ(tail)≤(2+96e²)Γ(f), uniformly in cutoff/horizon/levels. For every δ>0, one cutoff makes complete even-power error≤δΓ(f) for every finite real cell source [K]. Full Haar identity retains signed potential [L]; summed original prime-edge Gamma payment with strict reserve and full-Weil negative prime-edge entries [S].
- **Open:** Prove full wave or odd/nodal sign, paying first-prime/coarse/polar terms and infinite retained-orbit sign. Divergent prime/square coefficient masses forbid absolute payment, not signed compensation.
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
- **Done:** Ward/collision receivers; extremizer attainment/Hermite asymptotics; shifted budgets. Zero displacement≤d and deep dyadic copies≤C log X·N(t) for t log X≤c d², uniformly in 0<d≤1/2. Reality horizon 2π exp((2/3+ε)/t), 0<t≤1/8; local forces, forward simplicity and collision-continuous energy [L]. Compact-region forward simplicity even after a multiple collision; small-time collision mass counts index plus multiplicity excess; uniformly bounded N(t) iff finite off-line support [S]. On finite index, index is the least exceptional-wave count along a suitable prime-side tower [L]. Minimal-wave amplitudes recover right-zero multiplicities via nonzero spline factors; the ξ/ζ multiplicity bridge reconstructs small-time collision mass 2(κ+Σ(m−1)) from one minimal tower count, assuming finite index [S].
- **Open:** Arithmetic cap/collision extinction or all-height finite-head sign. Amplitude recovery assumes finite index and a minimal bounded subtraction; it supplies neither. No polynomial N(t) bound; local force/continuity tools do not yet give a localized energy evolution bound. Finite N(t) at each t>0 does not give uniform count or RH.
- **Sources:** R:XiWardGlobalCapAndFiniteHeadArithmetic; ALDG:HermiteHeatRootBarrier; R:Heat/HeatUniformDepthZeroDensity; R:KiKimLeeTwoThirdsHorizon; HKT:HeatCollisionsCountTheIndex [S]; AKLT:TheCollisionMassIsTheWaveNumber [L/S]; [local heat tools](#local-factors).

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
- **Done:** Exact heat explicit formula; fixed-rank signs/inertia; positivity on both log2/log3 grids with polar cancellation iff RH. Arbitrary-zero detector [L]; quantitative two-prime phase non-aliasing [S]; alternative centered-heat derivation [P].
- **Open:** Both actual grid signs at every degree/height, or one-sided vertical/prime-chirp bound. Pairwise anti-aliasing does not control coalescence or many-node Gram eigenvalues; one grid aliases.
- **Sources:** R:XiGaussianHeatTwoPrimeSourceSampling; R:HeatGridAliasingBoundary; [two-prime precision](#two-prime-precision).

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

- **Path:** Actual signed late-lag bound, complete atomic-family sign, all-generator one-prime sign or consecutive-ratio ζ-kernel tower sign → RH.
- **Done:** Atomic receivers at (log log N)^α/N, α>1; all arbitrarily small pole-free C² generators on any prime's towers decide RH. One fixed Steklov profile gives an RH-equivalent family at c_N=(log log N)(log log log N)^β, β>2, smaller than every (log log N)^{1+ε} [L]. Fixed-width complete Liouville-twin negative witnesses [S]. Integer windows/some shrinking schedule and fine mixed two-prime towers carry full index, finite or infinite; quantitative two-prime anti-aliasing; exact tower-positivity stabilizer versus square-root Count precision [S].
- **Open:** Actual signed lag/family/tower positivity or arithmetic index ceiling. Fixed-ratio positivity does not supply sign on the unbounded super-Gevrey schedule. c_N=O(log log N), β≤2 schedules, bounded-overlap completeness and an explicit shrinking full-index schedule remain open. Pairwise anti-aliasing gives neither zero spacing nor a many-node Gram floor; tiny generator support does not bound aperture.
- **Sources:** S:EveryWidthDecidesTheCriticalLine; SMAP:TheDyadicSignOfAPoleFreeGeneratorIsRH [L]; HKT:ShrinkingAtomsCarryTheWholeIndex; HKT:IndexZeroSelectsTheVonMangoldtWeight; AKLT:FineTowersDecideEveryOrbitKernel [S]; [atomic synthesis](#atomic-stability); [two-prime precision](#two-prime-precision); [fixed-width twin test](#twin-overlap); [source selection](#smap).

<a id="act"></a>
### ACT — Arithmetic criticality / single-shift variation

- **Path:** One fixed theta shift a>0 → D_a(u)≤2S_a(u)+V_a(u) for every even compact C² profile → odd Weil positivity → RH.
- **Done:** Exact single-shift ground-state variation receiver; light-cone signs; fixed-support reflected-prime collar paid at sufficiently large shift.
- **Open:** One fixed shift paying every profile/support, including exterior primes and signed/polar remainder. Support-dependent absorption is insufficient.
- **Sources:** D:ShortProfilePoleFreeVariationInequality; D:RestrictedWeilGroundEnergyCriticalAtInfinity.

<a id="aip"></a>
### AIP — Arithmetic incidence positivity

- **Path:** Actual prime incidence + plateau gauge → all-aperture GlobalIncidenceAllocation → odd positivity ↔ RH.
- **Done:** Allocation/odd-sign and complete-cell receivers; full W+G=D+P+ΣV u² with G≥0, V signed; logarithmic Gram floor. One explicit plateau has eventual complete-Weil positivity at every fixed 0<c≤1+10⁻¹⁸, including widths whose Markov Gram admits no Metzler gauge. One-profile super-Gevrey RH receiver [L]; complete Liouville-twin rejection [S]. Uniform original-Γ even-power approximation [K]. Profile-uniform touching floor, fixed-conductor prime-window limits, prime-edge Γ reserve/negative entries and conductor-normalized primitive curvature floor [S].
- **Open:** Sign on an RH-complete overlapping family, beyond the fixed-ratio interval. Pay non-arithmetic Gamma edges/signed potential and first-prime/coarse/polar terms. Scalar primitive-curvature floor needs integral/symbol identification and actual operator matching; fixed-conductor prime limits need continuous-weight transfer, growing-conductor operator control and full residual control.
- **Sources:** I:GlobalIncidenceAllocationCondition; I:GlobalSharedSurplusAllocation; [signed frontier](#signed-hodge); [prime spectrum / complete matrix](#renormalized-potential); [overlap positivity](#first-overlap).

<a id="acs"></a>
### ACS — Arithmetic Castelnuovo–Severi effectivity

- **Path:** Full-source effectivity / bounded-error Rosati heights / all-ordinate chirality → Hodge → RH; complete-cell index payment is a source target.
- **Done:** Effectivity/height/chirality and complete-cell receivers; full signed Haar identities, logarithmic work/Gram bounds. Fixed-profile complete-Weil positivity through c=1+10⁻¹⁸ and one-profile super-Gevrey RH receiver [L]; Liouville-twin rejection [S]. Uniform original-Γ even-power approximation and finite-field Weyl pole survival [K]. Profile-uniform touching floor, count/gauge precision, prime-edge Γ reserve/negative entries, primitive curvature and fixed-conductor prime limits [S]. Actual elliptic adelic Haar, finite-place rational approximation, local shells/spherical integral, simple-root lifts and real loop Iwasawa existence [K]; ideal norms [L]. Full K∩B=M and factorization-independent Borel-equivariant spherical function [S]. Sharp 16/21 matrix certificate and below-threshold ζ moments [L].
- **Open:** Actual quadratic RI with degree-zero subquadratic growth, Rosati-height bound or index zero. Pay full signed graph/coarse/mixed/polar form on RH-complete families. Census needs wider-frequency signed moments/column normalization. Audit full compact–Borel/spherical chain. Arithmetic quotient covolume/unipotent measures, local Iwasawa-character identification, Euler product/Eisenstein unfolding and characteristic-zero effectivity bridge remain; finite-place approximation does not construct the global quotient measure.
- **Sources:** G:ExactArithmeticSourceEffectivity; AE:TheEffectivityCalculus; [signed frontier](#signed-hodge); [prime–polar cancellation](#prime-polar-cancellation); [complete matrix](#renormalized-potential); [overlap positivity](#first-overlap); [kernel index](#hecke-krein); [census](#pair-schur-slack).

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
| <a id="sc"></a>**SC — Stokes/Witt−Krein:** cross-fibre indefinite invariant → orientation. | Rigged fibres and Witt/Selberg coordinates [L]. Tempered orbit index equals supremum over consecutive-ratio towers or fine cyclic towers within any two-prime lattice, including infinite index; no finite-pair premise [S]. | Source-fixed cross-fibre sign/index selecting the wall. Fine-grid exhaustion and pairwise two-prime precision supply no arithmetic sign/index ceiling; locality is invariant under unitary twins; finite-pair classification still requires its representation. | R:PaperKreinWallFourierCompletion; V:WittSelbergReceiverCoordinates; [kernel index](#hecke-krein); [index scope](#aklt); [two-prime precision](#two-prime-precision) |
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
| <a id="signed-hodge"></a><a id="balanced-haar"></a>**Haar / signed source payment** | HF, ACS, AIP, CHMD | Individual Haar W≥mass/10; D_H≥log(2)·mass/12; original poles give D_H+P≥D_H/8 and ≥mass/144. Signed Gamma cross-error≤16e^(1/2)mass [L]. Actual cross-entries have summable positive Laplace expansion. With u_a=√(2a+1)d_a, G=½ΣK_ab(u_a−u_b)²≥0: Γ=Σrow_a u_a²−G and full original W+G=D_X+P+ΣV_X(a)u_a², retaining outgoing charge and both poles; V_X signed [L]. On literal prime edges n_b=m n_a, a≥1: 0≤J_ab≤log(2)M_b/√m. The shared graph is paid once: 0≤G_prime≤G, Q_res+G_prime=Q_X, Q_res≥(1−log2/log3)Q_X≥0; every surviving prime conductance is strictly positive. Exact W+(G−G_prime)=Q_res+absent-root diagonal+P+ΣV u². The exact full-Weil matrix retains both poles jointly and has prime-edge entries≤−(log3−log2)M_b/√m<0. All claims passed a clean direct Lean check [L]. | Control the remaining non-arithmetic Gamma graph and signed diagonal jointly with the retained prime reserve, roots, and poles; then first-prime/coarse/head costs. Neither entrywise coupling positivity nor the exact identity supplies a lower floor; no positivity of V_X is proved. | G:TheHaarArithmeticReservePaysBothPoles; G:TheHaarGammaCrossTermsCostOnlyMass; G:TheHaarGammaCrossTermsArePositive; G:TheHaarGammaDebtIsAnAdditiveGraph; G:TheHaarPrimeEdgesRetainTheirGammaReserve [L]; [checked payment](../drafts/pipeline/3-formalized/acs-haar-prime-edges-retain-gamma-reserve.md) |
| <a id="haar-occupation"></a>**Subcritical Haar occupation** | HF, ACS, AIP | x_a=d_a/√(2a+1), cell weight≥1/2; cross-kernel Λ(n/m)/(n/m). For every finite signed Haar source, D_H+B=½Σ_e occupation_e+R, R≥0. B=½Σ_a(EulerOffset−outgoing_a)x_a²≥0; each outgoing row is a subseries of the complete source-prime ladders, EulerOffset=Σ_p log p/(p²−1). Complete basis, original-domain membership and full summability proved [L]. | Pay B jointly with original Gamma/polar costs; B≥0 does not permit dropping it from an upper bound. Zero original root coordinate is not transformed-ground orthogonality; occupation positivity is not full-Weil positivity. | G:TheHaarDivisorFormHasSubcriticalPrimeWeights; G:TheHaarDivisorReserveControlsValuationOccupation; RAPT:TheInversePrimeNumberOperatorHasOccupationEnergy [L] |
| <a id="generator-heads"></a>**Actual generator heads / even-power approximation** | CHMD, HF, ACS, AIP | Exact stopping averages preserve mean; tail⊥head in L² and tail mass≤32Γ(f)/(1+log A). The actual finite BV profiles satisfy Γ(head)≤32e²Γ(f) and Γ(head)+Γ(tail)≤(2+96e²)Γ(f), uniformly in cutoff and horizon. Signed compensation gives complete even-power error≤δΓ(f) with one cutoff before all finite sources [K]. | First-prime/coarse/polar payment and retained-orbit sign. Ordinary mean preservation does not preserve both exponential Weil moments; complete retained orbits remain noncompact. | SAHT:ActualGeneratorHeadsAreLocalIntervalMeans; SAHT:ActualGeneratorHeadsAndTailsHaveUniformGammaBounds; SAHT:AllEvenPrimePowersHaveOriginalGammaApproximation [K] |
| **All-level Euler approximation** | HF, ACS, AIP, CHMD | Every lag has head error≤96Γ/(1+log A); finite prime sets have the corresponding coefficient-mass bound. For all primes and k≥3, H=Σ2log(p)/p^(k/2)<∞ and sum of absolute errors≤96HΓ/(1+log A), uniformly in source horizon, levels and every finite selection [K]. | Prime/square absolute coefficient masses diverge; signed even-power compensation follows from [actual-head approximation](#generator-heads) [K]. First-prime/polar control and retained-orbit sign remain; general BV sources retain noncell components. | SAHT:FiniteEulerFactorsHaveAllLevelGeneratorApproximation; SAHT:AllHigherPrimePowersHaveAllLevelGeneratorApproximation; SAHT:CriticalEulerCoefficientMassStartsAtCubes [K] |
| <a id="touching-mixed"></a>**Mixed Gamma / reserve** | RW, HF, ACS, AIP, CHMD | Mixed Γ coupling²≤128e^(1/2)Γ(g)·mass(h); exact interval and balanced-Haar energies. Finite disjoint mean-zero interval families, including touching endpoints, have absolute Gamma off-diagonal error paid once by boundary remainders; Haar specialization costs O(mass) [L]. Ordered square reserve and sharp unattained norm π/2 [S]. | Joint signed arithmetic payment using actual boundary reserve; O(mass) does not establish a positive remaining floor. No uniform positive relative reserve. | G:GammaCouplingUsesOnlyDetailMass; G:GammaFiniteMeanZeroOffDiagonal; G:TheHaarGammaCrossTermsCostOnlyMass [L]; AID:TheOrderedWeilSourceRetainsItsGammaSquareReserve [S] |
| <a id="prime-polar-cancellation"></a>**Full prime–polar cancellation** | RW, HF, ACS, AIP, CHMD | For every ε>0, eventually R, every real compact BV f supported in [−R,R]: abs(primeSum(f)−P(f))≤ε exp(R)(Γ(f)+mass(f)). All prime powers and both poles retained; no derivative norm [S]. Smooth-cutoff frequency bounds [L]; square boundary ζ′/ζ(1+it)=o(log abs(t)) [L]. | exp(R) loss prevents aperture-uniform relative smallness, index ceiling or sign. | M:ThePrimePolarCutoffHasUniformFrequencyBounds; R:Sieve/ZetaLogDerivIsSublogarithmic [L]; AID:TheFullPrimePolarSourceCancelsInGammaNorm [S] |
| <a id="renormalized-potential"></a><a id="tower-finite-part"></a><a id="ramanujan-quasimodes"></a>**RAPT — prime / complete-Weil spectra** | HF, ACS, AIP | Prime gap 2log2; bounded prime spectrum/simple eigenlines→E_m=γ_E+log m+tameDifferent(m) [L]. For fixed C² profile φ on [0,1], ∫φ²>0, width c/N, 0<c<1: complete-W bounded counts/eigenlines converge to arithmetic spectrum. Every fixed finite Ramanujan packet has identity Gram and diagonal complete energy F_φ(c)+E_m−γ_E+α·1_(m=1), α=c(∫φ)²/∫φ². Both poles select conductor one; Markov has −α instead of +α. For fixed integers q>0,n,h≥0, 0<A≤B, Σ_{AN<k≤BN}Λ(k)c_q(kn+h)/k→log(B/A)c_q(n)c_q(h)/φ(q); all prime powers retained. Normalized modes inherit successor eigenvalue c_q(h)/φ(q) [S]. | Audit scalar-limit drafts; continuous compact-weight transfer, growing conductor/energy, full residual control and sign on RH-complete overlapping families. Fixed-mode residuals are width-uniform [S], not operator-norm convergence or ξ spectrum. Charge reserve degenerates as profiles approach q=1. | RAPT:TheBoundedPrimeSpectrumIsTheAdjunctionSpectrum [L]; RAPT:TheBoundedCompleteWeilSpectrumIsTheAdjunctionSpectrum; RAPT:TheCompleteWeilFormIsDiagonalOnFiniteRamanujanPackets; RAPT:TheMarkovAndWeilPacketFormsHaveOppositePoleShifts; CACT:UnitAveragesDiagonalizeSuccessorCorrections; CACT:PrimeResidueWindowsConvergeToTheirUnitMean; CACT:ActualPrimeWindowsDiagonalizeAffineRamanujanModes [S] |
| **Touching reserve / bounded-energy compactness** | HF, ACS, AIP | For fixed nonzero C² profile on [0,1], q=(∫φ)²/∫φ²<1: exact full matrix retains both poles and actual boundary prime star; nonratio operator error O_φ(log N/N). One mass floor plus (1−q)·primeDefect/4 controls all 0<c≤1. Finite Ramanujan coordinate detection and width-uniform norm quasimodes exclude eigenvalues below endpoint conductor-one energy [S]. | Source chain uncompiled/unwired; positive-profile consequence below [S]. Extend beyond ratio one; q→1 removes strict reserve. Fixed-mode convergence is not full operator-norm convergence. | CACT:TheCompleteWeilMatrixKeepsItsBoundaryCorrection; CACT:OneRamanujanFamilyDetectsAllBoundedEnergiesThroughTouching; CACT:RamanujanQuasimodesAreUniformThroughTouching; CACT:OneHorizonMakesTheCompleteWeilMatrixPositiveThroughTouching [S] |
| **Growing Ramanujan frames** | HF, ACS, AIP | For Q≥2, full-horizon Gram≥(log(N+1)−2log Q)Σd_m²; window square-mass discrepancy≤Q(Q−1)Σd_m² [L]. On (A,A+N], harmonic Gram error≤Q(Q−1)/(A+1)Σd_m². Every dyadic annulus (A,2A] with A≥4Q(Q−1) has frame bounds 1/4 and 5/4. Literal prime kernel compressed to that single annulus is identically zero [S]. | Cross-annular prime transport, complete-Weil signed energy and complement control at growing Q; positive Gram floor for N+1>Q² is not sign or full-index exhaustion. | CACT:GrowingRamanujanFamiliesHaveASquareRootHorizon [L]; CACT:AnnularRamanujanFamiliesHaveTwoSidedFrames [S] |
| <a id="counting-positivity"></a>**ACP — finite prime gap selection** | HF, ACS, AIP, SRT | All finite flip sets: exact conductor weights, full resolvent limit and greatest gap from secular signs. Single-prime gap=min(r_p,2log2), below ceiling iff p<11. Interior gaps strictly decrease under proper inclusion. Maximal base gap plus exact untwisted dyadic-probe lower bound selects the empty flip set [L]. | Finite sign-flip class only; no full Weil sign or arbitrary-weight selector. Every fixed probe tolerance admits remote nontrivial flips. | ACP:TheFinitePrimeSecularSignsDetermineTheGap; ACP:TheParitySecularRootDeterminesTheGap; ACP:OneDyadicProbeSelectsTheFinitePrimeSource; ACP:ConductorMassBoundsGapLossAndProbePrecision [L] |
| **ACP — infinite patterns / exhaustion** | HF, ACS, AIP, SRT | Every pattern has Euler density c_P and actual conductor coordinates. Bounded-energy mass converges to counted mass; c_P=0 iff mass escapes every bounded window. Full actual resolvent converges for every 0<s<2log2, to zero when c_P=0 [L]. Every pattern has an attained greatest gap; for c_P>0 secular signs classify it exactly, and finite-prime cutoff gaps decrease to it [S]. Sparse infinite flips retain prescribed submaximal gaps; cofinite flips have gap zero [L]. | Zero-density greatest-gap classification; infinite-pattern maximal-gap/source selection; full signed Gamma/pole payment. A zero limiting resolvent alone gives no eventual sign. | ACP:EveryPrimePatternHasActualConductorCoordinates; ACP:PrimeCountsDetermineEveryBoundedSpectralMass; ACP:EveryPrimePatternHasItsFullArithmeticResolvent; ACP:CofinitePrimeFlipsHaveZeroGap [L]; ACP:PositiveDensityTransfersTheExactCutoffGap [S] |
| <a id="smap"></a><a id="nonratio-lags"></a>**SMAP — full source selection** | AIP, HF, ACS, SRT, MC | Full overlapping-atom positivity selects RH and λ=Λ under abs(λ)≤Λ [L]. For any fixed prime, all C² compact generators have tower index zero iff RH and λ=Λ on n≥2. Thus tower positivity implies Count, but its additive stabilizer is δ(n)=0 for n≥2: Λ+1/n has Count iff RH yet is never tower-positive [S]. Λ and its Liouville twin cannot both be tower-positive along one nonnegative nonzero generator at any spacing [L]. | Prove actual Λ sign for every generator/window. Exact source selection is not a sign producer; Count alone cannot supply tower positivity for general weights. One preselected generator is insufficient. | SMAP:PositivityAtEveryRootSelectsTheVonMangoldtWeight; SMAP:TheDyadicSignIsRigid [L]; HKT:IndexZeroSelectsTheVonMangoldtWeight; ASRP:TowerPositivityIsPrecisionExact [S] |
| <a id="atomic-stability"></a><a id="levy-approximation"></a><a id="atomic-dirichlet"></a>**SSHA — atomic synthesis** | SRT, AIP, HF, ACS | Full W continuity; fixed-width spline families and widths (log log N)^α/N, α>1, are RH-complete. Single Steklov profile φ∈C_c^∞([-1,1]), ∫φ=1, satisfies ‖φ^(q)‖₁≤A12^q q!log(q+3)^{2q}. For every β>2, RH ⇔ eventual full-Weil positivity on all atomic coefficients at dilation κ_N=N/c_N, c_N=(log log N)(log log log N)^β=o((log log N)^{1+ε}) for every ε>0 [L]. Fixed-width integer windows and some shrinking schedule carry full index [S]. | Actual family sign. β≤2, c_N=O(log log N), bounded-overlap completeness and explicit shrinking full-index exhaustion remain open. No compact Gevrey profile of order≤1; this does not exclude logarithmic Denjoy–Carleman profiles or settle endpoint completeness. | SSHA:UnboundedOverlapIsTheRiemannHypothesis; SSHA:TheDenjoyCarlemanProfiles; TM:SuperGevreyCriticalGrowth [L]; HKT:ShrinkingAtomsCarryTheWholeIndex; HKT:TheReceiversEndAtTheQuasiAnalyticBoundary [S] |
| <a id="spacing-scale"></a><a id="interaction-stability"></a><a id="arithmetic-sections"></a>**Profile-uniform touching sections** | HF, ACS, AIP, SRT | Markov fails for e/(2π)<width/spacing<1; complete-Weil positivity holds for suitable smooth plateaus at each fixed 0<c<1 [L]. For every b<2−log(2π), ε>0, one smooth profile of mass>1−ε gives W≥b‖x‖² at one eventual horizon simultaneously for every 0<c≤1 and every vector, retaining all prime/polar terms [S]. | Profile-uniform touching capstone/dependency audit remains distinct from fixed-profile Trans-Metzler positivity below. Horizon need not be uniform as profile→indicator; RH-complete exhaustion remains open. | SSHA:TheMarkovFormFailsInsideTheSeparatedRegime; CACT:SmoothPlateausMakeTheSeparatedCompleteWeilMatrixPositive [L]; CACT:OneHorizonMakesTheCompleteWeilMatrixPositiveThroughTouching [S] |
| <a id="primitive-curvature"></a>**Primitive overlap curvature** | HF, ACS, AIP | For m>1, E_m(k)=Σ_(ζ primitive m) abs(Σ_(j<k)ζ^j)²=Σ_(d∣m)μ(m/d)r_d(d−r_d), r_d=k mod d. E_m(k)=0 iff m∣k; otherwise cyclotomic norm gives E_m(k)≥φ(m). Actual A_m(t)=Σ_(d∣m)μ(m/d)d²{t/d}(1−{t/d}) interpolates adjacent E_m values; A_m(t)/φ(m)≥{t}(1−{t}) for t≥0, uniformly in m [S]. | Audit both drafts. Integral/symbol identity, actual overlapping-operator realization, smooth transfer and conductor/overlap-uniform low-energy exhaustion remain. Scalar floor vanishes at integers; selected-mode positivity is not full-Weil sign. | CACT:PrimitiveRootPrefixEnergyIsAMobiusQuadraticRemainder; CACT:CyclotomicNormGivesAConductorUniformCurvatureFloor [S] |
| <a id="first-overlap"></a>**Trans-Metzler complete positivity** | HF, ACS, AIP, SRT | For φ=plateau(1/1000), complete Weil matrix is eventually positive definite at each fixed w=c/N, 0<c≤1+10⁻¹⁸. Reference floor1/25 plus prime-defect reserve absorbs full overlap/drift perturbation, leaving normalized floor1/120 for 1/2≤c≤1+10⁻¹⁸. At w=(1+10⁻¹⁸/2)log(1+1/N), complete positivity coexists with no unimodular Metzler gauge for the Markov Gram [L]. | Extend bounded-ratio positivity to an RH-complete unbounded-overlap family, or prove bounded-overlap completeness. Generic tempered finite-off-line zero models do not force fixed-ratio positivity; no actual ζ finite-support claim follows. Selectivity is shown against the Liouville twin only; single prime flips ω_p, p≥11 (pole kept, maximal gap) are untested at fixed ratio. The argument is perturbative around touching (overlap error O((wN)²)). | TM:ExplicitPlateauParameters; TM:TransMetzlerDecomposition; TM:TransMetzlerPositivity [L]; TM:ZeroSideStratum [S] |
| <a id="twin-overlap"></a>**Fixed-width Liouville selectivity** | HF, ACS, AIP, SRT | For nonzero C² φ supported in [0,1], c_RE=exp(β(φ)/‖φ‖₂²)/(2π)<1 and Nw_N→c>c_RE, the complete Liouville-twin form has an eventual negative atomic witness; one exponential moment vanishes, killing the full pole product. Explicit plateau covers every c≥1/2; some smooth plateau every c>e/(2π). Conversely all atomic tests are nonnegative for every N≥1 at 0<c≤fixedWidthRatio times atomSpacing(N) [S]. | Dependency audit; actual ζ sign beyond the established fixed-ratio range and RH-complete exhaustion. No sharp transition established; narrow-width twin survival forbids blanket fixed-width source selection. | TM:LiouvilleTwinSelectivity [S] |
| <a id="lorentzian"></a><a id="polar-gluing"></a><a id="frobenius-repair"></a>**ALG — form reductions / repairs** | HF, ACS, AIP, LI | Metzler below spacing and subspacing Hodge [L]; no nonnegative unitary gauge above overlap ratio 1 [S]. At every width, full W≥0 iff primitive Markov sign plus pole-corrected affine floor [S]. Polar/Frobenius repairs classified [S]. | Prove both inequalities on complete families; identify/pay any correction in original W. A corrected positive form is not the original. | ALG:TheHodgeIndexIsAGapOnThePoleComplementAndOneScalar; ALG:TheHalfDefectIsTheOptimalHodgeRepair [S] |
| <a id="turan-layer"></a><a id="local-factors"></a><a id="aldg"></a>**Polynomial / local heat tools** | LA, WD; HF, ACS | Ordinary ξ coefficients Turán; Hermite barriers/attainment. Uniform shrinking-depth transfer; local cofactors, exterior forces O(log X), forward simplicity, collision-continuous energy and gap-independent pair flux [L]. Simple-zero velocity/local branch and compact-region forward simplicity after arbitrary positive-time collisions [S]. | Localized energy evolution and small-time N(t) bound; all-height finite-head signs. Ordinary-coefficient Lorentzianity is not Jensen real-rootedness; positive Ramanujan+Lorentzian Euler factors force impossible prime equality [S]. | R:Heat/HeatUniformDepthZeroDensity; R:Heat/HeatExteriorForce; R:Heat/HeatZeroSumContinuity; R:Heat/LocalizedHeatPairForce [L]; R:Heat/HeatLocalizedEnergyEvolution; ALG:RamanujanAndLorentzianMeetOnlyAtTheWeilBound [S] |
| **ζ growth / heat horizon** | LA, WD | μ(11/18)≤1/9 via A·B·A²B and interpolated profiles. Heated zeros real/simple beyond R=max(X₀,2π exp((2/3+ε)/t)); nonreal count and collision mass≤C(R+1)log(2+3(R+1)) [L]. | Still exponential in 1/t; no polynomial upper count, uniform total count or extinction. | R:ZetaElevenEighteenthsLineBound; R:ZetaElevenEighteenthsProfiles; R:KiKimLeeTwoThirdsHorizon [L] |
| <a id="outward-field"></a><a id="index-descent"></a>**AES / AID / CACT — source work and index** | HF, ACS, SRT | RH iff ℰ<1; ℰ finite iff finite off-line support. Actual completed W(R)≤64R L_R(L_R+1), abs(W_N(R))≤128R L_R(L_R+1), L_R=C+log(R+4), R≥4, uniformly in taper N [L]. R²(W(2R)−W(R))↑E₂; E₂ finite iff finite support; RH iff E₂≤3·431349/2000. Annular increment≤39/50 eventually iff finite support; at every R≥4 iff RH [S]. | Bounded work, subquantum annular increment or critical-energy ceiling. O(R log²R) retains all exterior interactions but proves none of these targets. | AES:TheTransverseEnergyOfTheZeroDivisor; CACT:TheCompletedSourceWorkHasALogarithmicCeiling [L]; AID:TheCriticalSourceRateHasACanonicalEnergy; AID:EveryOffLineQuartetCostsAStrictScaleQuantum [S] |
| <a id="hecke-krein"></a>**HKT — actual kernel index** | HF, ACS, SRT, WD; SC | Actual ζ spline-kernel κ=#distinct right zeros, even; RH iff κ≤1; finite κ iff finite off-line support iff orbit Krein–Langer decomposition. Integer/two-prime/all-width families carry κ; prime tower counts distinct p^(ρ−1/2), with exact Nyquist alias bound; at most κ(κ−1)/2 blind primes, and positivity on infinitely many towers forces κ=0 for positive-plus-finitely-many-pairs kernels. Global law: κ=0 iff eventually ψ(x)−x≤C√x log²x; for curve data over 𝔽_q, κ=0 iff the lower square-root point count. κ tied exactly to critical energy and small-time collision mass [S]. On finite index, a suitable tower's minimal exceptional-wave count is κ, and collision mass=2(κ+multiplicity excess) [L]. Minimal amplitudes equal right-zero multiplicities times nonzero spline factors; ξ/ζ multiplicities agree, reconstructing 2(κ+Σ(m−1)) from one minimal count on finite index [S]. | Independent arithmetic index/energy/growth ceiling or a producer of the one-sided count. Classification supplies no finiteness; explicit shrinking-width full-index schedule remains open. | HKT:TheConverseKreinLangerTheoremForOrbitKernels; HKT:EveryReceiverAtEveryWidthIsBoundedByTheIndex; HKT:TheNyquistLawOfAPrimeTower; HKT:AllButFinitelyManyPrimesSeeTheWholeIndex; HKT:TheGlobalLawIsTheOneSidedSquareRootCount; HKT:IndexIsEnergy; HKT:HeatCollisionsCountTheIndex [S]; AKLT:TheCollisionMassIsTheWaveNumber [L/S] |
| **HKT — decomposition / compression** | HF, ACS, AIP, SRT; SC | Hermitian κ≤m iff PSD after adding m squares; finite-index witness attained. Atomic Dδ₁−P has window index 0/1/≥2 across log N−γ and log N−γ−2log2; every fixed D has infinite lattice index. A curve's characteristic polynomial annihilates its trace kernel regardless of purity. Euler compressor δ₁−cδ_p, abs(c)≤p^(−1/2), preserves every nonzero right-strip pair and its finite-pair index [S]. | Positive-minus-finite-rank is not a covariant character decomposition. Spectral annihilation is a receiver, not a count producer; ordinary Euler compression cannot lower index. Need actual arithmetic count/index control. | HKT:FiniteIndexIsPositiveMinusFiniteRank; HKT:TheIndexOfAFiniteExponentialSum; HKT:TheIndexOfABohrSeries; HKT:TheMarginIsTheWidthOfTheIndexOneWindow; AKLT:CompressionsAreReceivers [S] |
| <a id="aklt"></a>**AKLT — cyclic/tower detection** | HF, ACS, SRT; SC | PSD+finitely many nonunitary pairs: almost every faithful tower carries full index; infinitely many PSD prime towers force zero. Every finite negative witness of a continuous logarithmic kernel persists on fine grids. Tempered orbit index equals supremum over consecutive-ratio towers and over a fine sequence ⟨p^a q^b⟩ inside any two-prime lattice; finite or infinite index. Actual ζ specializes without finite-pair membership [S]. Unitary twists preserve pair decomposition, tower faithfulness and cofinite full-index detection [L]. For a separated finite-pair kernel, any minimal bounded wave subtraction recovers its outer nodes and weights up to permutation [S]. | Actual arithmetic tower signs/index ceiling; wave rigidity assumes the finite-pair representation and bounded subtraction. Locality is twin-blind. Fine mixed p–q generators differ from pure-prime towers, whose log spacing≥log2. General ℤ² cyclic positivity still fails. | AKLT:CyclicSubgroupsDecideTheKreinLangerClass; AKLT:TowerFaithfulSpectraAreDecidedByAlmostEveryTower; AKLT:FineTowersDecideEveryOrbitKernel [S]; AKLT:LocalityIsTwinBlind [L]; AKLT:TheIndexIsTheNumberOfExceptionalWaves [S] |
| <a id="two-prime-precision"></a>**Two-prime phase separation** | SRT, HCF, HF, ACS; SC | For fixed distinct primes p,q, some c,C>0 give abs(e_p)log q+abs(e_q)log p≥c·min(abs(Δ),(2+abs(Δ))^(−C)), e_p=Δlog p−2πk_p, for every real Δ and integer k_p,k_q. One prime aliases at Δ=2π/log p. Integrality gives exponential separation; Baker gives polynomial separation. Dirichlet supplies nonzero integer forms≤log p/(n+1) [S]. | Audit source; transfer pairwise precision to actual many-node sampling/Gram control and arithmetic sign. Constants depend on p,q; bound degenerates as Δ→0 and gives no zero-spacing lower bound, RH or finite index. | ASRP:TwoPrimeTowersSeeEveryOrdinateDifference [S] |
| **AKLT — index stability / exceptional waves** | HF, ACS, SRT; SC | Finite Hermitian limit index is an eventual lower bound under pointwise convergence. For PSD+κ pairs with nonzero limiting weights and nodes separated/nonunitary at one element, index eventually equals κ. On a separating tower, least number of exponential waves whose subtraction leaves a bounded count is exactly κ; outer nodes attain it [S]. | Actual finite-pair representation and arithmetic count bound remain unproved inputs. Index can drop under vanishing weights, collisions or unit-circle contact; generic wave theorem is not an unconditional ζ finite-support bound. | AKLT:TheIndexIsContinuousOffTheDiscriminant; AKLT:TheIndexIsTheNumberOfExceptionalWaves [S] |
| **AKLT — local index / twist completion** | HF, ACS, SRT; SC | On ℤ^S, finite card(S)≥2, axis-supported kernels have index 0 or ∞; positive-weight axis sums of δ₀−r^abs(n), r>0, have index∞. Euler Poisson kernels/twists are PSD. For abstract finite curve data, explicit q↦qⁿ, β↦βⁿ base change identifies twistCount with twisted-base-change pointCount. Twist preserves index; one uniform square-root upper bound over every 2^j base change ⇔ unitarity [S]. | Finite nonzero index requires off-axis interaction. One twist alone fails for an abstract four-eigenvalue datum, not an actual curve. Need actual complete-source/count producer; Gamma is not axis-supported. | AKLT:LocalConstituentsMeetOnlyAtTheIdentity; AKLT:TheTwistTowerCompletesTheUpperCount [S] |
| <a id="count-precision"></a>**Square-root count / parity** | WL, MC, HF, ACS, SRT | Count_Λ: ψ−x=O(√x log²x) ⇔ either one-sided bound ⇔ RH; precision exponent=sup Reρ. For a≤Λ, Count_a ⇔ RH and Σ_{n≤x}(Λ−a)=O(√x log²x). Sign flips on F qualify exactly when Σ_{p≤x,p∈F}log p has that bound; torus gauges use Σ_{p≤x}(1−cos(2πt_p))log p. Finite prime flips preserve Count iff RH. Liouville twin sum=2ψ(⌊√n⌋)−ψ(n)=−log(torsion quotient); harmonic–exponential odd upper count ⇔ RH [S]. | Produce actual Count_Λ/odd-class bound. Count does not identify Λ among gauges. PNT/short-interval laws are too coarse; exact Chebyshev/Stirling inversion needs its specific signed error, not size alone. Generic size-controlled inversion has no uniform sublinear bound [S]. | ASRP:TheGaugeStabilizerOfTheCount; ASRP:ThePrecisionLedgerOfTheCount [L]; ASRP:TheCountIsTheRiemannHypothesis; ASRP:WherePrecisionIsLost; AKLT:TheParityFormOfTheGlobalLaw [S] |
| <a id="monotone-inversion"></a>**Monotone Möbius inversion** | WL, MC | I_x(E)=Σ_{k≤x}μ(k)E(x/k). For E nondecreasing on (0,∞), abs(E)≤B on (0,x], Abel summation gives abs(I_x(E))≤3B max_{k≤⌊x⌋}abs(M(k)). I_x(1)=M(⌊x⌋). RH ⇔ for every δ>0, uniformly over such E with B=1, I_x(E)=O(x^{1/2+δ}); no uniform exponent<1/2 [S]. | Prove actual Mertens-scale cancellation or suitable structure for the specific Chebyshev/Stirling error. Monotonicity transfer supplies neither input; no O(√x) endpoint equivalence asserted. | ASRP:MonotoneErrorsInvertAtMertensPrecision [S] |
| **One-signed count perturbations** | WL, MC; HF, ACS, SRT | UpperCount(b), b≥Λ, or LowerCount(a), a≤Λ, implies RH. For b≥Λ, Count(b) ⇔ RH and b−Λ∈𝒬, where 𝒬 means partial sums O(√x log²x). For δ≥0, σ_abs<1/2 ⇒ δ∈𝒬 ⇒ σ_abs≤1/2; σ_abs>1/2 destroys any existing Count [L]. | Produce actual majorant/minorant bound; no square-root estimate constructed. Boundary σ_abs=1/2 not classified. | ASRP:OneSignedPerturbations [L] |
| **Curve precision calibration** | WL, MC, HF, ACS; SC | For finite curve data, absolute error O(q^{kθ}) ⇔ lower-count half ⇔ all normalized Frobenius moduli≤q^{θ−1/2}. Attained exponent=1/2+max log‖β‖/log q for nonempty data; square-root precision iff unitary. Odd hyperelliptic calibration attains it. Upper square-root count suffices if no real outer eigenvalue. Golden abstract datum has N_k≤5^k+1 and N_k/5^k→1, but lower/absolute precision iff θ≥1/2+log φ/log5>1/2 [S]. | Actual ζ square-root estimate/characteristic-zero source bridge. Abstract upper counts miss real outer spectrum; this is not an actual-curve counterexample and does not invalidate either one-sided ζ criterion. | ASRP:CurvesCalibrateThePrecisionExponent [S] |
| <a id="integrality-precision"></a>**Integer-auxiliary precision** | WL, MC, HF, ACS, SRT | Integrals of integer polynomials of degree≤N−1 form exactly lcm(1,…,N)⁻¹ℤ; least positive value=e^(−ψ(N)), attained. Square-root analytic ceiling and floor each ⇔ RH; each power-scale infimum=sup Reρ. Integer Dirichlet auxiliary floor=e^(−mψ(N)), m≥0; length N gives <N real zeros [S]. If deg P≤n, then P(a/b)=0 or abs(P(a/b))≥b^(−n); sup≤e^(−(n+1)+C(n+1)^θ), θ<1, eventually forces zeros at 0,1/2,1 [L]. | Independent analytic integral ceiling/floor. Sup-norm vanishing is a necessary constraint, not an auxiliary construction or a no-go for positive integrals. Pointwise positivity is not required. | ASRP:TheIntegralityLatticeOfTheHorizon; ASRP:TheIntegralityExponentIsTheZeroWidth; ASRP:IntegerDirichletPolynomialsAtArithmeticPoints [S]; ASRP:SupNormCeilingsForceVanishingAtSmallRationals [L] |
| <a id="arithmetic-polarization"></a><a id="conjugate-diagonal"></a>**Polarization / theta detectors** | HF, ACS, OWU, SRT, RW | Collided form computed from log abs(ξ) and theta prefixes; its translation invariance iff RH. Fixed-aperture log-Sobolev comparison, signed Gårding and finite index. Quantitative theta/divisor detectors [L]. | Actual Hecke-defect upper bound or full sign; collided positivity and detector accuracy do not give either. | PL:HeckeInvarianceOfTheCollidedPolarizationIsRH; PL:WeilsFormHasFinitelyManyNegativeDirectionsAtEveryAperture; CDG:PolynomialThetaLocalSelection |
| <a id="bvi"></a>**BVI — cancellation / rate dictionaries** | MC, CTF, PM, HF | Exact escaped-μ, receiver, Hecke-defect, zero-strip and integer-theta rate dictionaries; uniform VK decay. Fixed-modulus/below-diagonal savings [L]. | RH-strength subpower readings/half-power cancellation; no fixed Vaughan power saving supplied. Balanced-regime short-window Möbius/prime power saving ⇔ quasi-RH; strip [1/4,3/4] ⇔ Chebyshev Cesàro mean-square energy ≪N^{3/2+ε} [L]: further dictionaries, no producer. | V:UnconditionalEscapedMoebiusDecayAndCrossRouteBridge; V:SingleScaleThetaPrefixTransferAndVKCeiling; RDP:ShortWindowDispersionAtSeventeenThirtieths; R:QuasiRHNormalizedChebyshevCesaroAndMertensActionAbscissaLaw |
| <a id="adr"></a><a id="acp"></a>**Escape / ArithmeticCorrespondencePositivity** | PM, MC, WL, HF, ACS | Residual kernels, compact pole-order/Gram laws and escape classification. Prime-error energy iff RH; genus slope iff RH+simple zeros [L]. | Exterior tightness, positive gauge mass, inverse coercivity or actual energy estimate; compact laws do not exclude infinite-height escape. | CP:CompactReceiverWindowsSelectTheMaximalVisibleOrder; CP:TheAbelSlopeOfThePrimeErrorIsTheArchimedeanGenus; [ADR corpus](../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/) |
| <a id="arithmetic-correlation"></a><a id="ssa"></a>**Gauge averages / successor arithmetic** | MC, PM, HF, ACS, AIP | A.e. square-root cancellation, exact shift floors, escape measures and quantitative charged-cell growth [L/S]. | Select actual μ; obtain matching-profile signed estimates. Typical gauges, relative/twin cancellation and growing cell counts supply no all-test sign. | ACG:AlmostEveryGaugePointCancelsToTheSquareRoot; SSA:TheShiftFloorsAreExact; ACG:SubProgressionStabilizerInversionAndCellHolonomyGrowth |
| <a id="aog"></a><a id="biarithmetic"></a><a id="biarithmetic-gauge"></a><a id="arithmetic-effectivity"></a>**Arithmetic geometry / effectivity** | HF, ACS, WL, MC, AIP | Source/index/rate and degree–torsion dictionaries; RR/effectivity/height/chirality receivers; torsion=ψ, first Fourier=M; finite-curve calibrations, Burgess and least-nonresidue bounds [L/S]. | Actual source positivity/Rosati heights; character estimates do not supply μ cancellation. | J:TheIndexExit; AE:TheEffectivityCalculus; BGG:TheCriticalConservationLaw; BG:ArithmeticEulerCharacteristic |
| <a id="apd"></a><a id="mpg"></a><a id="sbwf"></a>**Positive duality / multiplicative geometry** | HF, ACS | Positive-measure theta/FE rigidity; affine/GNS realization; boundary-capacity and finite-frequency laws [L/S]. Simple-pole completed class identifies ζ [L]. | Source-compatible mixed positivity/interior sign. Rigidity needs its full analytic/moment inputs; source identification is not Weil positivity. | APD:PositiveMeasureHamburgerRigidity; MPG:GrowthToForcing; SB:TheSimplePoleClassIsZeta |
| <a id="renormalized-biarithmetic"></a><a id="arithmetic-intersection"></a><a id="horizon-renormalization"></a>**Renormalization / intersection** | HF, ACS, AIP, MC, OWU | Exact periodic/Ramanujan survival, prime-tower and counterterm laws; collided moment reconstruction [L]. Residue/character finite parts and fixed-field gauge means [S]. | Signed mass-relative/growing-sieve control with full Gamma/poles; local tower bounds cannot be summed as a global ℓ² ceiling. | RBG:TheRenormalizationSurvivalLaw; AIT:TheLocalFormsDoNotSum [L]; RAPT:TheFinitePartOnResidueClasses [S] |
| <a id="artin-mertens"></a>**Artin–Mertens / Hecke foundations** | RAPT; number-field support | Global continuation, Re s≥1 nonvanishing and fixed-field Mertens [L]. For finite-primitive characters, actual dual-class Mellin integrals, absolute class/unit unfolding and radial majorants justify the inverse-character class-series identity for Re s>1, including nonzero parity [K]. For every nontrivial finite-order character, raw completed physical/dual numerators are entire and vanish at 0/1 respectively, before reciprocal-Gamma multiplication [K]. | Divided-difference completion/removable values, finite-class recombination and normalized global functional equation. Field/modulus-uniform bounds and interior zero exclusion remain. | HLF:HeckeLFunctionsHaveGlobalContinuation [L]; HLF:HeckeDualClassKernelsHaveExactMellinIntegrals; HLF:HeckeDualUnitOrbitsUnfoldOverTheLogSpace; HLF:HeckeDualAveragedMellinIsTheInverseClassSeries; HLF:HeckeCompletedThetaResiduesCancel [K] |
| **Lattice Poisson / theta foundations** | Theta families; BAG; Hecke support | Affine Schwartz/parity Gaussian Poisson; actual ideal trace dual, covolume=N(I)√abs(discriminant), reciprocal place scaling, theta inversion and exponential tails. Exact N(I*)=1/(abs(discriminant)N(I)), including zero ideal with totalized inverse [L]. | Normalization tools, not RH-selective sign or completed Hecke functional equation. | H:IntrinsicParityPoisson; H:NumberFieldIdealTraceDuality; H:NumberFieldIdealCovolume; H:NumberFieldScaledIdealTheta; H:NumberFieldTraceDualsHaveDiscriminantNorms [L] |
| <a id="elliptic-base"></a>**Elliptic base fields / pole transfer** | Geometry / effectivity calibration | Actual y²=x³−x over 𝔽₃: genus one, degree-2 zeta numerator, roots modulus1/√3; full Weyl poles retain multiplicity [K], one rotation threshold for both roots [L]. Affine integral closure/Dedekind ring [K]; infinity DVR with uniformizer x/y and residue 𝔽₃ [L]. Actual completions preserve residues; full adeles have compact-open integral product, denominator clearing, σ-compactness and σ-finite additive Haar of integral volume1. Every finite adele differs from an actual rational function by an integral finite adele [K]. Local uniformizer scaling=q⁻¹; inverse dilate volume=qⁿ; shell0 has volume1, shell(n+1) has volume qⁿ⁺¹−qⁿ, and all shells exhaust the field [K]. Ideal quotient cardinality multiplicative in every infinite Dedekind domain [L]. Spherical shell kernel is absolutely integrable with integral (1−z/q)/(1−z) for norm(z)<1 [K]. Actual local factors use finite residue sizes and q=3 at infinity; nonzero affine ideal quotients are finite, with principal norm=3^(pole degree) [K]. | Product formula and full place/curve Euler product; quotient covolume/unipotent measure, Iwasawa-character identification and Eisenstein sum/constant term, then characteristic-zero source/RR bridge. Ambient Haar and Weyl noncancellation do not supply unfolding. | AE:FiniteFieldEllipticIntegralClosure; AE:FiniteFieldEllipticLocalFields; AE:FiniteFieldEllipticAdeleHaar; AE:FiniteFieldEllipticFiniteApproximation [K]; AE:FiniteFieldEllipticInfinityResidue [L]; H:LoopEisenstein/AffineA1FiniteFieldWeylPoles [K/L]; H:DiscreteValuationHaar; H:DiscreteValuationShells [K]; H:DedekindIdealNorm [L]; H:LocalRankOneIntegral; AE:FiniteFieldEllipticLocalIntegrals; AE:FiniteFieldEllipticIdealNorm [K] |
| <a id="loop-foundations"></a>**Affine Weyl / loop-group foundations** | Automorphic foundations | Convergent rotated affine A₁ Weyl sum and Gaussian degree extraction [L]. Tame extension, Borel coordinates, unique Bruhat labels, exact simple SL₂ lifts, vertex generation and real Iwasawa factorization G=BK [K]. Reduced alternating simple words avoid B; arbitrary join-word reduction gives full K∩B=M, the central/coroot sign torus. Intrinsic χ is trivial on M; Φ(bgk)=χ(b)Φ(g), Φ(1)=1 and Φ≠0, independent of Iwasawa factors [S]. | Dependency-closed audit/integration of word reduction, intersection and spherical function; determinant-metric compatibility, finite root-coordinate Bruhat refinement, arithmetic quotient/measures, coset-sum convergence and constant-term identification. Algebraic factorization supplies no RH sign. | H:LoopEisenstein/AffineA1WeylSum [L]; H:LoopEisenstein/LoopBruhatDecomposition; H:LoopEisenstein/SimpleRankOneEmbeddings; H:LoopEisenstein/VertexGeneration; H:LoopEisenstein/RealIwasawaExistence [K]; H:LoopEisenstein/CompactBorelIntersection; H:LoopEisenstein/RealBorelCharacters; H:LoopEisenstein/RealSphericalFunction [S] |
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
| TM | TransMetzlerWeilPositivity | — | — |

## Alias lookup

BVI→[support](#bvi); C1→RW; CCM-FU→FU; CLG/TTF,K-RVM,S6F,TCD,UEB→TH; CSB,STC,U,MPLF,RHist,BPC,TQFQ,WS2,SQB→RN; D2,Q,RG,RG-ETA,TK→PA; E,EDQ,L,HDL,PSRC→MC; FZZ-P→PM; PW-B→[candidate](#pw-b); G,HC→WD; O→WL/RW (genus mechanism dead); P,SP-E→RP; SV2,RG-HF→SZ; T1,T2,Route T→TT; Route T successor/ULF sub-unit anchor→TG; Deninger→HF. [Retired labels](rh-killed-routes.md#retired-labels).
