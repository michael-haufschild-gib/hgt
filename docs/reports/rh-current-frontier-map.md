# RH proof-route frontier

**Status:** RH open. **31 live routes; 17 standalone candidates; PW-B candidate sub-branch.**
**Corpus checkpoint:** `6046e5478f649abd5cbcb104efc4472e3bf43ec3` — committed corpus coverage; working-tree additions and unintegrated/unfinished source marked [S].

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
| Full Weil floor ≥‖f‖₂²/5000 and odd floor ≥‖f‖₂²/1000 through radius 181/500; smooth primitive floor ≥‖f‖₂²/1000 through (log2+1/50)/2. | All apertures with complete prime/Gamma/polar terms. At 181/500 only atom 2 is read; every weight with w(2)=log2 shares the full floor. |
| Full/even/odd H¹ floors with VK saving; full/odd H¹ floor rate sets and critical-deficit energy rate sets are [zero width,∞), endpoint attained. | Arithmetic rate zero. Existing savings retain positive leading exponential growth. |
| RH ⇔ width zero ⇔ full/even/odd Hodge defect zero ⇔ cofinal damped-μ admission ⇔ vanishing Báez–Duarte residual ⇔ positive gauge mass for every actual subcritical cofactor limit. | Produce any one sufficient source estimate; equivalences alone close none. |
| Physical L² full and polar rates agree; form-norm/Birman–Schwinger infimal rates equal width. | Physical L² equality with positive width and form-norm endpoint attainment remain open. Do not exchange norms. |
| Fixed-aperture completion/sign transfer; collided-form equivalence to ∫‖f̂(σ)‖²log(‖σ‖+4)dσ at every fixed aperture; signed Weil Gårding bound and finite negative index. | Coercivity is for the positive collided form, not W. Finite negative index need not be zero. No uniform positive ground-energy gap at unbounded aperture. |
| Source RR, maximal positive blind ideals, boundary/collar forcing and simple-pole source rigidity. | Full-source sign/exhaustion and nonreal interior zero exclusion. Restricted positivity and source identification are not RH. |
| Re W=collided mass−off-line defect; RH iff W equals the collided form iff collided-form translation invariance. The collided form and its Hecke defect are computed by the Laplacian of log‖ξ‖ and by finite theta prefixes, without zero indexing. Section count with RR+Bézout, effectivity, integral Rosati heights and the one-sided ψ count are RH-equivalent. | Arithmetic construction of a form both positive and translation-equivariant, e.g. an upper bound forcing the computed Hecke defect to zero. Equivalences and computations supply no sign; positive kernel counts need not supply Rosati heights; subtracting ψ from the polar box destroys RI. |
| Electrostatic forms: RH iff every right-zero transverse field≤1 iff (explicit c>0) every right-zero field<√(2c log(\|γ\|+4)) iff distinct-zero transverse energy ℰ<1 iff every unit window has energy<2; ℰ<∞ iff finitely many off-line zeros. Hecke defect ≍ moment of inertia: 4L²M_f≤E_f(L)≤8(cosh L−1)M_f, M_f=Σmδ²\|f̂(ρ)\|². For σ>1 a zero β+iγ of multiplicity m forces ΣΛ(n)n^(−σ)cos(γlog n)≤Re(arch′/arch)−m/(σ−β). | Per-distinct-zero energy≤16(C+log(\|γ\|+4)); window energy≤16·#window·(C+log(\|T\|+H+4)) [L]. Need field, energy or M_f below the off-line quantum, not logarithmic growth. The σ>1 prime-field ceiling has no inside-strip continuation; detection and quantization supply no bound. |
| Torsion renormalization: identity counterterm, survival cone {0}, κ_min≍log N with divergence at the arithmetic point, fixed-radius Hecke cocycle not a bounded coboundary [L/S]. Spacing radii remove log t drift but retain tame ramification and an indefinite finite part [L]. Archimedean lattice germ PSD on Σc_i=0; pole completion PSD, with full-rank divergence regenerated at infinite node height [L]. Weil's prime kernel=Σ_p log p·(K_(p^−1/2)−I) over p-fibres, each two-sided bounded; no global ℓ² ceiling [L]; on orders≤N, prime form≤(2log N+log4+4)Σx_n² [L], sharpened to (log N+log4+4)Σx_n² with matching log N−log8−4 lower ceiling [S]. | Source-faithful coupled prime/Gamma/pole sign. Keeping the Abel torsion block forces counterterm rank≥number of orders and prime-survival dimension≤partner rank [S]; periodic constant-mode coupling preserves only the arithmetic point, not orders≥2. Change the prime block/regulator or supply growing partner rank and control the finite part. |

**Sources:** D:ThreeTenthsSharpGaugeWeilPositivity; I:SchurLendingOddWindowThreeHundredSixtyTwoThousandths; G:AllParityCriticalDeficitAndEndpointSobolevLaws; O:TheWidthDictionary; C:UnconditionalBirmanSchwingerRateReadsTheZeroWidth; PL:TheOscillatoryCapacity; PL:HeckeInvarianceOfTheCollidedPolarizationIsRH; CP:ASectionCountIsTheSign; AE:NaiveHeightsAreTraces; AE:ThePolarBoxCount; CP:TheStepanovCountIsTheSign; PL:TheCollidedFormIsTheLogarithmicSobolevNorm; PL:WeilsFormHasFinitelyManyNegativeDirectionsAtEveryAperture; CDG:XiSourceCurrent; SP:LiouvilleOddWindowRefutationAndSelectiveFullPositivity; AES:TheFieldLawHasAThreshold; AES:TheTransverseEnergyOfTheZeroDivisor; AES:QuantizationTurnsWindowsIntoPoints; AES:TheHeckeDefectIsTheMomentOfInertia; AES:TheExternalFieldIsAPrimeSum; AES:TheTorsionCountertermIsLogarithmic; AIT:TheHeckeCocycleOfRenormalization; RBG:TheArchimedeanGermSurvivesOnItsPolarHyperplane [L]; AIT:TheLocalFormsDoNotSum; AIT:TheSpacingRegulatorRemovesTheAnomaly [L]; RBG:TheCountertermRankDichotomy; RAPT:TheCoupledSurvivalLaw [S].

## Live routes

<a id="wl"></a>
### WL — Weil lag function

- **Path:** Actual prime lag/deficit → one-sided bound or subexponential critical energy → RH.
- **Proved [L]:** Critical energy bounded ⇔ coprime cross-work bounded below ⇔ cumulative energy O(T) ⇔ RH; width-rate endpoints and O(1) high-zero tail. Eventual ψ(x)−x≤C√x(log x)² iff RH; horizon torsion=ψ(N), first Fourier=M(N). Linear prime-error log-energy budget iff RH. All-c damped integrability plus Abel slope→C₀=2+γ_E−log(4π) iff RH with simple critical zeros. Archimedean remainder uniformly L²-bounded for 0<c≤1/4; under RH, high-zero Abel tails vanish uniformly; simplicity gives genus saturation. Successor shift preserves finite critical residue costs.
- **Open:** Prove actual adverse-correlation/linear prime-error energy bound without RH; genus saturation is the stronger RH+simple-zeros target. Conditional tail exhaustion and the converse close the analytic equivalence, not its arithmetic input.
- **Sources:** B:WeilLagCriticalDeficitEndpointAndLimitLaw; B:HighZerosCarryABoundedCriticalDeficit; CP:TheStepanovCountIsTheSign; AE:TheHorizonTorsion; CP:ThePrimeErrorBudgetDominatesTheArchimedeanGenus; CP:TheAbelSlopeOfThePrimeErrorIsTheArchimedeanGenus; CP:ThePrimeErrorSymbolSplitsAtTheZeros; CP:TheZeroPartHasNoMassAtInfiniteHeight; CP:TheSuccessorDefectIsABoundedHardyPerturbation.

<a id="rw"></a>
### RW — Restricted Weil ground energy

- **Path:** Complete prime−Gamma−polar form → ground minimum μ(A)≥0 at every aperture → RH.
- **Proved [L]:** Completed-domain receivers, shell flux and prime-shell decomposition. μ strictly decreases; RH iff every finite-aperture μ>0, equivalently cumulative frozen-flow relaxation≤initial energy on the threshold ladder. Signed Gårding bound gives finite negative index at every fixed aperture, not index zero. Full ground-energy floor≥1/5000 through radius 181/500. Norm-specific rates: shared frontier.
- **Open:** Source-derived relative-step or cumulative-relaxation bound paying collars, low modes and complete polar energy. Telescoping supplies no bound; permanently frozen prime families eventually become negative.
- **Sources:** C:TheApertureFlowNeverStalls; C:ThePrimeShellBetaFunction; C:ThresholdVanishingAndCollarDominanceOfThePrimeShell; C:UnconditionalEqualityOfPolarAndFullGroundEnergyRates; PL:WeilsFormHasFinitelyManyNegativeDirectionsAtEveryAperture; SP:LiouvilleOddWindowRefutationAndSelectiveFullPositivity [L].

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
- **Proved [L]:** Exact receivers, fixed-modulus/window cancellation and below-diagonal savings; diagonal norms do not pay the remainder. For odd prime p and r≥2, quadratic-character interval sums obey K_r N^(1−1/r)p^((r+1)/(4r²))(1+log p); least nonresidue≤p^(1/(4√e)+ε) for sufficiently large p. Torsion Fourier=M(N); every-strict-half-power bound iff RH; M=o(√x) false. Linear Mertens energy forces RH, simple zeros and summable inverse-derivative residue squares. Finite-curve budget iff purity+simple spectrum with exact slope. Escaped-boundary growing-endpoint and dyadic rate laws ⇔ zero abscissa Θ≤1−θ, 0<θ≤1/2. Uniform escaped-μ vanishing with bound Ce^(−κσ(M)/48), M=(N−b)/a→∞, and receiver/prime-band equivalences [L]; this VK rate supplies no fixed power saving. For 0<θ≤1/2, Θ≤1−θ is also equivalent to the exact all-test Hecke-defect strip cap, dyadic growth at rate 1−2θ and Re ξ′/ξ≥0 throughout Re s>1−θ [L]. Along n_k=⌊exp(2^k/2)⌋+1, the same strip condition iff every compact-test integer-theta reading is O_ε((n_k+1)^(2(1−2θ)+ε)); RH iff every positive power suffices [S].
- **Open:** Actual moving-scale μ cancellation at every strict half-power, or cofinal subpower energy. The stronger linear log-energy budget is not produced. Uniform decay in N over all multipliers is impossible; uniform decay in the escaped endpoint M survives, but the half-power rate remains open. Typical-phase or relative twin cancellation does not select actual μ.
- **Sources:** R:MobiusHilbertFormEquivalence; T:OscillatingProbeSourceEstimatesEnergyGapAndCollarLimitations; V:TheDualNormIsMinorArcBelowTheDiagonal; V:TheDiagonalDualNormIsArchimedean; CP:TheMertensBudgetForcesASimpleCriticalSpectrum; CP:AMertensBudgetIsPurityWithASimpleSpectrum; AE:TheBurgessBound; AE:TheLeastQuadraticNonresidue; SP:MoebiusEscapedPairingBoundaryLaw [L]; V:SingleScaleThetaPrefixTransferAndVKCeiling [S]; V:UnconditionalEscapedMoebiusDecayAndCrossRouteBridge [L]; [BVI](#bvi), [correlation support](#arithmetic-correlation).

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

- **Path:** Full source positivity, defect D<2, collided-form Hecke invariance, right-zero field≤1 or every unit-window full-row energy<2 → RH; dyadic defect zero-rate receiver [L].
- **Proved [L]:** Source/divisor surfaces agree; distinct-right-zero defect D even when finite, RH iff D<2. Effectivity/height receivers; Re W=collided mass−off-line defect; RH iff collided translation invariance iff one-shift similitude. Fixed-aperture collided form≍log-weighted Fourier energy; polynomial theta reconstruction. All-zero Laurent source-field identity retains multiplicities/exterior rows. RH iff every right-zero field≤1 iff (explicit c>0) every right-zero field<√(2c log(\|γ\|+4)) iff distinct-point ℰ<1; ℰ finite iff finite off-line support. Compact arithmetic work exhausts full multiplicity-copy energy, including ∞. For each distinct zero, E(ρ)≤16(C+log(\|γ\|+4)); off-line E(ρ)≥1. Window energy≤16·#window·(C+log(\|T\|+H+4)). Window full-row energy≥off-line count; RH iff every unit window has energy<2. For compact f, M_f=Σm_ρ(Reρ−1/2)²|f̂(ρ)|² satisfies 4L²M_f≤E_f(L)≤8(cosh L−1)M_f and E_f(L)/L²→4M_f. For σ>1, prime cosine field at ordinate γ≤archimedean field−m/(σ−β) for each zero β+iγ of multiplicity m. Dyadic growth E_f(2^kL)=O_ε(exp((2φ+ε)2^kL)), φ,L≥0, forces exact cap E_f(L)≤D(f)(2cosh(2φL)−2). For 0<θ≤1/2, all-test cap at φ=1/2−θ ⇔ Θ≤1−θ ⇔ Re ξ′/ξ≥0 on Re s>1−θ [L]. For a≥0, all zero depths≤a iff every right terminal has depth≤a; RH iff no right terminal. For φ≥0, all-test/all-scale Hecke cap E_f(L)≤D(f)(2cosh(2φL)−2) iff all zero depths≤φ [S]. Explicit all-n theta-prefix errors transfer to defect and transverse moment; VK gives readings=o(n²) throughout |L|≤2log(n+1), while RH requires subpolynomial readings on the canonical dyadic schedule [S]; [prefix bounds](#bvi).
- **Open:** Actual full sign/D<2, bounded-error Rosati-height lower bound, M_f=0 for every test, dyadic defect zero-rate, or arithmetic upper field/work/window bound below the off-line quantum. Exterior σ>1 control supplies no inside-strip bound. Relate multiplicity-copy energy to distinct-point ℰ. The theta-prefix VK upper bound is not subpolynomial; the force-zero + finite-energy receiver supplies neither required input. Terminal-lens Harnack transports the outward lower floor to discs [S], not an arithmetic upper bound. Prime-detector power-saving counts [L] still permit exceptional zeros; finite Rosati moments [L] supply no off-line sign. Periodic Ramanujan/constant-mode coupling preserves exactly the arithmetic-point direction, no order≥2; horizon prime divergence survives every fixed number of linear constraints [S]; [scope](#renormalized-potential).
- **Sources:** J:TheIndexExit; AE:NaiveHeightsAreTraces; PL:HeckeInvarianceOfTheCollidedPolarizationIsRH; PL:TheCollidedFormIsTheLogarithmicSobolevNorm; CP:EveryXiZeroHasASourceField; AES:TheFieldLawHasAThreshold; AES:TheTransverseEnergyOfTheZeroDivisor; AES:TheSelbergWorkExhaustsTheTransverseEnergy; AES:QuantizationTurnsWindowsIntoPoints; AES:TheHeckeDefectIsTheMomentOfInertia; AES:TheExternalFieldIsAPrimeSum [L]; RBG:TheDyadicAmplificationOfTheHeckeDefect; V:UnconditionalEscapedMoebiusDecayAndCrossRouteBridge [L]; AIT:ZeroMomentsAreRosatiPairings [L]; AES:TheEnergyOfAZeroIsLogarithmic; AES:LargeValuesAtZeroOrdinates [L]; AES:HigherMomentsAtZeroOrdinates [L]; RBG:HarnackOnTheCaratheodoryRegion; RBG:TheTerminalCeilingAndTheOneScaleBoundAreZeroFreeStrips; RBG:TheHeckeMomentProblem; RBG:IntegerThetaPrefixesReadTheDefectWithoutLoss; V:SingleScaleThetaPrefixTransferAndVKCeiling [S]; [theta reconstruction](#conjugate-diagonal), [electrostatics](#outward-field), [renormalization](#renormalized-biarithmetic), [ACS](#acs).

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
- **Proved [L]:** Weight rigidity; attained aperture-antitone minima with exact RH criterion. Full positivity for sufficiently high dyadic/polynomial windows and separated lacunary unions; dense-window estimates retain high-energy dominance. Full/even compact C² floor≥‖f‖₂²/5000 through radius 181/500; this local floor also holds for every weight with w(2)=log2.
- **Open:** All-aperture minimum≥0, or full-positive weights at every finite aperture. Pay low/mixed modes on an RH-complete cone; restricted-family positivity does not pass through arbitrary tent approximation or polar-nonclosed limits.
- **Sources:** R:EvenSectorPoleWeightUniqueness; R:EvenSectorBlindVariationalAttainment; A:DenseScaleWindowsAndMultiWindowPositivity; A:FromTheCriticalFamilyToTheReceiver; A:SourceSelectionInTheFullWeilCone; SP:LiouvilleOddWindowRefutationAndSelectiveFullPositivity [L]; [L² cycle recovery](#closed-cycle-tools).

<a id="gta"></a>
### GTA — Transverse Schur charge

- **Path:** Actual theta-stage positive quartic Schur charge → rank-uniform transverse decay → RH.
- **Proved [L]:** Exact late-stage decay criterion; strong finite-truncation convergence, positive charge and compact/ideal diagnostics.
- **Open:** Rank-uniform arithmetic transverse-energy decay independent of zero data. Strong finite-prefix convergence is insufficient.
- **Sources:** R:Hedenmalm/HedenmalmThetaSchurQuarticSpectralDecayEquivalence; R:PaperThetaSchurModeCharge; R:PaperThetaSchurCompactGap.

<a id="owu"></a>
### OWU — Odd Weil-weight uniqueness

- **Path:** Actual-Λ odd positivity, or odd-positive weight plus all-scale dilation-ray sign → RH.
- **Proved [L]:** Odd/polar-hyperplane criteria, local floors and twisted full EF transport. At radius 181/500, edge mass≤‖F‖₂²/1961 implies Liouville-twin positivity; any negative witness must exceed it. First-prime twist comparison retains Gamma/pole corrections; multi-prime repulsion prevents exact vacuum alignment. Smooth odd radius-181/500 witnesses separate actual Λ positively from both its Liouville twin and the single-atom-2 sign flip negatively. At radius 23/40, where atoms 2 and 3 are read and the {2,3} flip is not a height twist, one smooth odd witness has W_Λ>‖F‖₂²/25 and W_λ<−(3/10)‖F‖₂². For even complex g supported in [−η,η], η≤181/500−log2/2, Re W(g−T_log2g)≥‖g−T_log2g‖₂²/1000 [L]; midpoint centering swaps parity, with no cross-term. Support inclusion preserves this witness at every larger aperture; at radius 2log2 the exact Λ/Liouville difference has seven signed autocorrelation terms, squares 4,9 cancel [L].
- **Open:** All-aperture actual-Λ odd sign or full reflected-prime/polar payment. Companion-forcing certificate and conductor horizon have no common aperture for 0≤δ≤1/2; need stronger signed estimates or a different detector, then companion-cluster exclusion. The persistent witness and exact collar difference do not prove every-test positivity or pay signed autocorrelations. Zero-ordinate second moments [L] and prime-detector power-saving counts [L] leave exceptional zeros and signed reflected correlations uncontrolled; [scope](#analytic-large-values).
- **Sources:** B:OddSectorPolarHyperplaneAndPoleWeightSynthesis; R:WeilMarkovOddPositivity; R:WeilDilationRayCriterion; R:OddSectorBlindVariationalAttainment; CP:TheFirstGaugeChargedWindowOffTheEdge; BGG:MultiPrimeDiophantineRepulsion; CDG:TheConductorForcingGap; SP:LiouvilleOddWindowRefutationAndSelectiveFullPositivity [L]; SP:TwoPrimeCatalanSeparationAndContinuumTowerObstruction; I:NineModulusCollarSelectivityAndPolarLedger [L]; P:RamanujanParityTwinLimitsAndShortCycleObstruction [L]; [prime-form scope](#arithmetic-intersection).

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
- **Proved [L]:** Every-width receiver, exact rates, orbit/index laws and polynomial-aperture detection. One prime/all short tests or one shift/unrestricted supports suffices. Twisted sinh detector is σγ-odd; sign+local-count+depth dominance forces a companion. Conductor-horizon positivity requires C+(4+ε)e^a+2≤log(1+|γ|/8) and both derivative-tail bounds. Prime-symbol recurrence forbids uniform eventual power savings, not full Weil positivity. Zero-ordinate second moments [L] and prime-detector higher moments give power-saving alignment counts in an explicit threshold regime [L]; exceptional ordinates remain. At lag log2, even complex profiles of radius≤181/500−log2/2 have Re W(g−T_log2g)≥‖g−T_log2g‖₂²/1000 [L]; no all-profile or late-lag sign.
- **Open:** Actual-Λ late-lag lower bound at every positive exponential slack, zero-rate orbit bound or sufficient horizon containment. Pay cross-window correlation at unbounded separation. Existing companion forcing requires e^(2δa)>768A log(|γ|+3), incompatible with the conductor horizon for 0≤δ≤1/2, A≥1. Need improved signal/cost or independent full detector sign, not this splice.
- **Sources:** S:EveryWidthDecidesTheCriticalLine; S:ZetaLagFamilyVinogradovKorobovEnvelope; S:SmoothWeilDetectorPolynomialAperture; G:OneSidedLefschetzBoundsAtOnePrimeAreTheStrip; PL:TheForcingHalfOfEllipticLocalization; PL:ThePriceOfEllipticLocalization; A:SingleHeightPhaseSelectiveApertureAndPowerSaving; CDG:TheConductorForcingGap; AES:LargeValuesAtZeroOrdinates [L]; AES:HigherMomentsAtZeroOrdinates [L]; P:RamanujanParityTwinLimitsAndShortCycleObstruction [L].

<a id="act"></a>
### ACT — Arithmetic criticality / single-shift variation

- **Path:** One fixed theta shift a>0 → D_a(u)≤2S_a(u)+V_a(u) for every even compact C² profile → odd Weil positivity → RH.
- **Proved [L]:** Exact ground-state variation/receiver; continuum light-cone positivity; fixed-support subunit reflected-prime collar paid at sufficiently large shift. Small-window floors and signed-moment identities.
- **Open:** One fixed a paying every support/profile, including exterior primes and signed/polar remainder. Support-dependent absorption does not give this uniform inequality.
- **Sources:** D:ShortProfilePoleFreeVariationInequality; D:SignChangingTwoMomentAndAtomPoleIntegralLaw; D:RestrictedWeilGroundEnergyCriticalAtInfinity.

<a id="aip"></a>
### AIP — Arithmetic incidence positivity

- **Path:** Actual prime incidence + plateau gauge → all-aperture GlobalIncidenceAllocation → odd positivity ↔ RH.
- **Proved [L]:** Full incidence identity; allocation iff RH; shared-resource laws, lattice Schur reduction and odd floor through 181/500. Finite gauge conjugacy/successor selection; log-cell remainder controlled by weighted coefficient variation. Full-form radius-181/500 Λ/Liouville and atom-2 separation rules out complete-form gauge conjugacy. Raw prime towers admit energy≤−c e^A, excluding sub-half H¹ floors. Dyadic log-cell covariance on profiles supported in [1,X], X≥4, iff ω(p)=1 for every prime p≤2X+1; global covariance fixes Euler gauge, unlike lattice dilation. Square-class source-form positivity is invariant under real sign gauges [S]; actual finite prime kernels satisfy P^ε(m,n)=ε(m)ε(n)P(m,n), preserving ℓ² mass and unboundedness [L]. For every real sign gauge flipping 2, 162(K+1)^4≤X implies ≥K charged cells and scalar-uniform cell defect≥2K [L]; no formalized positive-density bound and no Weil-sign transfer (for Liouville, logarithmic density 1/2 of λ(a)=λ(2a+1) is Tao's two-point logarithmic Chowla theorem, not formalized). At radius 2log2, prime support is {2,3,4,5,7,8,9,11,13}; W_λ−W_Λ=4Σ_(n∈{2,3,5,7,8,11,13})Λ(n)n^(−1/2)autoCorr_F(log n), squares 4,9 cancel. Catalan 8·9 separates real scale twists from Liouville; ratio-comb floor retains signed remainder/pole debt [L]. At explicit atomic width every real sign twin has M=arch−prime≥0. Below atom spacing, nonnegative weights give M_ω≥M; on the two-atom {1,p} test at ω(p)=−1, M_ω−M=(2log p/√p)‖f‖₂² for every N≥p [L]. On the same atomic tests (width≤atomicWidth N), the full ζ Weil form obeys Re W+2S²≥0 and Re W≥0 on |S|≤|C|, C/S the cosh/sinh moments [S]; [scope](#atomic-stability).
- **Open:** Joint full-continuum prime/Gamma/pole payment with signed remainder. Raw-tower no-go does not apply to the pole-neutralized full odd form. Finite prime-form tower decomposition and logarithmic finite-order upper bound [L] supply no global ℓ² ceiling [L]. Narrow log-atom tests identify the full prime functional with ‖φ‖₂²Σ_pQ_p [L]; Gamma/pole domination is only proved assuming RH. The explicit log-atom pole pairing [L] vanishes on Σx_n/√n=0; its Gamma-only domination still assumes RH. Atomic stability is gauge-blind; its positive-weight margin makes ζ the minimum, not a selected positive winner. Cone positivity has no odd/reflected or full-test transfer. Logarithmic self-energy lower bound and signed archimedean decomposition [L] retain inter-atom debt; tower domination still assumes RH. Horizon polar subtraction controls an absolute coefficient norm; raw prime divergence survives any fixed number of linear constraints [S]. Off-diagonal terms cancel the apparent linear diagonal reserve; no reserve reuse. Gauge selection and the nine-modulus comb bound supply no nonnegative full budget or all-aperture sign.
- **Sources:** I:GlobalIncidenceAllocationCondition; I:GlobalSharedSurplusAllocation; M:TheCompensatedRemainderOfTheFullLedger; BGG:EuclideanCellRemainderAndPolarNeutralCollapse; SP:TwoPrimeCatalanSeparationAndContinuumTowerObstruction; SP:LiouvilleOddWindowRefutationAndSelectiveFullPositivity; RBG:LogCellsFixTheGauge [L]; RBG:TheGaugeChargeOfACoupling [S]; I:NineModulusCollarSelectivityAndPolarLedger; AIT:TheFiniteIntersectionIsGaugeBlind; AES:TheWeilPrimeFormOnAtomsIsLogarithmic [L]; AIT:WeilsPrimeFunctionalIsTheFiniteIntersection [L]; RBG:TheCellHolonomyDefectCountsChargedCells [L]; RBG:TheSelectivityBatteryOfRenormalizedBiarithmeticGeometry [S]; AIT:ThePolarPartPairsThePoleDirection; AES:TheStabilityLawAtAtomicResolution; AES:TheGaugeIsInvisibleAtAtomicResolution [L]; AES:TheWeilFormAtAtomicResolution [S]; ACG:SubProgressionStabilizerInversionAndCellHolonomyGrowth [L]; AIT:TheHodgeIndexInTowerCoordinates [L]; [RAPT](#renormalized-potential).

<a id="acs"></a>
### ACS — Arithmetic Castelnuovo–Severi effectivity

- **Path:** Arithmetic effectivity/bounded-error Rosati heights → Hodge → RH; equivalently all-ordinate positive-deformation chirality or rational/positive central-vanishing ceilings.
- **Proved [L]:** Source RR, restricted Meyer RR+Bézout and effectivity/Tate/height receivers; faithful degree needs RH+simple zeros. All-nonzero-ordinate chirality and rational/positive central ceilings each iff RH. Positive prime-mass rigidity at γ iff no ξ zero has ordinate γ; full two-sided rigidity unproved at zero-free ordinates, false at zero ordinates. Horizontal exclusion plus no central drop gives zero-residue rigidity; horizontal exclusion also yields even surplus-residue quantization and finite-divisor cosine conservation. Central excess forces deficit Abel liminf≥excess; ζ^d sub-half-deficit rigidity with κ≤d needs no horizontal exclusion. Selberg source Λ₂=Λlog+Λ∗Λ≥0, LΛ₂=ζ″/ζ on Re s>1; order-m self-term m²→m(m−1), residue 2mR unchanged [L]. For real completely multiplicative ω, twisting gives Λ₂^ω=ωΛ₂; nonnegative twisted source forces ω(p)=1 at each prime with sign phase [L]. At a flipped prime p, source gap=2log²p; real σ>1 series gap≥2log²p·p^(−σ) [L], not a signed-test form margin. Torsion adjunction, finite Abel limits and exact Hecke-renormalization cocycle [L]; no bounded diagonal potential cancels it globally. For distinct positive orders, I(n,m)=log|𝓞_{ℚ(ζ_n)}/(Φ_m(ζ_n))|; in particular I(n,1)=Λ(n), n≥2; I(p^k,p^k)=log\|disc ℚ(ζ_(p^k))\| for primes p, k≥1. Power maps transport the regulator; rotations preserve it exactly and diagonalize torsion point energies into nonnegative lattice-germ modes [L]. Rotation frequencies are rational circle modes, not ζ-zero ordinates. Spacing renormalization removes log t drift, retains tame ramification, and has a negative {1,2} direction [L]. [Scope](#arithmetic-intersection).
- **Open:** Actual arithmetic h⁰ with quadratic RI+degree-zero subquadratic growth, bounded-error Rosati heights, or all-ordinate chirality/central ceiling. Conservation/quantization retain horizontal exclusion. Positive-deformation composition/irreversibility [S] does not prove actual all-ordinate chirality. Factor-ceiling transfer assumes the ceiling; positive Selberg coefficients construct neither a completed Rankin–Selberg member nor an upper bound on continued residues. Periodic Ramanujan/constant-mode coupling preserves only the arithmetic point [S]. Completed twin kernels recover prime intersections at infinite node height but regenerate a full-rank logarithmic counterterm with zero survival cone [L]. Raw horizon divergence survives every fixed-rank subtraction [S]; neither full Gamma/pole sign nor a uniform bound over growing frequency clouds follows.
- **Sources:** G:ExactArithmeticSourceEffectivity; AE:TheEffectivityCalculus; AE:NaiveHeightsAreTraces; BGG:PositiveCoupledRigidityAndTheCriticalTransferLaw; BGG:StrongMultiplicityOneBelowTheSquareRootDeficit; BGG:TheDeficitResidueBoundsTheCentralExcess; BGG:TheCriticalConservationLaw; BGG:TheQuantizationOfTheSquareRootSurplus; BGG:TheCentralCeilingTransfersToFactors; BGG:StrongMultiplicityOneForPowersOfZeta; AES:TheRenormalizedSquareIsSelbergsSource [L]; AES:QuantizationTurnsWindowsIntoPoints [L]; [electrostatics](#outward-field), [intersection](#arithmetic-intersection), [RAPT](#renormalized-potential), [BGG](#biarithmetic-gauge); RBG:PositivityIsIrreversible [S]; AES:TheGaugeMarginOfTheRenormalizedSource [L].

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
| <a id="bvi"></a>**BVI — Bézout–valuation incidence** [L/S] | MC, HF, PM, CTF | Λ/pronic readout; fixed-modulus/below-diagonal cancellation; uniform escaped-μ VK decay. For 0<θ≤1/2, escaped θ-rate ⇔ receiver rate≤1/2−θ ⇔ Θ≤1−θ ⇔ all-test Hecke strip cap ⇔ dyadic defect rate 1−2θ ⇔ Re ξ′/ξ≥0 on Re s>1−θ. Single-test asymptotic dyadic rate gives the exact finite-scale cap without constant/slack loss. Integer-theta readings ℛ_f(L,n): explicit all-n error \|ℛ_f−E_f\|≤ε_f(n)→0 for \|L\|≤2log(n+1); 4L²M_f≤ℛ_f+ε_f. With n_k=⌊exp(2^k/2)⌋+1, Θ≤1−θ iff ∀f,ε>0, ℛ_f(2^k,n_k)=O_f,ε((n_k+1)^(2(1−2θ)+ε)). VK ceiling ℛ_f≤D(f)(n+1)²exp(−4δ_n log(n+1))+o_f(1), δ_n=min(η₁,δ_VK(n+2)), gives ℛ_f=o(n²) throughout the horizon [S]. Missing: RH-strength subpolynomial readings; VK gives no fixed power saving. | V:TheBalancedStatisticIsTheQuasiRiemannHypothesis; V:TheMoebiusTailStatisticAtLargeModuli; V:TheMeanValueIsTheLeadingCoefficientOfTheReceiver; V:UnconditionalEscapedMoebiusDecayAndCrossRouteBridge [L]; V:SingleScaleThetaPrefixTransferAndVKCeiling [S] |
| **ArithmeticCompensationTheory (ACCC)** [L] | AIP, MC, RW, ACT, PM, CTF | Compensated identities/rate dictionaries. Prime-packet dispersion: primes p≤Q₀, Q₀≥2, window K, V=Σa_p²‖C(p)‖₂²: \|Σpacket²−KV\|≤Q₀(Q₀−1)V; log-free bilinear Gram remainder, no cardinality loss. For p≥67, K>Q₀(Q₀−1), nonzero packets cannot cancel in mean square. Fixed finite prime sets admit simultaneous omitted-class bias cancellation, preserving the 17/30 short-window transfer. Growing packets/complete source energy remain uncontrolled. | M:TheCompensatedRemainderOfTheFullLedger; O:TheWidthDictionary; M:MultiModulusKloostermanDispersionAndPrimeRowTransfer |
| **SignedArithmeticEnergyIncidence (SAEI)** [L] | AIP, MC, PM, CTF | Graph/frustration, packed-path payment and receiver coordinates. Local PSD/payment does not prove full continuum sign. | SAEI:FrustrationIsPaidAlongCanonicalPaths; SAEI:CycleHolonomyDecidesBalance |
| **SignChangingScrewGauge (SCG)** [L] | AIP, ACT | Signed gauges, folded potentials and moment cancellation; middle-region/remainder sign open. | D:SignChangingTwoMomentAndAtomPoleIntegralLaw |
| **ArithmeticOrientationTheory** [L] | HF, ACS, AIP, PM, MC | Section/rate dictionaries and paid-quotient diagnostics; no independent orientation or index ceiling. | O:TheEffectivityConeFromSections; O:TheWidthDictionary |
| <a id="aog"></a>**ArithmeticOrientationGeometry (AOG)** [L] | HF, ACS, WD, SRT, PM | Source/configuration equality, orbit/index/rate laws, theta h⁰ and finite-Euler invariance; source sign open. | J:TheScalingDatumOfAConfiguration; J:TheOrientationOfACycle; J:TheIndexExit |
| <a id="adr"></a>**ArithmeticDefectRigidity (ADR)** [L] | PM, MC | ζ/η symbols, exact residual kernel, bounded-energy Mellin holomorphy and translated-zero escape classifications in their stated finite-rank/nonresonant classes. Actual escape completeness and inverse coercivity open. | [corpus](../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/) |
| <a id="biarithmetic"></a>**BiarithmeticGeometry** [L/S] | WL, HF, ACS, AIP, PM, MC | Degree-minus-log-torsion identity, affine/source-domain calibration and exact escaped-boundary accounting. Finite affine rigidity and normalization freedom do not produce arithmetic sign. | BG:ArithmeticEulerCharacteristic; BG:HorizonBoundaryCalculus; BG:SharedBudgetDescent |
| <a id="biarithmetic-gauge"></a>**BiarithmeticGaugeGeometry (BGG)** [L] | AIP, OWU, ACS, HF | Abel–Gram divisor jumps; boundary law d≤κ, 2Σ_(t∈Z)ord_(1+it)Λ≤κ−d for finite Z⊂(0,∞), under zero-residue deficit. Under horizontal exclusion: finite critical jumps r satisfy r(0)+2Σr(t)cos(θt)≥0; zero-residue half-power deficit gives surplus Abel limit D∈2ℕ, D≤2ord_(1/2+iγ)ξ. Full-class central ceiling transfers to entire cofactors of (2ξ)^k; neither ceiling nor automorphic realization constructed. | BGG:TheAbelGramLawOfPositiveDeformations; BGG:TheBoundaryCapacityOfDeformationsOfPowersOfZeta; BGG:TheCriticalConservationLaw; BGG:TheQuantizationOfTheSquareRootSurplus; BGG:TheCentralCeilingTransfersToFactors |
| <a id="mpg"></a>**MPG — Multiplicative positivity geometry** [L/S] | ACS | Boundary capacity/profile realization; integer-family classifications; sharp finite-cosine limits [L]. Nonnegative packet on ℚ-independent frequencies has Σ\|a_j\|≤a₀. For ω_j=Σ_i n_ji g_i, ℚ-independent g_i, n_ji∈ℕ and 1≤Σ_i n_ji≤M, signed Σa_j≤Ma₀, independent of generator count; one-generator Fejér packet attains Ma₀ [S]. For integer coefficient vectors n_j≠0 of mixed sign, any weights m with 1≤\|n_j·m\|≤M give the same signed bound; such weights exist for every fixed finite cloud [S]. M depends on the cloud; no absolute-coefficient or growing-cloud uniform bound, and no arithmetic relation classification for actual zero ordinates. Missing: completed Euler/FE realization or RH-strength interior estimate. | [corpus](../../formal/GaloisForLFunctions/MultiplicativePositivityGeometry/); MPG:ExactFejerBarrier; MPG:GrowthToForcing [L]; RBG:CollectivePacketsDiluteOverIndependentOrdinates; RBG:EveryLatticeCloudHasAFinitePurchaseBound [S] |
| <a id="apd"></a>**APD — Arithmetic positive duality** [L] | ACS, HF | Positive-measure theta/FE rigidity; Bochner/GNS and affine spectral classification. Every nonzero L² wave, and every finite dilation measure with nonzero absolutely continuous part, admits a visible affine extension. Atomic spectrum stays blind; singular-continuous necessity unclassified. Real dilation-orbit extension and weak GNS integration do not construct actual source-compatible mixed positivity. | APD:PositiveMeasureHamburgerRigidity; APD:EverySquareIntegrableWaveHasAVisibleSuccessor; APD:EveryDensityHasAVisibleAffineExtension; APD:TheArchimedeanDilationOrbitExtendsToRealScales; APD:TheGNSRepresentationInheritsWeakMeasurability |
| <a id="acp"></a>**ACP — ArithmeticCorrespondencePositivity** [L] | ACS, HF, WL, MC, PM, OWU | Compact effective-pole/escape laws. Prime-error linear budget iff RH; all-c integrability and genus Abel slope iff RH+simple zeros. Uniform archimedean L² remainder and RH-conditional zero-tail exhaustion close this equivalence, not actual cancellation or PM exterior tightness. Finite-curve Mertens budget iff purity+simple spectrum; exact repulsion slope and strict-Hasse elliptic calibration. | CP:TheAbelSlopeOfThePrimeErrorIsTheArchimedeanGenus; CP:ThePrimeErrorSymbolSplitsAtTheZeros; CP:TheZeroPartHasNoMassAtInfiniteHeight; CP:AMertensBudgetIsPurityWithASimpleSpectrum; CP:TheMertensBudgetOfAnEllipticCurveIsStrictHasse; CP:CompactReceiverWindowsSelectTheMaximalVisibleOrder |
| <a id="outward-field"></a>**AES — ArithmeticElectrostatics / outward-field localization** [L/S] | HF, ACS | RH iff every right-zero field≤1 iff distinct-point total ℰ<1; ℰ finite iff finite off-line support. Compact source work exhausts full reflected multiplicity-copy energy, also ∞. Off-line distinct-zero energy satisfies 1≤E(ρ)≤16(C+log(\|γ\|+4)); window energy≤16·#window·(C+log(\|T\|+H+4)); unit-window energy<2 iff RH [L]. Defect/second-moment comparison and exterior σ>1 prime-field ceiling: [HF](#hf). Circle Fekete bound Nlog N, attained by roots of unity [L]. Terminal-lens Harnack spreads the outward lower floor with factor 1/3 [S]. Missing: subquantum arithmetic upper bound, inside-strip field control, copy/distinct energy comparison and ξ-stability transfer. | CP:EveryXiZeroHasASourceField; AES:TheFieldLawHasAThreshold; AES:TheTransverseEnergyOfTheZeroDivisor; AES:TheSelbergWorkExhaustsTheTransverseEnergy; AES:QuantizationTurnsWindowsIntoPoints; AES:TheEnergyOfAZeroIsLogarithmic; AES:TheHeckeDefectIsTheMomentOfInertia; AES:TheExternalFieldIsAPrimeSum; AES:TheTorsionIsTheStableEquilibriumOfTheCircle; RBG:CriticalDiscsAndTheTerminalLens [L]; RBG:HarnackOnTheCaratheodoryRegion [S] |
| <a id="renormalized-biarithmetic"></a>**RBG — RenormalizedBiarithmeticGeometry** [L/S] | HF, MC, ACS, OWU, AIP | Periodic survival=mode relations; Ramanujan survival=per-order cancellation, even-lag survival=per-odd-core cancellation for positive orders not divisible by 4. Exact finite parts=−orbit intersection−cyclotomic digamma/harmonic kernel. With H=cyclotomicHarmonic, pole completion gives PSD K_mn(x,y)=H_mn(x)+H_mn(y)−H_mn(x+y); node-independent intersections cancel at fixed nodes. As u→∞, K_mn(u,u)→−I(m,n) for m≠n, while K_mm(u,u)−φ(m)log u→−I(m,m)+φ(m)(γ−log2); distinct-order counterterm diag(φ(m)) has survival {0}. Dyadic parity split isolates φ(q)log2 [L]. General periodic-germ entries and I(m,n) have finite rational-shift digamma formulas [S]. E(2L)≥4E(L)+E(L)²/D [L]; terminal ceilings/Hecke caps are strip criteria [S]. [Prefix bounds](#bvi), [cell growth](#arithmetic-correlation). Missing: source-faithful full-test sign or zero defect rate; prime recovery with a new full-rank divergence supplies neither. | RBG:TheRenormalizationSurvivalLaw; RBG:TheSurvivalConeOfAPeriodicGermIsItsModuleOfRelations; RBG:TheDyadicAmplificationOfTheHeckeDefect; RBG:TheRamanujanTwinsSurviveExactlyOnPerOrderRelations; RBG:TheRamanujanTwinsCarryThePrimes; RBG:ThePoleNodeCompletesTheArchimedeanGerm; P:RamanujanParityTwinLimitsAndShortCycleObstruction [L]; RBG:TheTwistedEntriesAreDigammaSums; RBG:TheTerminalCeilingAndTheOneScaleBoundAreZeroFreeStrips; RBG:TheHeckeMomentProblem; RBG:IntegerThetaPrefixesReadTheDefectWithoutLoss; RBG:TheSelectivityBatteryOfRenormalizedBiarithmeticGeometry [S] |
| <a id="arithmetic-intersection"></a>**AIT — ArithmeticIntersectionTheory** [L/S] | HF, ACS, AIP | Torsion adjunction, cyclotomic quotient log-orders/discriminants, Abel finite parts and non-coboundary Hecke cocycle. Prime form Q=Σ_pQ_p on p-free fibres; no global ℓ² ceiling. Distinct-prime ladder kernels have disjoint pair support; consecutive positive orders share a p-ladder iff (n,p)=(1,2). In the defined curve-tower model, degree-d,d′ towers both charge lag lcm(d,d′) [S]; no global arithmetic coupling/sign follows. Summed individual-tower bound Q≤238√M·mass; joint bound Q_N≤(2log N+log4+4)mass [L], sharp leading constant 1 [RAPT](#renormalized-potential) [S]. Sign twins are ℓ²-isometric conjugates. Spacing regulator removes log t drift, retains tame ramification and a negative {1,2} direction [L]. On p-ladders x₀=x₁=0, Abel finite part≤−((1−p^(−1/2))/(1+p^(−1/2)))log p·Σx_j² [L], not full Weil sign. Narrow log-atoms: prime functional=‖φ‖₂²Q; pole=2αβ(Σx_n/√n)(Σx_n√n), α=∫φe^(−u/2), β=∫φe^(u/2). Gamma-only domination on Σx_n/√n=0 assumes RH [L]. Exact archimedean decomposition=self-energy·Σx_n²+pole−Σ_(m<n)x_mx_n K_φ(log(n/m)), K_φ(c)=∫_(0,∞)autocorr_φ(y−c)e^(y/2)/sinh y dy [L]; resulting tower domination assumes RH. For real C² φ supported in [−δ/2,δ/2], 0<δ<1/2, E_φ≥‖φ‖₂²(γ₀+e^(−1/2)log((1−δ)/δ)) [L]; signed inter-atom coupling remains. Reflected Dirichlet moments=2Re((Q(ρ)conj Q(ρ*))^k), not positive collided squares [L]. Missing: full signed Gamma/pole payment and arithmetic Rosati sign beyond atomic resolution. | AIT:TheDifferentOfATorsionOrbit; AIT:TheArchimedeanIntersectionIsALogOrder; AIT:TheHeckeCocycleOfRenormalization; AIT:ThePrimeKernelIsASumOfTransverseTowers; AIT:TheLocalFormsDoNotSum; AIT:TheFiniteIntersectionIsGaugeBlind; AIT:TheEllipticCorrespondencesOfTheCircle; AIT:TheSpacingRegulatorRemovesTheAnomaly; AIT:TheSelfIntersectionDominatesTheTower; AIT:TheSquareRootPriceOfSeparateTowers; AIT:WeilsPrimeFunctionalIsTheFiniteIntersection; AIT:ThePolarPartPairsThePoleDirection; AIT:ZeroMomentsAreRosatiPairings [L]; AIT:TheHodgeIndexInTowerCoordinates [L]; AIT:TheBaseAndTheSuccessor [S] |
| <a id="renormalized-potential"></a>**RAPT — RenormalizedArithmeticPotentialTheory** [S] | HF, ACS, AIP | Positive block B=[[A,C],[Cᵀ,D]], A injective: ker D⊆ker C, rank B≥dim A, prime-survival dimension≤rank D. For A=I, D=vvᵀ: C=bvᵀ, ‖b‖≤1; prime survival=ℝb at ‖b‖=1, otherwise {0}. Normalized Ramanujan modes plus any positive number of constant-mode nodes give coupling e₁1ᵀ: prime survival=ℝe₁ if order 1 is present, else {0}; no order≥2 survives. Matched vectors (−(Σw)e₁,w) have nonnegative finite part. Retaining Abel torsion forces A=cI, c>0. Finite-part −Q+Σh(n)x_n² is Hecke-covariant iff h is constant on positive orders. Weighted prime row=A(⌊N/m⌋)+log m, A(y)=Σ_(t≤y)Λ(t)/t; log N−log8−4≤κ_N≤log N+log4+4 for optimal Q_N/mass ceiling, N≥1. Pole vector n^(−1/2) supplies the lower bound. Retaining torsion self-intersections instead forces κ_N≥(3/2)log N−C under φ-weighted mass, at least (1/2)log N−O(1) above the covariant prime ceiling. Not the optimal torsion coefficient. Horizon profiles x=Σ_i c_i n^(−1/2)1_(n≤M_i), M_i≤N: \|Q_N(x)−ℓ_N(x)²\|≤(log8+5)B_abs, ℓ_N=Σ_(1≤n≤N)x_n/√n, H_M=Σ_(1≤n≤M)1/n, B_abs=Σ_ij\|c_i c_j\|H_min(M_i,M_j). Actual mass=Σ_ij c_i c_j H_min; B_abs=mass for c_i≥0, not arbitrary signed c. For prime p, span{n^(−1/2)1_(n≤M,v_p(n)=j):0≤j≤J} obeys Q_M≥(log M−C_p,J)mass. Hence ∀J,K, sufficiently large M admit a positive-mass vector in the common kernel of any J linear functionals with Q_M>K·mass: even polar neutrality or fixed-rank corrections leave unbounded raw prime energy. This does not obstruct full Gamma/pole compensation. Missing: source-faithful coupled prime/Gamma/pole sign and sufficient surviving test space. Support, not independent route. | RAPT:TheCoupledSurvivalLaw; RAPT:TheArchimedeanPlacePaysTheArithmeticPoint; RAPT:TheCovariantCountertermIsTheAnomaly; RAPT:TheAnomalyCostsHalfALogarithm; RAPT:TheHorizonCountertermIsPolar; RAPT:TheHorizonDivergenceLivesOnTheTorsionOrbits [S] |
| <a id="atomic-stability"></a>**Atomic-resolution stability** [L/S] | AIP, HF, ACS | N≥1, δ_N=log(1+1/N), real C² g supported in [0,w], f=Σ_(1≤n≤N)x_n g(·−log n), arbitrary real x_n. For 0<w≤δ_N/4: M(f)≥[2θ′(0)+e^(−1/2)log(δ_N/(2w))−2log N−log4−4]‖f‖₂², M=arch−prime. Thus M(f)≥0 for w≤(δ_N/4)exp(−e^(1/2)(2log N+log4+4+2\|θ′(0)\|)). Every completely multiplicative ±1 twist shares finite prime-form spectral bounds and M_ω≥0 at this width. For w<δ_N, M_ω−M=‖g‖₂²(Q_N(x)−Q_N(ωx)); x_n≥0 gives M_ω≥M. At a flipped prime p≤N, x=1_{1}+1_{p} gives M_ω−M=(2log p/√p)‖f‖₂² [L]. This fixed-p normalized margin is independent of N, not uniform in p. For ζ, C=∫f cosh(u/2), S=∫f sinh(u/2), Re W=M+2C²−2S²: Re W+2S²≥0 and Re W≥0 on \|S\|≤\|C\|, including nonnegative bump/weights [S]. Missing: signed/reflected all-test transfer; ζ minimizes M on the nonnegative-weight gauge orbit; neither this margin nor the moment cone implies odd positivity. | AES:TheStabilityLawAtAtomicResolution; AES:TheGaugeIsInvisibleAtAtomicResolution [L]; AES:TheWeilFormAtAtomicResolution [S] |
| <a id="arithmetic-polarization"></a>**ArithmeticPolarization** [L] | ACS, HF, OWU, PM, RW | Faithful collided form; one-shift similitude⇔RH; depth rates and Weyl growth. Fixed-aperture collided norm≍log-weighted Fourier L² norm; signed Weil Gårding bound and finite negative index. Section positivity and commensurable Fejér–Riesz coupling. Constants depend on aperture; no translation invariance or zero negative index follows. | PL:TheCollidedFormIsAPolarization; PL:TheDepthProfileCarriesTheGlobalCollision; PL:OneVerticalSectionDecidesPositivity; PL:PositiveLatticeLinesAreCouplings; PL:TheCollidedFormIsTheLogarithmicSobolevNorm; PL:WeilsFormHasFinitelyManyNegativeDirectionsAtEveryAperture |
| <a id="conjugate-diagonal"></a>**ConjugateDiagonalGeometry** [L] | HF, ACS, OWU, SRT | Fixed-strip source: theta cutoff N_n=(K+4)(n+1)²⁰, η_n=exp(−K(n+1)²⁰), fixed bump control K. Uniform 4^j-normalized moment error O(n⁻²+log n/n) on a+j\|L\|≤2log(n+1), \|τ\|≤n/2. Two-radius divisor detector r_n=1/[16(n+1)⁶], error O(n⁻²), threshold 1/2, centers 0≤Re c≤1 and \|Im c\|≤n/2. Separate full-theta C^r test law permits j\|L\|≤(2r−2)log(n+1), r≥2. No quadrature, zero exclusion or Hecke-defect upper sign. | CDG:PolynomialSourceScale; CDG:PolynomialThetaMetric; CDG:PolynomialThetaLocalSelection; CDG:ThetaSourceRegularityMetric; CDG:TwoScaleDepthRigidity; CDG:TheConductorForcingGap |
| <a id="arithmetic-effectivity"></a>**ArithmeticEffectivityTheory** [L] | ACS, HF, WL, SRT, MC | Effectivity/Tate/height receivers; polar-box RI iff Hodge; torsion=ψ, first Fourier=M. Squarefree odd-degree hyperelliptic calibration and elliptic Hasse over every odd-characteristic finite field. Quadratic-character Burgess bound for all intervals and r≥2; least nonresidue≤p^(1/(4√e)+ε) eventually. Character estimates do not supply actual μ cancellation or ζ Rosati heights. | AE:TheEffectivityCalculus; AE:NaiveHeightsAreTraces; AE:ThePolarBoxCount; AE:TheHyperellipticCalibration; R:HyperellipticDescent; R:EllipticCurveHasseBound; AE:TheBurgessBound; AE:TheLeastQuadraticNonresidue |
| <a id="sbwf"></a>**StripBochnerWeilForcing (SBWF)** [L] | ACS, MPG | Completed-system shrinking collars and real-zero budgets. Simple-pole class exactly real nonzero multiples of ζ, d=1; κ=2 admits off-critical models. Source identification and real-zero contraction do not exclude nonreal interior zeros at κ=1. | SB:SharpHalfPoleCollar; SB:StripReflectionRigidity; SB:TheSimplePoleClassIsZeta |
| <a id="arithmetic-kunneth"></a>**ArithmeticKunnethTheory** [L] | HF, ACS | Total-support depth bound, diagonal product moments and Künneth–Adams count positivity. Golden impure datum satisfies the entire positive-count hierarchy. Actual signed product/trace mechanism missing. | AK:ProductReceiversSeeDepthOnlyThroughTotalLength; AK:KunnethPositivityIsPointCountPositivity |
| <a id="arithmetic-correlation"></a>**ArithmeticCorrelationGeometry** [L/S] | MC, PM, HF, ACS, AIP | Gauge classification/averaging, a.e. square-root/successor cancellation, Pell moments and escape measures [L]; actual μ gauge not selected. For 0<θ₀≤1/2 and θ₀X<q<1/(2θ₀), coalescent congruent-pair sum=0; principal-character gauge=0 even at ramified primes. Exact inversion: primeCoalSum=−Σ_(χ≠1)Re twistedSum_χ; Cauchy–Schwarz retains factor φ(q)−1. At bandwidth 4/3, q=⌊T^κ⌋ works for 1/3+η<κ<1−η [L]. For every real sign gauge σ with σ(2)=−1, 162(K+1)^4≤X gives #charged cells≥K and hsDefect_σ(X,c)≥2K for every c; hence the minimal defect diverges. Witnesses a=2t(t+1), 2a+1=(2t+1)², arise from successor sign changes. Liouville agreements λ(a)=λ(2a+1) inherit this fourth-root count [L]. Missing: matching-profile prime-surplus cancellation, formalized positive-density cell bounds (for Liouville, logarithmic density 1/2 follows from Tao's two-point logarithmic Chowla theorem; natural density is open two-point Chowla) and full signed-form transfer. | ACG:AlmostEveryGaugePointCancelsToTheSquareRoot; ACG:TheMoebiusExceptionalSetIsComeagerAndNull; ACG:RHIsTheVisibilityOfEveryEscapeState [L]; ACG:SubProgressionStabilizerInversionAndCellHolonomyGrowth; RBG:LogCellsFixTheGauge; RBG:TheCellHolonomyDefectCountsChargedCells [L]; RBG:TheLiouvilleCellDefectGrowsLogarithmically [S] |
| <a id="aldg"></a>**ALDG — ArithmeticLocalDivisorGeometry** [L] | LA, WD | Actual finite-head coordinates; local repair cones, universal reflectors, sharp Hermite/heat barriers, attained extremizers and asymptotics. Model optimality does not supply actual all-height coefficient sign. | ALDG:SourceLocalFactors; ALDG:SourceDivisorGeometry; ALDG:HermiteHeatRootBarrier; ALDG:MaskedPairHeatThreshold |
| <a id="ssa"></a>**SignedSuccessorArithmetic** [L] | MC, PM, BVI | Sharp odd-shift/lag-2 logarithmic floors 1/3 and 1/4; successor cocycles, finite-field moments and signed half-damping endpoint. Twin extremizers prevent generic floors from proving actual μ/Liouville cancellation. | SSA:TheShiftFloorsAreExact; SSA:TheHypercubeFormIsBoundedAtHalfDamping; SSA:TheSizeTruncatedHypercubeFormIsTheReceiver |
| **TransThresholdPairCorrelation** [L] | HF, ACS | For every 0<η<1/3, ε>0, selected smooth profiles give eventually N₀ˢ−M_off≥(29/36−ε)N−S and S_off+2M_off≤(7/36+ε)N+S, S=primeCoalescentSurplus. Proper powers=o(N), not o(1); actual prime sum=model+centered discrepancy [L]. Missing: S≤(1/18+o(1))N on the same certificate profiles. `PrimeCoalescentSurplusAtMost` distinct-count witnesses are not automatically these profiles. No unconditional 75% on-line theorem. Unconditional census [L]: (2/3−ε)N+M_off≤N₀ˢ, M_off≤(1/6+ε)N, ≥(4/5−ε) of ordinates carry a critical zero; ≥3/4 of copies lie within 4/log T of the line. | P:SmoothWeightedCertificateAtFourThirds; P:CoalescentPrimeReductionAndParitySieve; P:RamanujanDirichletCoalescentTransfer; P:ParitySensitiveRamanujanStabilizerTransfer; SP:ParityLobeObstructionAndEscapeLaplaceSplit; R:Zeta23OffLineMultipleExclusion; R:Zeta23SimpleOffLineNearLine; R:Zeta23CriticalOrdinateCensus [L] |
| **SelectivePositivityAndThresholdLaws** [L] | AIP, OWU, EWU, RW, SRT, MC, HF, ACS | Short-cycle/escaped-μ receivers, theta box RR, Jacobi-height models and parity/raw-tower obstructions. Full real/complex floor 1/5000 through radius 181/500; odd Λ-positive witnesses negative for Liouville and single-atom-2 twins at that radius; some nonzero shifted-pair even witness negative there. Higher primes remain unseen when 2A<log3. At radius 23/40 one odd witness is Λ-positive (>‖F‖₂²/25) and Liouville-negative (<−(3/10)‖F‖₂²); the full ζ floor there is not certified. Support, not independent route; all-aperture sign open. | SP:JacobiHurwitzTorsionInflationAndShortCycleHeights; SP:MoebiusEscapedPairingBoundaryLaw; SP:SerreDualScalingCohomologyAndLargeSieveSections; SP:TwoPrimeCatalanSeparationAndContinuumTowerObstruction; SP:LiouvilleOddWindowRefutationAndSelectiveFullPositivity |
| <a id="closed-cycle-tools"></a>**Controlled closed-cycle recovery** [L] | HF, EWU | Normalized real L² autocorrelations continuous/even/unit-bounded. General finite-net recovery retains collar amplification κ^(−n−1), continuity modulus and support cutoff. Derivative-controlled sources with normalized energy≤B and n+1≥BR² instead obey sup error≤2e_spoke+2(n+1)e_pair+2√Bη; common-array error≤2(n+2)(res_f+res_g)+2√Bη. Linear conditioning requires this derivative subclass and a common support cutoff, not arbitrary L². Integer-blind grid subclass retained. Recovery supplies no signed Weil positivity. | B:ControlledClosedCycleRecovery; B:ClosedCycleDataResiduals; B:GridCycleRecoveryParameters; B:FiniteNetClosedCycleRecovery; B:L2ClosedCycleRecovery; B:FiniteNetDerivativeRecovery |
| **Finite-window incidence / concrete certificates** [L] | PM, BVI; shared | Actual ancestor depths occur once each; weighted path bound has factor 4. Clipped binary-parent coercivity Σ_(1≤n≤N)(f(n)−f(1))²≤8NΣ_(2≤k≤N)(f(k)−f(⌊k/2⌋))². Actual exact-doubling incidence recovers integer-grid joint bound 24N; arbitrarily small ordered quadratic node perturbations erase every doubling edge, forcing any joint constant≥N(N+1)/12. On N=2^(h+4)−1, doubling alone admits no finite coercivity constant; tent high/low level counts are explicit. Tolerant weighted incidence survives with displacement cost. Finite sieve/source realizations do not supply cofinal admission or global positivity. | B:FiniteWindowVariance; B:BinaryDepthCoercivity; B:BinaryPathWeights; B:DyadicTentLevelCounts; B:ExactDoublingEnergy; B:WeightedDoublingIncidence; O:ConcreteSourceDictionaries |
| <a id="analytic-large-values"></a>**Analytic large-value / zero-density tools** [L] | HF, WL, ACS, SRT, OWU; shared | Guth–Maynard/Heath–Brown, sharp S₂, Selberg near-line density and smoothed Landau formula [L]. For finite zero-copy sets G in (A,A+R], A≥T₀, R∈ℕ, F(t)=Σ_(n≤N)a_n n^(it): Σ_γ\|F(γ)\|²≤Klog(A+R+1)(R+8N(1+log N))(2+log²N)Σ\|a_n\|². Large-value count·V² obeys the same bound; a_n=w_nΛ(n)/√n, \|w_n\|≤1, gives mass≤log N(log N+log4+4) [L]. Prime-supported convolution mass≤k!·mass^k [L]. For F(t)=Σ_(p∈P)w_p log p·p^(−1/2+it), P⊂{primes≤X}, \|w_p\|≤1, X≥2, R≥1, V>0, 0<θ≤1 and log R(log X+7)≤θV²: #\{γ∈G:\|F(γ)\|≥V\}≤Klog(A+R+1)R(1+log R)(2+log²R)θ^(−1)R^(logθ/log X) [L]. Strict exponent saving needs θ<1. No off-line-zero→alignment implication or exceptional-count extinction; holomorphic moments at ρ differ from nonnegative ordinate moments. | R:ZetaZeroDensityThirtyThirteenths; R:Sieve/HeathBrownPairSumAllLengths; B:ZeroDensityFilteredCriticalDeficitLaw; G:ZeroDensityFilteredWeilPositivityAndCoercivity; R:SelbergShortWindowNearLineDensity; R:ZetaSmoothedLandauFormula; AES:LargeValuesAtZeroOrdinates [L]; AES:HigherMomentsAtZeroOrdinates [L] |
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
| SP | SelectivePositivityAndThresholdLaws | AES | ArithmeticElectrostatics |
| RBG | RenormalizedBiarithmeticGeometry | AIT | ArithmeticIntersectionTheory |
| RAPT | RenormalizedArithmeticPotentialTheory | — | — |

## Alias lookup

BVI→[support](#bvi); C1→RW; CCM-FU→FU; CLG/TTF,K-RVM,S6F,TCD,UEB→TH; CSB,STC,U,MPLF,RHist,BPC,TQFQ,WS2,SQB→RN; D2,Q,RG,RG-ETA,TK→PA; E,EDQ,L,HDL,PSRC→MC; FZZ-P→PM; PW-B→[candidate](#pw-b); G,HC→WD; O→WL/RW (genus mechanism dead); P,SP-E→RP; SV2,RG-HF→SZ; T1,T2,Route T→TT; Route T successor/ULF sub-unit anchor→TG; Deninger→HF. [Retired labels](rh-killed-routes.md#retired-labels).
