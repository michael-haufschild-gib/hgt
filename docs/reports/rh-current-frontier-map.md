# RH proof-route frontier

**RH open · 38 live route formulations · 9 candidates.**
**Corpus checkpoint:** `fd3e350aa0a5d051b24c74764fbd082db4dd60e0`.

Live = source observable + proved RH-sufficient receiver + explicit open estimate. Candidate = missing independent source mechanism/landing.
Formulations need not be independent: HJ→PA, BSH→CDC; FEL's BSY criterion→CTF. Source construction does not discharge zero-selective sign/vanishing.
Evidence: [L] integrated, source-reviewed; [S] unfinished/unintegrated, unverified; [K] individual Lean + standard-only transitive-axiom audit. Untagged established facts: [L].
Notation: vkScale(x)=(logx)^(3/5)(loglogx)^(−5/3).

[Routes](#live-routes) · [Candidates](#route-candidates) · [Shared positivity frontier](#shared-frontier) · [Killed/retired](rh-killed-routes.md) · [Source codes](#source-locator)

<!-- Status quo only: replace the affected frontier; do not append theorem inventories. -->

## Find a route

| Family | Live routes | Candidates |
|---|---|---|
| Arithmetic incidence | [AIP](#aip) | — |
| Prime explicit formula / signed energy | [WL](#wl), [RW](#rw), [FU](#fu), [CFC](#cfc), [RP](#rp), [PA/HJ](#pa), [LI](#li), [JAS](#jas), [CTF](#ctf), [EWU](#ewu), [OWU](#owu), [PBM](#pbm), [RB](#rb), [ACT](#act) | [APF](#apf), [EGC](#egc), [EWJ](#ewj), [FEL](#fel) |
| Möbius cancellation | [MC](#mc) | [MSC](#msc) |
| Theta / heat / moments | [TT](#tt), [LA](#la), [TH](#th), [HCF](#hcf) | — |
| Zero visibility / localization | [SRT](#srt) | — |
| Zero-configuration geometry | [ZCG](#zcg) | — |
| Causal hyperbolic–modular duality | [CHMD](#chmd) | — |
| Geometry / index / arithmetic rigidity | [TG](#tg), [HF](#hf), [GTA](#gta), [ACS](#acs) | [IRK](#irk) |
| Newton dynamics | [XN](#xn) | — |
| Renewal / singular comparison | [RN](#rn) | — |
| Ward / collision | [WD](#wd) | — |
| Suzuki / boundary limits | [SZ](#sz), [SEC](#sec) | — |
| Physical realization / cosine zero-loss | [PM](#pm), [PTR](#ptr) | [W1C](#w1c) |
| Singular source completion / affine index | [SC](#sc), [CDC/BSH](#cdc), [PCS](#pcs) | [RFHM](#rfhm), [WBF](#wbf) |
| Deterministic recurrence | [BAG](#bag) | — |

## Live routes

<a id="wl"></a>
### WL — Weil lag function

- **Path:** Actual prime-deficit critical energy bounded → RH.
- **Established:** Bounded endpoint energy⇔RH; every eventually nonempty cyclotomic bandwidth has energy abscissa2Θ. First-band O_ε(N^(1+ε))⇔RH. Pole-subtracted prime-source gauge exponents range exactly over [Θ,1], minimized at the trivial gauge [K].
- **Open:** Actual ∃C∀t≥0, E(t)≤C, or first-band square-root-scale bound. The gauge spectrum does not construct exponent1/2; [pole matching is insufficient](rh-killed-routes.md#pole-matching-half-power).
- **Sources:** B:WeilLagCriticalDeficitEndpointAndLimitLaw; R:CCM/CCMPrimeDeficitCriticalEnergy; CAF:FirstCyclotomicBandAbscissa [L]; AGT:ThePoleSubtractedSpectrumIsAnInterval [K].

<a id="rw"></a>
### RW — Restricted Weil ground energy

- **Path:** Complete Weil form → μ(a)≥0 at every radius → RH; equivalently prime-blind archimedean/pole positivity (PBAP).
- **Established:** Attained minima; floor1/(20000·2^k) through a_k, a₀>181/500. Precontact det H=1 and endpoint-trace Gram identity; all-lattice/two-site receivers [L]; exact {2,3} band below log2 [K]. Scalar flow: L=artanh r, Ψ=½logH₁, ΔL=ΔΨ−∫sinh(2L), ∂₊logK(i,i)=2cosh(2L); finite contact forces anchor-kernel/∫1/(1−r²) blowup [L]. One nonzero exponentially decaying Ξ-divisible integer-blind test has archimedean/pole energy0; full positive cone, if nonempty, is pinned to Λ [L].
- **Open:** Ψ(x)−Ψ(base)=∫q, q∈L¹ through finite contact. Actual precontact Riesz charts have bounded forcing, exact Green/endpoint readout and all prime/polar/commutator terms; Green error≤2‖f‖∞V², V=renewal mass [S]. Aperture-uniform forcing/readout control through contact remains. Alternative PBAP: archimedean/pole energy≥0 on every nonnegative finite mixture blind at ±log n, n≥2. Exact null-test correlation has sharp tail exponent1 [L], not universal sign. [Floor boundary](rh-killed-routes.md#frozen-weil-floor-tower); [prime-entry](#prime-entry), [EWU](#ewu), [OWU](#owu), [ACT](#act).
- **Sources:** C:TheApertureFlowNeverStalls; I:TheWeilFloorTowerIsFrozen; CSTW:{TheWeilKernelDivergesAtContact,TheWeilTowerHasItsPrecontactCanonicalSystem,TheWeilHamiltonianHasDeterminantOne,TheWeilKernelVanishesAtZeroAperture,TheSamplingAtomsArePositiveMimicsOfZeta,AHyperbolicFlowIsRestoring,TheWeilChainIsOneScalarFlow}; GWZ:RHIsDecidedOnTwoSites; VHR:WindowEntries; R:{TwistedArcMinimumPrincipleProof,WeilConeXiDivisibleBlindTest}; B:ExactExtremal/ExactBlindTest [L]; CSTW:{TheRenewalReadoutHasAnExplicitModulus,TheWeilRieszVectorsHaveGeneralCharts} [S]; B:ExactExtremal/SharpCorrelationTail [L]; SWC:BelowLogFour/RetainedVarianceAndHalfWindowBandBelowLogFour [K].

<a id="fu"></a>
### FU — CCM-FU signed prime scheduling

- **Path:** Signed prime/Möbius history → one-sided sampled Abel bound → RH.
- **Established:** Fixed integer m≥1: either one-sided bound on A(j^m)/j^m⇔RH. One controlled sample per sufficiently large backward window of length N^(1−δ), some δ>0, suffices. Exhaustive bounded-size prime blocks and insertion prefixes are paid at each block's fixed horizon [L].
- **Open:** Complete-history sample bounds across advancing clocks, retaining seed, drift, covariance and endpoints. Fixed-horizon payment does not control cross-clock debt.
- **Sources:** R:{MobiusDivisorOneSidedPowerGapBootstrap,MobiusDivisorLowerStripPowerGapBootstrap,MobiusDivisorPaidPrimeExhaustion} [L].

<a id="cfc"></a>
### CFC — CCM first-clock lower bound

- **Path:** Published first-clock sine coefficient bounded below on an aperture tail → RH.
- **Established:** Exact tail criterion; ¬RH forces unboundedness below on every tail. Finite-matrix all-aperture phase-natural transport is identity for distinct positive clocks and nonzero source coordinates.
- **Open:** Actual lower bound retaining prime, archimedean and endpoint terms; transport feasibility supplies no bound.
- **Sources:** R:CCM/CCMFirstClockTailLowerBoundCompleteness; R:CCM/CCMFirstClockPhaseNaturalTransportRigidity.

<a id="rp"></a>
### RP — Route-P / SP-E history floor

- **Path:** Matched−quantile prime history → eventual linear defect floor → RH.
- **Established:** Exact linear-floor criterion; low-LCM and copied-diagonal payment. Sublinear floor is impossible.
- **Open:** High-LCM pairs, moving core and singular-domain terms in one complete-history floor.
- **Sources:** R:SPEQuantileRieszRoutePLinearFloorCriterion; R:RoutePLcmPairPayment.

<a id="pa"></a><a id="hj"></a>
### PA — Prime–archimedean source passivity

- **Path:** Prime−archimedean trace → current sign or subexponential mismatch → RH.
- **Established:** One C>0 gives calibrated Hausdorff-row sign for every k and r≥C(k+1)²; complete saddle/core/tail assembly closed. Explicit row thresholds H(k) also available. HJ exterior scalar-diagonal criterion has discharged radius218/25 [L]. [Verified-height transfer](#finite-height) gives conditional finite ranges; HJ residual-only branch overlaps SEC/HCF.
- **Open:** Signs below the quadratic boundary, uniformly in unbounded k; these remaining entries⇔RH. Alternatively K(z,z)≥0 on 0<Im z<1/2, Re z>218/25 at regular points ζ(1/2+iz)≠0, or TV(n)/qⁿ→0 for every q>1. Finite per row is not a finite RH certificate.
- **Sources:** R:{PrimeArchEndpointFrequencyAccretivity,PrimeArchBernsteinExponentialPhase,XiHurwitzOrientationPositivePairedSource,XiPositivePairedDiagonalSectorCollapse}; S:EffectiveHorizons/{HausdorffShifts,HausdorffQuadraticRegion} [L].

<a id="finite-prime-clocks"></a><a id="mc"></a>
### MC — Möbius cancellation at half power

- **Path:** Actual Möbius/Liouville half-power cancellation → RH.
- **Established:** Bounded damped E_ε for arbitrarily small ε>0⇔RH; fixed-t₀ sharp M_N(1/2+it₀)=O_ε(N^ε)⇔RH. Undamped energy≤CTexp(−c·vkScale(T)), N≤T. Möbius-polynomial zeros accumulate at every point of Re s=Θ=1/2+zeroWidth; compact subsets right of Θ, excluding1, are eventually zero-free. Eventual zero-freeness on every compact subset of Re s>1/2 excluding1⇔RH [L]. Explicit half-power gauges exist; pole-preserving flips have exponent max(θ,Θ) [K].
- **Open:** Actual trivial-gauge cancellation or independent Möbius-polynomial zero exclusion right of1/2; signed long-modulus/harmonic-tail payment. [Bounded undamped Hilbert form fails](rh-killed-routes.md#mobius-hilbert-endpoint). [Pole matching](rh-killed-routes.md#pole-matching-half-power), [coefficient norms](rh-killed-routes.md#moebius-coefficient-blindness) and zero-location reformulation supply no half-power bound.
- **Sources:** R:MobiusHilbertFormEquivalence; ADT:TheMertensFunctionIsAGluingDeterminant; C:{TheDampedMobiusCriticalEnergy,MobiusHilbertVinogradovKorobov,LongModulusExactDecomposition}; MZF:{TheWidthIsReadInOneWindow,TheZerosOfTheMollifierCondense} [L]; AGT:{AnExplicitPointHasExponentOneHalf,TheFlipPointsBreakTheMoebiusHalfPowerLaw} [K].

<a id="tt"></a>
### TT — Theta-tail and heat–Cassini currents

- **Path:** Actual theta/Wold residual → bounded weighted endpoint energy for every t<1/2 → RH.
- **Established:** Wold residual=O(exp(−c·vkScale(N))); D_t+Q_t/2=endpointEnergy_t/2≥0. Boundedness for each 0<t<1/2⇔RH. Φ-Doob identities retain every reflected-prime term. Uniform endpoint bound on the shrinking band 0≤t≤min(1/2,κ·vkScale(N+2)/(96log(N+2))) [L].
- **Open:** For every fixed 0<t<1/2, some C_t bounds D_t(N)+Q_t(N)/2 for all N, with literal weights (n+1)^(2t). Shrinking-band control does not reach a fixed positive t; endpoint t=1/2 fails. Odd-sign branch: [OWU](#owu).
- **Sources:** R:{PaperWoldDirectedCovarianceEnergy,PaperWoldDirectedCovarianceRH,WeilMarkovOddPositivity}; M:WoldResidualVinogradovKorobov; C:ThetaEndpointVinogradovKorobov [L].

<a id="la"></a>
### LA — Jensen line anchor

- **Path:** Actual Ξ Jensen polynomials → sublinear upper imaginary-root growth → RH.
- **Established:** RH⇔infinitely many unshifted Jensen degrees real-rooted. Also RH⇔∀ε>0, infinitely many reversed degrees have maximal upper-root height≤εd, for each fixed finite Möbius mollifier, σ>0 and phase. Large-d reversed Jensen roots with abs(Re z)≤√(d log d)/100 are real. Nonreal multiplicity N_d is nondecreasing, sup_d N_d=total off-line ζ multiplicity; N_d≤300√(d log d) for log d≥6.1·10⁶ [L]. [Verified-height transfer](#finite-height) gives conditional full-degree reality.
- **Open:** Control roots outside the proved inner region: sublinear maximal upper height or all-root reality. Bounded N_d would give only finite off-line support. [Bulk reality permits unbounded exceptions](rh-killed-routes.md#jensen-bulk-reality). Heat descent: [ZCG](#zcg).
- **Sources:** FFP:{FiniteFreeDeBruijnNewman,ImaginaryPartDichotomy,JensenCountsOffLineZeros,NonRealJensenCountBound,JensenRootsAreRealBelowTheSaddleEdge,BulkBlindness} [L].

<a id="zcg"></a>
### ZCG — Zero-configuration geometry / heat descent

- **Path:** Actual ξ half-Gaussian source → exclusion of positive-time heat collisions → RH.
- **Established:** No positive-time real collisions⇔RH. All-height large-X horizon (6600/9991+ε)/logX. For every δ,ε>0 some κ>0 gives, for large T outside δT heights, reality and gap error abs(g·log(x/2π)/2−π)≤ε in abs(Re z−X)≤κ/(2logT), when 7κ/logT≤tlog(Re z/2π)≤1/8 [L]. Power-saving capstone: for every κ>0, some θ<1 bounds by T^θ the measure of X∈[T,2T] with a nonreal heat zero within abs(Re z−X)≤1 at any t≥κ/logX; likewise localNewmanConstant(X)·logX>κ, for large T [S; half-Gaussian/slope API mismatch].
- **Open:** All-height collision exclusion at arbitrarily small t, including bounded/exceptional heights: frequency<1 at every collision or global central-gap control. At power level η³/40000, depthWindow(d,η) yields localNewmanConstant(X)≤(d+16η)/log((X−1)/2π) for large X, 0<η≤1/8 [S]; local zero-free-strip/level inputs and exceptional heights remain. Density approach needs normalized-derivative lower bounds and weak/multiple-zero control; exact simple-zero Blaschke identity is available [S]. [Heat structure cannot select time0](rh-killed-routes.md#heat-time-shift).
- **Sources:** ZCG:HeatScaleRepulsion/{SubWeylCollisionFreeHorizon,SymmetricHalfCollisionLaw,LocalNewmanDensityOne}; NGF:{TheCentralInequalityIsStrongerThanRH,TheCentralInequalityAtTheCriticalScale,TheZerosAreRealAtTheCriticalScale,TheCrystalIsFormedAtTheCriticalScale}; MZF:TheCountNeedsNoSeparation [L]; ZCG:HeatScaleRepulsion/{TheSlopeOfXiAtAPowerLevel,TheHalfGaussAtAPowerLevel,TheExceptionalSetHasAPowerSaving} [S]; [MZF/AIF](#mzf).

<a id="tg"></a>
### TG — Topological sub-unit gate

- **Path:** Actual anchored cubic defect → trace norm<1 → integer zero count vanishes → RH.
- **Established:** Source defect constructed and trace class; exact integer trace and enclosed multiplicity≤trace norm. Endpoint decay/subunit and Gaussian central-gap receivers [L].
- **Open:** For every formation rectangle R, some x>0 satisfies ‖anchoredCubicDefect R x‖₁<1. Alternative scalar Gaussian passage: bounded centered boundary-argument L¹ oscillation along some x_k↓0 on every required circle. A scalar prime budget<1 is not an established cubic trace-norm bound.
- **Sources:** R:{FormationAnchoredCubicSpecialization,FormationAnchoredCubicEndpoint,RestrictedUnitaryCubicRelativeIndex,GaussianCentralGapExplicitCriterion,GaussianPassageBoundedUnderRiemannHypothesis} [L].

<a id="hf"></a>
### HF — Positive Hodge form on arithmetic cohomology

- **Path:** Complete arithmetic form ≥0 → Hodge index → RH.
- **Established:** Small-critical-multiple full-space floor; every fixed critical ratio has positive conductor packet through ⌊(logN)^(13/32)⌋. Optimal terminal correction is pole-attained, zero on ker S_A [K]. Every compact C² profile: log-log overlaps positive on conductor spans N^θ, every θ<1/4 [L]. Cofinal source-work≤2⇔RH; [shared frontier](#shared-frontier).
- **Open:** Full-space sign eventually at c=2K(logN)^(1/8) for every K>0, or the cofinal source-work ceiling. Full complement, larger conductors and source-kernel control remain. Far-complement O(c) loss exceeds the available O(logN/c⁷) reserve at large ratios.
- **Sources:** CACT:{CriticalMultipleCompleteWeilPositivity,TheCriticalLowPacketRetainsItsSignedPolarPart,EveryLowPacketCorrectionHasItsPolarCapacity}; AHD:TerminalPolarSourceHasANontrivialKernel [K]; SSHA:EveryEighthRootMultipleReceivesTheTiltedSpline; AID:TheSourceWorkHasAClosedQuantumThreshold [L].

<a id="chmd"></a>
### CHMD — Causal Hyperbolic–Modular Duality

- **Path:** One-sided bounded prime wave or odd Doob half-threshold bound → RH.
- **Established:** Wave/Doob receivers. In original Haar/coarse masses, (full prime−pole)/√Y has operator norm O(exp(−√log Y/92160000)), uniformly over detail horizons and M≤exp(√log Y/184320000). After a finite detail head, the complete nonfirst source retains any fraction 1−ε of Gamma energy, with exact cosh/sinh pole squares [L].
- **Open:** Either upper or lower boundedness of the unnormalized prime wave, or complete odd sign paying first-prime, potential and polar terms. Normalized decay and nonfirst reserve do not supply this payment.
- **Sources:** R:CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion; R:CHMDOddSectorCriterion; AID:{AllDetailPrimePoleCancellation,TheFullNonfirstSourceRetainsAlmostAllGamma} [L].

<a id="th"></a>
### TH — Theta moment positivity

- **Path:** Signed center-mixed theta jets → all-rank Hankel positivity → RH.
- **Established:** Full source ranks≤9 for 0<a<1/2; all ranks in collar width ≍(logN)^(−2/3)(loglogN)^(−5/3). Two-atom and q^n-chain all-rank sign, q≥2; remainder O(ae^(−πM)); rank-N receiver uses a cubic frequency window. Complete aperture spectrum=Σ_N τ_b(N)A(logN)=limit of prime second-difference inverses applied to A. Fixed-frequency pair sum absolutely convergent; A>0 with double-exponential decay; τ_b are literal Eisenstein divisor coefficients [L].
- **Open:** Full-source rank10+ at every aperture: sign of the complete signed spectrum. Exponentially decaying, exponentially convex amplitudes form an insertion-stable cone [S]; no actual-source membership supplied, and [positive Laplace-mixture membership fails](rh-killed-routes.md#theta-laplace-mixture) [L]. Frequency-weighted Bessel averaging still needs interchange. [Pointwise prime-difference iteration fails for2,3](rh-killed-routes.md#theta-two-prime-center); [finite heads lack an all-rank margin](rh-killed-routes.md#theta-finite-head-margin); [unequal pairs change sign](rh-killed-routes.md#theta-pairwise-positive).
- **Sources:** R:ThetaCusp/ThetaCuspCenterMixedSignedJetCompleteness; TCS:StrictEighthSection [K]; TCS:{StrictNinthSection,VinogradovKorobovCriticalCollar,AllApertureFiniteRankCriterion}; CAF:{TwoAtomAllRankAperture,ThetaPairGaussianRemainder,GeometricAtomApertureSpectrum,BesselTailCoshMoment,ThetaExponentialApertureProfile,EisensteinDivisorTrace,TheApertureSpectrumIsAnEulerProduct} [L].

<a id="rn"></a>
### RN — Theta renewal and singular comparison

- **Path:** Two-ended theta renewal source → exclusion of joint energy/cross-flux nodes → RH.
- **Established:** Compact cone-preserving operator; det₂ represents renewal denominator D, not Ξ. Two-ended formula recovers Ξ with multiplicities; full-divisor zeros are exactly joint nodes. In theta ground coordinates, complete Weil sign⇔Gamma/polar jump energy≤prime jump energy [L].
- **Open:** Exclude joint nodes for 0<x<1/4, y>0, or prove that all-profile energy comparison. The comparison overlaps RW; cone positivity cannot replace it. Actual renewal spectrum is nonreal and loop Pick index is infinite in both signs: [obstructions](rh-killed-routes.md#renewal-positivity).
- **Sources:** R:{ThetaRenewalPositiveFredholm,ThetaRenewalFredholmSpectrum,ThetaRenewalFullDivisorCharge}; R:CCM/CCMThetaGroundRHCriterion [L].

<a id="heat-charge"></a><a id="log-scale-defect"></a><a id="mollified-corridor"></a><a id="wd"></a>
### WD — Ward orientation and horizontal collision

- **Path:** Source current/window energy → collision-charge bound, all-resolution sectoriality or cofinal long-mollifier moment control → RH.
- **Established:** Attained extrema/collision receivers; RH⇔fixed-[0,1] ζM_N second moment subpolynomial in N. Cofinal long-prefix O_θ(T^K), fixed K/unbounded θ, suffices. Width slope=2w; pure-Möbius equivalence; r=2 zero-damping head=1−1/(D+1). Sparse subpolynomial compact parity energy or sharp defect gives K=3. Corridor b·loglogT/logT, b>1: bad-window measure O(T/log^ηT), 0<η<b−1; b>2 gives eventual control on almost every geometric ray [L].
- **Open:** Produce a fixed-window subpolynomial bound, `hcofinal` with θ-independent K (constant C_θ may vary), or sparse subpolynomial compact parity energy; alternatively collision bounds/shifted-detector saving. Transfer retains T². [Coefficient norms/local inverses are insufficient](rh-killed-routes.md#moebius-coefficient-blindness); [short weights retain the last-scale defect](rh-killed-routes.md#short-weight-defect). Stronger central O(logT) energy needs bounded inverse-ζ′ residue mass. Finite/shallow exceptions remain.
- **Sources:** CDG:LogScaleHeckeDefect/{UnitWindowMinimumAndOscillation,LogPowerExceptionalWindows}; CDG:NearLineLogMean/{TwoSidedThetaMollifierTrap,DiscCorridorDivergenceAndDetectorSharpness,LongMoebiusSecondMomentRigidity}; APR:{LongMollifiersImplyCriticalClustering,PrefixCancellationAmplifiesTheZeroFloor,TruncatedMoebiusCollarAndBlindnessLaws}; MZF:{TheWidthIsReadInOneWindow,TheLastScaleSurvivesEveryShortWeight,TheLongMollifierPaysForNegativeMoments}; SSA:PoleFreeHypercubeBridgesToLongMollifiers [L].

<a id="li"></a>
### LI — Paired Li and prime–Gamma balances

- **Path:** Actual clock primitive lower bound / prime–Gamma history budget → RH.
- **Established:** Guarded history-zero set Z_S finite; RH iff Z_S=∅. RH⇔primitive eventually bounded below⇔Cayley–Li sign on primitive vectors. Alternative: for every ε>0, R(t)≥−C_εe^(εt) eventually. Li signs n≤314 from the [height67 proof](#finite-height) [L].
- **Open:** Pay budget at every guarded zero or prove one of those lower bounds/signs. Finite Z_S is not finite off-line ζ support.
- **Sources:** R:{LiEvenCrossActualClockTerminalHistory,LiEvenCrossActualClockGrowthLaw,LiEvenCrossActualClockPrimitiveNegative}; ALG:RHIsReflectionPositivityOfTheCayleyLadder [L].

<a id="sz"></a>
### SZ — Suzuki screw and shifted-kernel limits

- **Path:** Complete Ward/Abel residual bounded below/bounded → RH.
- **Established:** Literal first variation=complete Weil energy. Completed Abel source A_N bounded⇔RH; abs(A_N)≤C√N exp(−c·vkScale(N)). Aligned completed/core energy ratio≤Cexp(−c·vkScale(N)) [L].
- **Open:** Actual sup_(N≥2) abs(A_N)<∞, complete first-variation sign, or rectangular Ward lower bound. VK saving still leaves the √N scale; a vanishing normalized ratio supplies no bounded unnormalized residual.
- **Sources:** R:Suzuki/{SuzukiRectangularWardDefectBoundedness,SuzukiCriticalRHCompleteFamilyTransfer,SuzukiTransitionCoreAbelSourceMultiGateWeld,SuzukiTransitionCoreAlignedGammaCompletion}; M:SuzukiResidualVinogradovKorobov [L].

<a id="fzz-p--parity-delay-mellin-orientation"></a><a id="gauss-mayer"></a><a id="pm"></a>
### PM — Physical-model Haar approximation (FZZ-P)

- **Path:** Faithful scattering source → Krein/Lewis positivity or pole/escape exclusion → RH.
- **Established:** Krein positivity⇔RH; actual-core Haar admission⇔ζ(2s)=0 for 0<Re s<1/2, Im s>0. Completed identity Q(H)=2Re[WH,WH] [L]; physical cusp residue=Krein square, Gaussian residue→complete Weil form [K]. At upper resonances, D_s≤0, with equality iff Re s=1/4. Boundary Maass–Selberg norm proves ζ nonvanishing on Re w=1 away from the pole, and upper-boundary scattering modulus1 [L].
- **Open:** Independent arithmetic D_s≥0 at every upper resonance, or full renormalized Krein positivity; physical mixed-parameter realization and signed descent. [Raw norm is not this sign](rh-killed-routes.md#mayer-krein-sign); [full spectral-determinant reflection fails even after λ-independent scalar repair](rh-killed-routes.md#mayer-spectral-reflection).
- **Sources:** RIT:MayerScattering/{MayerResonanceCharacterization,TheHeckeEquivariantCompletion,ArithmeticDefectObstructionAndReflectedCuspLaw} [L]; RIT:MayerScattering/{GaussianPhysicalCuspResidue,TheRetainedHeckeChannelReadsTheQuarterLine} [K]; RIT:{GaussMayerBoundaryNorm,GaussMayerArithmeticReflectionTraceObstruction} [L].

<a id="candidate-ptr"></a><a id="ptr"></a>
### PTR — Cosine-source zero-loss / photonic realization

- **Path:** Actual A_h=cosTransform(Φ cosh(hu)) → collision-free descent in h → RH.
- **Established:** Exact sech handoff to Ξ; strict Laguerre sign A_h′²−A_hA_h″>0 for h≥1/2, and for large abs(x), h>1/2−vkHadamardWidth(abs(x)+1). Sign at every 0<h<1/2,x∈ℝ⇔RH; real double-zero exclusion suffices [L].
- **Open:** Extend strict sign/collision exclusion below the VK boundary at every height. Independent prime-faithful lossless stack remains unconstructed; generic stack positivity does not prove the source inequality.
- **Sources:** R:{XiCosineShiftExceptionalPointCriterion,XiCosineShiftStrictLaguerre,XiCosineShiftSechHandoff,PhotonicLosslessWindowRH}; ZCG:CosineProducerStrictWindow [L].

<a id="jas"></a>
### JAS — Joint ancestry

- **Path:** Prime-product positivity or subpower bounds on moving finite power windows → RH.
- **Established:** For every ε>0, bounds abs(Riesz(m²,k))≤m^(εk), m<k≤m+m/log(m+1), on infinitely many m⇔RH. Finite-support admission and growing logarithmic-budget positivity.
- **Open:** Uniform arithmetic control on that moving k-window, or square-root prime-product budget. Finite admission supplies neither.
- **Sources:** R:JointAncestryLevelOneCapstones; R:JointAncestrySquareShellFinitePowerCriterion.

<a id="ctf"></a>
### CTF — Chronological tail / Báez–Duarte approximation

- **Path:** Finite-row approximation / averaged-current control / Möbius defect / BSY sign or mollifier infimum1 → RH.
- **Established:** RH⇔real unit-bounded rows reach every error tolerance. Dyadic linear-taper subpolynomial defect⇒RH. Sharp μ defect D_y≥c_ρy^(2Reρ−1); sparse subpolynomial D_y⇒RH. BSY sign I≤0⇔RH. For E_N=ζM_N−1 on the line, RH⇔∃ν>0∀τ∈ℝ∀ε>0, arbitrarily large N give meas{t∈[τ−1,τ+1]:abs(E_N(t))≤N^ε}≥ν. Sharp-defect/compact-parity bridge to [WD](#wd), with fixed K=3 [L].
- **Open:** Produce vanishing-error rows, sparse subpolynomial defect, BSY sign, or the uniform positive-proportion condition above. Exact [AIF infimum](#aif) is exp(2I(1)); RH needs budgets arbitrarily close to1, not merely to that unknown infimum [S]. Averaged-current branch needs arbitrarily large X with M>X and abs(Re current(X,M,ρ))≤BX^ε for each ρ,ε>0. [Full sharp-sequence decay fails](rh-killed-routes.md#sharp-mobius-defect); [good-height restriction retains the zero-forced exponent](rh-killed-routes.md#mollifier-good-set).
- **Sources:** R:{ChronologicalRiemannEquivalence,EulerDeletionCutoffAverage,BalazardSaiasYorCriterionEquivalence}; APR:{TheMollifierDefectIsASawtoothForm,TheLinearMollifierIsTheChebyshevError,PrefixCancellationAmplifiesTheZeroFloor}; MZF:TheExponentOfTheMollifiedErrorIsRigid; SSA:PoleFreeHypercubeBridgesToLongMollifiers [L].

<a id="hcf"></a>
### HCF — Gaussian heat trace / critical feature variance

- **Path:** Exact arch−prime heat trace → both prime-log grids positive at every degree → RH.
- **Established:** Heat explicit formula and two-grid RH criterion at independently fixed offsets. Absolute heat mass≤6/h; every off-line zero gives a pole-annihilating negative test on log2 or log3. Detector degree explicit from the finite outer spectrum; [verified-height transfer](#finite-height) gives conditional finite-degree positivity [L].
- **Open:** Nonnegative source moment functional on every real polynomial square annihilating the pole, on both grids at fixed offsets; alternatively bounded prime chirp on one vertical line. All degrees, not all offsets, are required. Spectral separation still controls detector degree.
- **Sources:** R:{XiGaussianHeatTwoPrimeSourceSampling,XiGaussianHeatPrimeChirpReceiver,HeatGridAliasingBoundary}; S:EffectiveHorizons/{TraceHankelDegrees,HeatGridDegrees} [L].

<a id="xn"></a>
### XN — Xi Newton invariant discs

- **Path:** Actual Xi first jets → line-centered self-map discs covering every zero → RH.
- **Established:** Coverage/self-map and closed-margin criteria; self-mapping supplies holomorphy. Margin M_(c,r)=r²abs(ξ′)²−abs((z−c)ξ′−ξ)² has nonnegative Laplacian. Local polynomial damping cancels poles while preserving root first jets [L].
- **Open:** Cover every ξ zero by a disc centered on Re c=1/2 with M_(c,r)≥0 throughout. Boundary sign does not control the interior minimum; local pole cancellation supplies no self-map bound.
- **Sources:** R:{XiNewtonDiscSourceMargin,XiNewtonDiscCurvature,XiNewtonCriticalPoleExclusion,XiNewtonScalarDamping} [L].

<a id="bag"></a>
### BAG — Deterministic zeta self-return

- **Path:** Actual ζ self-return / uniform twisted-head target mass → RH.
- **Established:** Strong recurrence⇔RH; actual-flow/head-target transfer proved. On every doubled disc inside 1/2<Re s<1, cutoff-uniform positive Haar target mass at every tolerance⇔RH. Weaker paired criterion: all-zero approach to the line at each fixed depth AND arbitrarily high returns on off-line-zero discs.
- **Open:** Uniform positive target mass as cutoff→∞; alternatively both inputs of the weaker criterion. Zero-free-target universality and density-one clustering do not supply them.
- **Sources:** R:{ZetaStrongRecurrenceOnCompactSets,ZetaTwistedDirichletHeadsApproximateZetaWithPositiveHaarMassIffZeroFree,ZetaDiscRecurrenceIffUniformHeadTargetDensity,ZetaWeakRecurrenceLadderCollapse} [L].

<a id="ewu"></a>
### EWU — Even pole-weight uniqueness

- **Path:** Even blind minimum≥0 at every aperture → even positivity → RH.
- **Established:** Weight rigidity; attained blind minimum≥1/20 for a≤(log2+1/50)/2. Even sign⇔−C≤Q⇔Hamburger moments; neutral gauge reduces sign to jump energy≥2·charge variance. Moving neutralizing pockets conserves outside deficit. Sign-gauge balance iff c≤logρ, ρ³=ρ+1 [L].
- **Open:** Blind minimum≥0 beyond that proved interval; pay variance with complete signed jumps. Outside-window negative conductances and Perron saturation-gap/height control remain; [entry transfer](#prime-entry) requires a margin.
- **Sources:** R:{EvenSectorPoleWeightUniqueness,EvenSectorBlindVariationalAttainment,EvenSectorBlindMinimumSmallAperturePositivity}; SWC:{TheParitySectorsAreTheBandAtTheCentre,NeutralThetaGaugeOptimizationAndPrimeFourSliverFrontier}; SWC:PerronSignLaw/ThePerronMarginIsBoundedByThePoleSaturationGap; FADF:{SignedThetaGaugesReverseTheEvenDeficit,FrustrationCannotBeSwitchedAway} [L].

<a id="gta"></a>
### GTA — Transverse Schur charge

- **Path:** Actual theta-stage quartic charge → arbitrarily small cofinal packets / compact full-mode operator → RH.
- **Established:** Canonical Schur family, strong finite-prefix convergence; full-mode compactness and finite-prefix operator-norm convergence each⇔RH. Cofinal arbitrarily small charge suffices. Late packets have charge≤stage Hilbert–Schmidt mass/400; small-spectrum charge≤(150δ²+425δ³/4+ε)·HS-ceiling², δ cuts squared spectral size [L].
- **Open:** For every ε>0,N, some k≥N admits charge<ε. The fixed 1/400 ceiling does not vanish; small-spectrum suppression leaves the large spectral nodes. [Ordinary skew-adjoint energy does not decay](rh-killed-routes.md#theta-skew-floor).
- **Sources:** R:{PaperThetaSchurModeCharge,PaperThetaSchurIdealClassification,PaperThetaSchurFiniteStageLimit}; R:Hedenmalm/HedenmalmThetaSchurQuarticAsymptoticZeroTransfer; S:EffectiveHorizons/ThetaSchurParabolicCharge [L].

<a id="owu"></a>
### OWU — Odd Weil-weight uniqueness

- **Path:** Actual odd polar-hyperplane Weil positivity at every aperture → RH.
- **Established:** Odd RH criterion; prime-free and moment-constrained unit-window floors [K]. Odd sign⇔C≤Q⇔shifted-jet Hamburger moments. Trivial-zero squares split into reflected Dirichlet energy minus mirror killing, paid by Lévy edge energy. No sign gauge removes an acting negative prime antidiagonal; at sufficiently large apertures, this frustration holds throughout each admitted full-positive weight cone [L].
- **Open:** Joint sign for every compact C² real odd F with ∫F(x)sinh(x/2)dx=0; this restricted family already implies RH. [Prime3](#prime-entry): collar-mass replacement fails for c≥287/500; deleting its signed term gives a negative odd test for c≥3/5 [L]. Outward-edge bounds still need a margin; [retained-variance payment](#act) remains open.
- **Sources:** R:WeilMarkovOddPositivity; B:OddSectorPolarHyperplaneAndPoleWeightSynthesis [L]; WTZ:TheHigherGammaReserveRepairsTheQuadraticCutoff [K]; FADF:{TheCentreReflectsTheTrivialZeros,FrustrationCannotBeSwitchedAway}; SWC:{TheSectorsAreTheMomentConditionsOfTheJets,TheCollarRatioIsSharp} [L]; SWC:BelowLogFour/TwoProfileRefutationBelowLogFour [K]; CHT:TheBandsOfTheCone [L].

<a id="pbm"></a>
### PBM — Regularized prime/log-ζ abscissa

- **Path:** Actual pole-regularized prime/log-ζ Dirichlet convergence for every σ>1/2 → RH.
- **Established:** Exact convergence/RH equivalence; prime-power difference controlled at square-root-plus-ε scale.
- **Open:** For g_n=(Λ(n+1)−1)/log(n+1), prove abs(Σ_(n<N)g_n)≤C_ε(N+1)^(1/2+ε) for every ε>0. Prime-count variant has the same threshold; regularization supplies no cancellation.
- **Sources:** R:{RegularizedLogZetaAbscissa,PaperPrimeRegularizedIdeal} [L].

<a id="rb"></a>
### RB — Robin/Nicolas divisor-sum criterion

- **Path:** Eventual extremal divisor-sum/primorial inequality → RH.
- **Established:** Eventual Robin/Nicolas criteria without a Θ<1 premise; colossally abundant and lcm(1,…,n) reductions; growing-prime-core constraints.
- **Open:** Eventually σ₁(n)<e^γ n loglog n on colossally abundant n; alternatively robinLcmDefect(n)≤1/(√n log n). Necessary divisibility conditions do not exclude counterexamples.
- **Sources:** R:{RobinColossallyAbundantReduction,RobinLcmRiemannCriterion,NicolasInequalityRiemannConverse}; B:RobinMovingValuationDefect [L].

<a id="srt"></a>
### SRT — Prime-side one-parameter lag localization

- **Path:** Complete atomic-family sign / horizon-layer sign / late-lag bound → RH.
- **Established:** Full-family/index receivers; terminal correction pole-attained, zero on a nontrivial kernel [K]. All-height/depth negative-test horizons without separation/simplicity; split-column receiver a>πD_on+πD_off/2. Actual ζ depth≥exp(−c log³T) gives a negative test at aperture λlog(T/2π)/2, λ>1; starting height [explicit](#finite-height) for λ≤2 [L]. General tempered configuration: positivity at a, remaining depths≤σ and multiplicity≤K per cell of length2π/ℓ, ℓ>2a, force k·pairEnergy(δ,a)≤(Kℓ/2)e^(2(2π/ℓ+σ)a) for a depth-δ site of multiplicity k [S].
- **Open:** Complete prime-side two-bump sign for every centre, lag and parity; alternatively all-window horizon sign. Complement/source-kernel payment remains. General visibility needs microscopic cell/depth control, not coarse RvM counts. Local logarithmic counts plus positivity at (logT)/36 permit fixed-depth countermodels [L]. [Mixed-column boundary](rh-killed-routes.md#mixed-column-threshold); [cut-crystal boundary](rh-killed-routes.md#kr-crt).
- **Sources:** S:AnExplicitClusterDetectorConstant; S:EffectiveHorizons/XiZeroMass [L]; AHD:{TheHorizonCriterion,TheCompleteCriticalResidueIsSupportedAtThePole,CriticalWindowsSurviveLowConductorRemoval} [K]; S:EvenAndOddTwoBumpTestsDecideTheCriticalLine; [distinct-cluster threshold](../../formal/GaloisForLFunctions/WindowVisibilityLaw/DistinctCoherentClustersHaveTheMultiplicityThreshold.lean), [split-column laws](../../formal/GaloisForLFunctions/WindowVisibilityLaw/SplitColumnThresholdAndPerturbedFragility.lean), [contact laws](../../formal/GaloisForLFunctions/WindowVisibilityLaw/ShallowClusterExclusionAndTaperedCrystalBarrier.lean) [L]; ZCG:NegativeTests/{SharpLocation,SharpLocationHeight} [L]; [general visibility](../../formal/GaloisForLFunctions/WindowVisibilityLaw/TheUniversalVisibilityThreshold.lean) [S]; [shared frontier](#shared-frontier).

<a id="act"></a>
### ACT — Arithmetic criticality / single-shift variation

- **Path:** One fixed shift pays every even compact C² profile → odd Weil positivity → RH.
- **Established:** Single-shift receiver; Ẑ(m_au)=2S_a−D_a+8V_c+8τ_cA₂, V_c≥0, τ_c>0. Joint neutral-even/retained-odd certificate⇔reflection band; for2c<log5 only {2,3,4} can enter. Their outward kicks cost<991/1000 of Lévy energy; full reflected-pair floor1/(20000·2^k) holds through a_k from [RW](#rw) [L]. Variance-free certificates fail for c>273/400 [K].
- **Open:** One shift, uniform in profile/support, paying reflected-prime D_a with same-side energy and retained variance/slack. Actual-weight band membership remains open; [prime-entry transfer](#prime-entry) requires a sector margin. [Specific floor tower is bounded](rh-killed-routes.md#frozen-weil-floor-tower) [L]. Variance-dropping fails [K].
- **Sources:** D:{SingleShiftCompleteness,ShortProfilePoleFreeVariationInequality}; I:ShiftedCollarsHaveExplicitPaymentThresholds; SWC:{ShiftedGroundStatesArePoleChargedOnEveryWindow,NeutralThetaGaugeOptimizationAndPrimeFourSliverFrontier} [L]; SWC:BelowLogFour/{TwoProfileRefutationBelowLogFour,RetainedVarianceAndHalfWindowBandBelowLogFour} [K].

<a id="aip"></a>
### AIP — Arithmetic incidence positivity

- **Path:** Complete reflected-prime/pole allocation → subexponential signed cost or full-space sign → RH.
- **Established:** Exact allocation/decomposition; full odd signed cost≤Kexp(r−c(2r)^(3/5)(log(2r))^(−5/3))·Sobolev mass for large r [L]. Small-K full-space and all-R growing low-block positivity; capacity=loglogN+O(1) [K]. Receiving modes have bounded charge, vanishing physical energy and growing existential cutoffs [L].
- **Open:** For every σ>0, abs(reflectedPrimePolarCost(F,r))≤C_σe^(2σr)(¼∫F²+∫F′²) for every odd compact C² F supported in [−r,r]; equivalently appropriate uniform allocation deficit. Packet branch still needs effective RH-complete schedules and full complementary Schur/four-channel payment.
- **Sources:** I:{GlobalIncidenceAllocationCondition,ReflectedPrimePolarAllocation,VinogradovKorobovSignedCost}; CSAR:ReceivingCharges/GrowingSimultaneousReceivingModes [L]; ACPL:ReceivingCharges/PrimeIncidenceCapacityGrowth [K]; [shared frontier](#shared-frontier).

<a id="inter-tower-coupling"></a><a id="coupled-tower-signature"></a><a id="sc"></a>
### SC — Stokes/Witt–Krein / archimedean successor

- **Path:** Glued affine Weil index≤1 / bounded Gaussian-damped two-prime kernel coupling → RH.
- **Established:** Glued index=κ_ζ+1; complete-matrix receiver. Fixed spline: sublinear-in-order tensor loss implies RH. Gaussian-damped ℕ² coupling has rate≤σ iff zero width≤σ; bounded coupling⇔RH. Exact normalized heat-average representation retains the full arithmetic prime+Gamma+pole spline source, with integrability and sum exchange [L].
- **Open:** Arithmetic bound for damped coupling, sublinear tensor loss, or glued index≤1/complete pole-hyperplane sign. Linear-in-order tensor loss only repeats the existing width bound. √Y-normalized prime–pole decay supplies no zero rate; [undamped coupling plus full RvM counts admits off-line model divisors](rh-killed-routes.md#coupling-growth).
- **Sources:** AKG:TheGluingFormulaAtEveryPlace; AKG:TowerCoupling/CoupledTowerSignatureFormula; CP:TheBaseIsAFixedLoss; ACPL:ConeBoundary/{GaussianConeKernel,PolynomialBoundaryRepulsion,TheGaussianCouplingIsAnArithmeticHeatAverage}; ACPL:ConeMoments/RVMCompletedSplineDivisor.

<a id="lattice-sections"></a><a id="acs"></a>
### ACS — Arithmetic Castelnuovo–Severi effectivity

- **Path:** Explicit Gamma/Lévy/horizon/Chebyshev source energy → all-aperture Bézout → RH.
- **Established:** Exact source cone/all-aperture Riemann–Roch; Bézout/ampleness⇔source-energy sign⇔RH. Primitive h¹≥‖f‖²/10000 and Künneth effectivity for a≤181/500. Finite curves: tensor-uniform growth⇔purity⇔deciding-window sign; rank-R purity⇔first R margins positive, with E_R=0. Finite virtual traces nonnegative at every positive power bound negative-spectrum radius by positive-spectrum radius. Odd-prime Kloosterman fibres have pure window receivers identifying every extension trace [L]. For b≠0, global degree-(m+1) moment=q(qA_m−B_m), q=card F; B_m counts 1+Σx=0, A_m also requires 1+Σx⁻¹=0 [S].
- **Open:** criticalDeficitSourceEnergy(r,(0,0,f))≥0 for every r>0, f∈realTestsAt r. Independent arithmetic count/height/Rosati production remains. Global-trace approach needs actual domination and tensor-uniform growth; finite-field calibration does not construct ζ's trace. [Weights](rh-killed-routes.md#invariant-tensor-weights), [endpoint positivity](rh-killed-routes.md#principal-endpoint-weights), [pure compression](rh-killed-routes.md#monodromy-compression).
- **Sources:** G:{ExactArithmeticSourceEffectivity,TheWindowReceiversOfACurve,Representation/EndpointCalibration}; LST:ThePrimitiveH1IsCoerciveAtSmallDegree; KPA:RiemannHypothesisIsTheRealityOfTheLegendreInvariant; AK:WeightFamilies/{CurveTensorReceivers,GoldenInvariantWeights,SplitWeilModel,CanonicalMonodromyCompression,PositiveGlobalTrace,KloostermanMomentHypersurface,KloostermanCurveReceiver}; GWZ:TheCanonicalFlowOfACurve [L]; AK:WeightFamilies/KloostermanMomentCounts [S]; SEL:{GammaIndependentEulerRigidity,DegreeGap,DegreeOneConductorPole} [K].

<a id="sec"></a>
### SEC — Adjacent prime seam / time-one Fock bound

- **Path:** Actual time-one prime–Gamma seam → factorial jet-energy bound at ξ zeros → RH.
- **Established:** Every open-strip seam is admitted in time-one Hilbert space; prime Dirichlet transform F_ρ identified. At any fixed x₀>1, RH⇔for every ξ zero ρ, sup_N Σ_(n<N) abs(F_ρ^(n)(x₀))²/n!<∞. Exact eventual adjacent compactness is an alternative receiver [L].
- **Open:** That bound at actual zero parameters; bound may depend on ρ. Hilbert admission and asymptotic seam smallness, even Euler-rescaled, do not imply factorial-Fock boundedness or exact compactness.
- **Sources:** R:{TimeOneGammaJetFockRHCriterion,XiPrimeSeamSparseEdgeCalkin,XiPrimeSeamAdjacentEssentialNormNoGo} [L].

<a id="cdc"></a><a id="bsh"></a>
### CDC — Constitutive dagger / BSH mate curvature

- **Path:** Actual source-metric gain → marked-repair equality / purified-curvature vanishing at ξ zeros → RH.
- **Established:** Actual Euler-face metric and purified gain constructed; curvature identification and calibration unconditional. Canonical potential fixed before zero selection. At N=1,n=2, equality of its two marked repair values at every ξ zero suffices; BSH purified-curvature zero is the same grade criterion [L].
- **Open:** RepairProofErasureConsistent for the canonical potential at every actual ξ zero, equivalently purified gain1. Full semantic descent is stronger than needed; neither metric construction nor finite trace identities force this equality.
- **Sources:** R:ConstitutiveDaggerConfluence; R:Deninger/{DeningerFailureNerveSingularCartierMetric,DeningerCalderonWittGammaTensorSquareMateIdentification}; S:TheZeroIndexedRoutesMeasureOneSide [L].

<a id="pcs"></a>
### PCS — Singular prime co-shift

- **Path:** Actual all-prime ground profile → reflection-odd singular class vanishes at ξ zeros → RH.
- **Established:** Concrete co-shift/ground profile; reflection-odd quotient class vanishing⇔RH. Finite-prime cutoffs converge strongly with persistent norm/ideal gap [L].
- **Open:** For every ξ zero ρ, (n↦n^(−ρ)−n^(−(1−conj ρ)))∈ℓ². Independent source differential forcing this remains unconstructed. CTF transport must retain the nonzero shift defect; injective literal intertwining is impossible.
- **Sources:** R:{PrimeCoShiftModel,PrimeCoShiftReflectionOddSingularCohomology,PaperPrimeCoShiftCofinalGap,PCSChronologicalDilationCarrierObstruction} [L].

## Route candidates

Promotion requires the missing independent source mechanism/landing below; an unproved final estimate alone does not make a live route a candidate.

| Candidate / intended path | Established [L] | Promotion gap | Sources |
|---|---|---|---|
| <a id="apf"></a>**APF — Arithmetic paired Fredholm:** prime source → divisor exhaustion → trace vanishing. | Signed source-first cycles and countable prime/grade/cap trace reconstruction. Existing receiver samples real Ξ-labels −2π·grade/log p. | Independent full-divisor exhaustion/RH landing; real-label reconstruction does not detect or extinguish arbitrary off-line zeros. | R:CCM/CCMArithmeticPrimeFredholmTrace; R:PaperPrimeFredholmReconstruction [L] |
| <a id="egc"></a>**EGC — Pole-safe contour:** correction → outer covariance/sign. | Double Gaussian contour realizes complete zero-pair sum on fixed rectangles; cofinal admissible contours and vanishing mass-subtracted inner remainder. Raw Gamma baseline persists [L]. | Height-fibre isolation/global outer landing into an RH-sufficient observable. Inner cancellation counts every enclosed copy; raw tail decay is not selective. | R:{XiEntireGaussianReflectionFibreCovariance,PaperEGCEnclosedPoleCancellation,PaperEGCSourceRayBaseline} [L] |
| <a id="ewj"></a>**EWJ — Euler/Wold jets:** faithful source reporter → endpoint sign. | All-depth reporter, compact-quotient character and Ξ-multiplicity transport; strong prefix convergence. Norm exhaustion iff c=0 or −a+b+2d=0. | Source-faithful endpoint admission outside the blind plane. Existing endpoint/transverse lanes retain positive essential gaps; their norm exhaustion is false, not merely unproved. | R:{PaperEulerWoldDepthHistory,PaperEulerWoldDepthCompression,PaperEulerWoldCompactCharacter} [L] |
| <a id="fel"></a>**FEL — Theta likelihood:** predeclared arithmetic history → calibrated contrast → BSY sign. | Probability/KL and conditional entropy accounting. Actual BSY sign criterion is live support under [CTF](#ctf). | Construct and calibrate a predeclared source/history that forces the BSY sign or another RH receiver; adaptive bookkeeping does not instantiate it. | R:PaperThetaObservationHistory; R:ZetaCriticalLineJensenInequality [L] |
| <a id="irk"></a>**IRK — Rotation-algebra trace:** arithmetic defect → K₀/Chern count → orientation. | Integral native finite-idempotent traces; actual Meyer–Ξ finite free resolution; completed relation and boundary trace classification. | Source-faithful projective/descent construction identifying analytic trace with Chern charge. Free resolution is not projectivity; current interface assumes these identifications. | R:{PrimeRotationCanonicalTraceIntegrality,PrimeRotationXiCompletedResolution,PrimeIrrationalRotationKZeroRH}; R:Deninger/DeningerMeyerPrimeRotationResolution [L] |
| <a id="msc"></a>**MSC — Möbius−Sonin transport:** squarefree Hilbert source → Sonin sign. | Unweighted critical discrepancy is in L²; summatory transport preserves strict-right divisor multiplicity/conormal. | Source-faithful Sonin/Weil-sign landing. L² admission and divisor preservation supply no sign; literal-column Bessel realization is confined to Re ρ>1. | B:SquarefreeUnweightedHilbertSource; R:Hedenmalm/{HedenmalmSquarefreeSummatoryConormalTransport,HedenmalmGammaSewnSquarefreeFisherBesselHilbertStabilityWall} [L] |
| <a id="rfhm"></a>**RFHM — Support grade:** faithful phase/depth source → arithmetic orientation. | Full support/phase/grade admission, native forward creation and strong cutoff exhaustion. | Source-defined phase/depth/compound law with RH-sufficient wall orientation. Energy-only statistics lose gain/grade; literal positive-coordinate ancestry sewing kills nonempty-support outputs. | R:{GammaThetaFullSupportSource,GammaThetaFullSupportCreation,PaperRFHMSurvivalInformation,JointAncestryCPrimeTorusRFHMSewingNoGo} [L] |
| <a id="w1c"></a>**W1C — Clifford–Dirac / centred Lee–Yang:** arithmetic operator or ferromagnetic limit → real-rooted Ξ. | Finite ferromagnetic Lee–Yang receiver; convergence to Ξ/Ξ(0) on one real interval suffices. All-moment convergence also suffices [L]. Mayer realization belongs to [PM](#pm). | Construct an independent sequence of finite nonnegative couplings/masses with that interval convergence, or a positive arithmetic reflection form with self-adjoint generator. Neither producer is supplied; slow-field convergence is not required. | R:{LeeYangIsingGraphDatum,XiIntervalLaguerrePolyaRH,IsingMomentConvergenceRH} [L] |
| <a id="wbf"></a>**WBF — Source certificates:** arithmetic stream → positive completion → Ξ. | Native Gram determinants recover exactly coefficient magnitudes/phase-gauge class; relative completion iff Hilbert–Schmidt weight. | Arithmetic certificate stream and source-faithful Ξ/Weil landing. Generic completion and magnitude recovery do not supply arithmetic phase orientation. | H:{PaperGenealogyFredholmRecovery,PaperGenealogyDeterminantGauge,PaperCriticalGenealogyCompletion} [L] |

## Shared frontier

<a id="first-overlap"></a><a id="relative-prime"></a><a id="physical-prime-defect"></a><a id="prime-centered-output"></a>
### Atomic positivity — RW, HF, SRT, AIP, ACS, SC

Critical ratio R=c⁸/logN; tilted spline has spectral order7. Other profile limits require C² support [0,1], positive square mass, Fourier-square decay exponent>4 and regular positive spectral tail. Families fixed unless stated.

| Established | Open / scope | Sources |
|---|---|---|
| Unit physical mass gives coefficient norm O(c⁴). Under strong L¹ convergence to F, critical high-frequency mass has the sharp weighted lower bound proportional to ∫_(-A)^0 F²e^(−8y); valid along subsequences. Below-grid error²≤C(c²r³/N²+1/r) [L]. | Produce strong limits for the actual moving sources; lower-bound recovery alone supplies no compactness or complementary sign. | AHD:{AtomicSynthesisRetainsItsMixedMass,TheSynthesizedProfileIsRecoveredBelowTheGrid,TheHighAliasingHasItsPhysicalDualFloor} [L] |
| W₈=∫H²e^(−8y) bounded by seventh-weighted collar mass; prime form≤εW₈+B_ε‖H‖². L¹ tails decay e^(−4A), prime polar tails k^(−9/2). Terminal logarithm has squared exponential dual mass≤1. Physical/Fourier tightness gives L² precompactness. Prefix L¹ mass²≤C_φP/c, P=prefix coefficient square mass [L]. | Uniform tail/energy bounds for actual critical sequences; prefix disappearance still needs P=o(c). Abstract compactness retains both tightness premises. | CACT:{ThePhysicalCollarHasBoundedExponentialMass,PrimeShiftsAreInfinitesimalInTheExponentialWeight,ExponentialMassControlsLaplaceTails,PhysicalAndFourierTailsGiveCompactness,ThePhysicalPrefixHasSmallL1Mass,ThePolarLogarithmHasFiniteExponentialDualMass} [L] |
| Full tilted-spline matrix positive for every subcritical exponent<1/8 [L], and through one fixed small multiple c≤2K₀(logN)^(1/8), with complete Schur payment [K]. | Every K>0. Losses R and R² persist; increasing N does not pay them. | CACT:{TheCompleteWeilMatrixIsPositiveDefiniteBelowTheEighthRoot,CriticalMultipleCompleteWeilPositivity}; SSHA:EveryEighthRootMultipleReceivesTheTiltedSpline |
| Every fixed independent mean-zero periodic joint family eventually PD at every ratio. Distinct primitive conductors>1 decouple at critical second order for common profiles, without parity restriction [L]. | Growing families/periods, coalescing frequencies and untwisted sign. Fixed-family positivity is not a full-space floor. | AHD:{JointPeriodicWindowsInheritThePolarization,PrimitiveCharacterConductorGrading,EveryFrequencySectorInheritsThePolarization} |
| Critical pencil=κWeil+(7J/R)weighted Gram. Tower windows A≤2a_k positive at every R. Exact-clock inertia=(n₊,n₋+n₀,0); null directions enter negatively [L]. | All apertures and growing complements; actual nullvector existence. This specific tower has a_∞<0.3621, not aperture exhaustion [L]. | AHD:{EveryCriticalRatioIsPositiveOnALargerWindow,TheCriticalBoundaryAddsItsNullDirections}; I:{MultiPrimeDilationModulusAndIteratedWeilFloors,TheWeilFloorTowerIsFrozen} [L] |
| Window index counts locally finite critical lengths; RH requires every critical length infinite. Single-prime transport⇔RH; prime2 modifies every test to a positive one [L]. | Arithmetic index ceiling; corrected-test sign does not prove original-test sign. Larger-prime transport retains an untouched head. | CWS:TheWindowIndexCountsCriticalLengths; AHD:{TheWindowIndexCountsTheRightZeros,MultiplicativeConvolutionHorizonAndTailCancellation} |
| Every fixed R>0: low packet m≤Q=⌊(logN)^(13/32)⌋ has positive diagonal plus polar genus, uniformly in coefficients. Removal preserves compensated window limit [K]. | Intermediate/far bands and mixed Schur payment. Full-horizon reference-energy floors fail, even for nonnegative coefficients. | CACT:TheCriticalLowPacketRetainsItsSignedPolarPart; AHD:CriticalWindowsSurviveLowConductorRemoval; [boundary](rh-killed-routes.md#full-conductor-diagonal) |
| Terminal source S_A is polar; inverse-energy mass→S_A²R/J₁ through Q. Optimal gain=S_A²/(J₁/R+κg), g=2+γ−log(4π), zero on ker S_A [K]. Far-complement bound retains one quarter of top archimedean energy and one eighth of dyadic aliasing reserve after window payment [L]. | Kernel energy, conductors beyond Q, growing apertures. O(c) and ratio-dependent losses still need joint payment; retained archimedean energy does not yet remove the large-R obstruction. | CACT:{EveryLowPacketCorrectionHasItsPolarCapacity,TheFarReserveRetainsArchimedeanEnergy}; AHD:TerminalPolarSourceHasANontrivialKernel |
| Capacity=loglogN+O(1) [K]. Each K admits growing bounded-charge receivers: exact coordinates/neutrality, physical energy→0; M=R(X)!X²≤X³, horizon X⁴⁰ [L]. Complementary pairing→t/80; corresponding two-dimensional Schur span positive [K]. | Effective cutoff rate and full complementary payment. Vanishing input energy does not imply vanishing complementary coupling; cutoff and horizon cannot be identified. | ACPL:ReceivingCharges/PrimeIncidenceCapacityGrowth; CSAR:ReceivingCharges/{GrowingSimultaneousReceivingModes,PrimeChargeSchur} |
| Complete signed incidence decomposition and centered/upward/cofactor estimates proved; Mertens channel norm≤log8+4 [L]. | Joint four-channel smallness at critical scales, including small/offset-dividing primes. No fixed linear charge² bound from combined adjunction/norm/physical-energy costs. | ACPL:ReceivingCharges/{MixedChannelDecomposition,MixedChannelBounds}; CACT:ReceivingCharges/{LiteralThreeRange,UpwardCentering}; [cost boundary](rh-killed-routes.md#prime-pole-cost) |
| <a id="prime-entry"></a>Admissible weight fibres closed/bounded/convex. At entry δ=2c−log n↓0, allowed variation scales with an existing margin·√n log(1/δ). Absolute edge cost crosses1 at c*∈(½log5,½log6]. Below2c<log5, {2,3,4} outward kicks cost<991/1000 of Lévy energy [L]. | Actual Λ-weight membership and full sector margin; fibres may be empty. Signed Hankel/pole/variance payment remains beyond tower floors. | FADF:{TheEntryConstantIsOne,TheEdgeLawCrossesOneBetweenLogFiveAndLogSix}; SWC:NeutralThetaGaugeOptimizationAndPrimeFourSliverFrontier; [absolute boundary](rh-killed-routes.md#absolute-edge-payment) |
| Window sign⇔all fitting lattices; all-lattice sign⇔RH∧λ=Λ. Even/odd jet sign⇔Hamburger moments; full sign⇔Stieltjes moments [L]. Retained-variance certificates below log2⇔convex {2,3} band [K]. | Actual positive measures/all-aperture band. Gamma-only derivative monotonicity omits prime/pole costs; variance-dropping fails. | GWZ:{AWindowIsTheUnionOfItsLattices,TheLatticeSelectsTheVonMangoldtWeight}; SWC:{TheSectorsAreTheMomentConditionsOfTheJets,BelowLogFour/RetainedVarianceAndHalfWindowBandBelowLogFour} |
| Every compact C² profile of positive square mass: energy≥a·e^(−Bc)‖x‖² on conductors≤N^θ, every 0<θ<1/4, for 1≤c≤b·loglogN; a,b profile-dependent, B universal. Subpolynomial spans admit super-log-log positive clocks. Fixed Beurling profile at c_N=2L(logL)², L=loglogN, has sign⇔RH [L]. | Full complement at an RH-complete schedule. Positive profile-dependent clocks do not prove the prescribed Beurling schedule or every eighth-root multiple. | CACT:{EveryProfileIsPositiveAtLogLogOverlapOnPolynomialSpans,EverySubpolynomialSpanHasASuperLogLogPositivityClock}; RIT:TheHodgeIndexAtCriticalOverlap |

<a id="finite-height"></a>
### Finite-height transfers — PA, LI, HCF, LA, TH, RW, SRT

Assuming `RHVerifiedThrough T`: Li n≤4.7T; Hausdorff k+1≤1.5(T−1), r≤RT³; heat-grid degree+1≤T/4800; Jensen degree d with 2·10⁷d⁴≤TlogT; central PF k+1≤3T. Each retains its lower-height threshold. Theta rank N, all 0<a≤3/4, needs verification through D(N+1)³+1. Height67 verification gives PF₂₀₀, Li signs n≤314 and all ξ-slice coefficients≥0 for abs(t)≤133/2 [L]; arbitrary-height verification remains open.

Sources: VHR:{LiAndHausdorffEntries,HeatGridEntries,JensenEntries,PolyaFrequencyEntries,ThetaEntries}; S:EffectiveHorizons/LowHeightGammaPF54; VHR:HadamardBudget/TheVerifiedHeightSixtySeven [L].

RW/SRT: `RHVerifiedThrough (windowHeight a)`⇒complete Weil sign on every C² test supported in [−a,a]. Pole-preserving normalized smoothing, verified-zero sampling and high-zero tail payment closed [L]. Actual verification at these explicit heights, or independent all-window sign, remains open. VHR:WindowEntries [L].

SRT detector starting height≤2πexp L(λ,c), where L=max{4/(λ−1),7Ωlog(792Ω²/(λ−1))}, Ω=2.2·10¹⁷(c+51395), 1<λ≤2,c≥0. Window sign at a forces depth<exp(−c log³T) for 2πexp L(2,8c)≤T≤2πexp a. Actual window sign remains open. ZCG:NegativeTests/SharpLocationHeight [L].

Edge Fejér budget: at a=1/2, L>0, γ≥4, off-line zeros force 2(2−4(1−e^(−L/2))/L)≤archBudget−primeSum. Finite support log n<L permits continuity to coefficients Λ(n)/n. At L=3 the prime polynomial≥−0.7278; combined budget excludes off-line zeros through height67 [L]. Unbounded-height strict reverse estimates remain open. VHR:HadamardBudget/{TheFejerBudget,TheBudgetAtTheEdge,TheVerifiedHeightSixtySeven} [L].

<a id="external-literature"></a>
### Scope guards

- RH-equivalent receivers are proved; their arithmetic positivity/cancellation inputs remain open.
- Finite off-line support is conditional, not established for ζ; it would not imply RH.
- Critical-line census: simple-critical proportion≥0.67250071−ε uses imported Zeta23 plus local IGP. Higher proportions need actual signed prime surplus/moments; model16/21 is not a ζ proportion. [Sub-threshold data, form-factor/pair-density positivity and F≥1 beyond threshold do not force the 75% certificate](rh-killed-routes.md#positivity-three-quarters) [L].
- Fixed aperture/rank/scale and density-one control leave finite or shallow exceptions. No uniform positive ground-energy gap at unbounded aperture.
- WD's long-mollifier receivers retain unproved moment bounds; neither critical-scale clustering nor finite off-line support is unconditional. Dyadic finiteness concerns only depth≥1/(2θ)+ε: CDG:NearLineLogMean/TwoSidedThetaMollifierTrap; APR:LongMollifiersImplyCriticalClustering [L].

<a id="pw-b"></a><a id="hb--theta-cusp-hawking-causal-scattering"></a><a id="isc-polar"></a><a id="art"></a><a id="dr"></a>
### Non-route labels

DR: [retired zero-freeness-based root construction](rh-killed-routes.md#dr); regional-root/multiplicity equivalence remains support, not an independent RH mechanism.

PW-B: [retired source-uniform extinction mechanism](rh-killed-routes.md#kr-pwb); surviving critical-line detector feeds PM/scattering. ISC-polar: rational Weyl pole-exclusion branch of PM/HF, not a separate route. BVI/ART: support. [Other killed mechanisms and retired aliases](rh-killed-routes.md).

<a id="aif"></a>AIF: CTF/FEL support. I(w)=Σ_(Reρ>1/2)m_ρG_w(ρ)≥0; I(1)=BSY integral. Actual ζ Szegő infimum closed: inf_(Q(0)=0)∫abs(ζ·exp Q(φ₁))²dP₁=exp(2I(1)). RH⇔∀ε>0 some budget<1+ε [S]. Open: near-unit budgets/inner-mass vanishing. These holomorphic mollifiers are not WD's long Möbius prefixes. [TheInnerFieldOfZeta](../../formal/GaloisForLFunctions/ArithmeticInnerFunctionTheory/TheInnerFieldOfZeta.lean), [TheInnerMassIsAMollifierInfimum](../../formal/GaloisForLFunctions/ArithmeticInnerFunctionTheory/TheInnerMassIsAMollifierInfimum.lean) [S].

Endpoint characters (ACS/HF/CTF): positive real-part alphabet gives coherent PSD characters; arithmetic matching⇔RH. Completed log-derivative jets recover every cycle value; independent coloring equals the cycle-product function on every permutation [L]. Literal arithmetic cycle-family positivity⇔RH⇔all common-pivot Gram tests positive [S]. Actual arithmetic positivity remains open. H:SymmetricCharacters/CycleCharacterIdentification; R:Representation/EndpointArithmeticMoments [L]; R:Representation/EndpointHankelReceiver [S]; [boundary](rh-killed-routes.md#endpoint-character-matching).

ADT: conductor degeneration supporting HF/ACS/SC; gluing determinant reformulates MC. AHD: horizon/index receivers within SRT/HF/SC. CWS: window locality/signed folds/index exhaustion within HF/RW/ACS; independent all-window positive realization open. See [shared frontier](#shared-frontier).

WTZ/DZG/ATD: RW/HF/ACS/PM support. Tate-positive dimensions=[0,κ(A)], κ(A)>0 and κ(A)→0; strict interior floor and exact rational-Hecke graph criterion [L]. Finite matrix reduction through A≤log(81/16); actual dimension1 sign through log(9/2). Atomic prime form satisfies abs(Σ_(k≤N)(Λ∗g)(k)g(k)/k)≤½logN·Σ_(k≤N)g(k)²/k [L]. Finite 2,3,5-closed templates containing1 fail at spread≥27/5 [S]; [boundary](rh-killed-routes.md#finite-hecke-template). First-jet domination⇔Weil sign; full-form all-aperture domination open. Sources: WTZ:{PositiveTateDimensionsFormAClosedInitialInterval,PositivePrimeMultipliersLowerTateDimension,TheTateHorizonBeforeEightyOneSixteenths,TheThirdTateStageDistinguishesEdgeSigns,TheAtomicLatticeHasTheSharpSchurBound} [L].

GWZ/CSTW: [RW](#rw)/AIP/ACS support. At log2<A<log3, complete-Weil sign reduces to one two-collar inequality, still open. Discrete Gram/flux and Riccati identities; next positive margin⇔contractive Schur kick, given previous positive margins. Finite-curve purity permits terminal contact; it does not prove ζ's contact exclusion. GWZ:{TheFirstStageComplementIsASchurComplement,TheLatticeAnchorFlow,TheCanonicalFlowOfACurve} [L].

<a id="mzf"></a>MZF: MC/WD/CTF/ZCG support. N(ρ)≤every finite Blaschke product [L]; at simple right zeros, N(ρ)=exp(−Σ_other m_aG_ρ(a)), with summable potential [S]. Let L=logT, x=(1−3c)α, 0<c≤1/28800, α≥2(1+1/c), x≤3cL/2, e^(−x/8)≤B₀≤1. Distinct zeros at heights [T+1,2T−1], depths [α/L,(α+1)/L], N(ρ)≥B₀ number O_c((α+1)²TL e^(−2x)/B₀²+(α+1)L³√T), without ordinate separation [L]. Open: lower bounds/negative moments and weak/multiple-zero contribution. MZF:{TheHyperbolicDensityTheorem,TheDerivativeReadsTheBlaschkeFactor,TheCountNeedsNoSeparation} [L]; [TheDerivativeIsTheBlaschkeProduct](../../formal/GaloisForLFunctions/ArithmeticInnerFunctionTheory/TheDerivativeIsTheBlaschkeProduct.lean) [S].

NGF: [ZCG](#zcg) support. Monotone Fock frequency≥k/2 at order k; for k≥2, Hermite collision profile least-gap²∈[16/k,24/(k+1)]. Buffered count/depth dissipation; finite-speed lateral energy has a factorial tail but permits tiny nonreal pairs. Isolated-pair opening requires separation/far-energy control [L]. [Adjacent gaps can close](rh-killed-routes.md#adjacent-dyson-gap); [flow structure cannot select time0](rh-killed-routes.md#heat-time-shift). Sources: NGF:{TheFrequencyIsAChaosLevel,TheHermiteMeshIsPinched,TheDepthMomentsAreDissipated,NonrealZerosEnterAtFiniteSpeed,TheCompressionAwayFromTheMesh} [L].

FFP: LA/TH support. Exact zero-piece reality⇔RH. Genus-one stability⇔upper-half-plane zeros and drift D≥0; sharp margin −D. ξ drift0; reversed Jensen roots approach Im0 for σ≥1. At scale½log d, G_d(iθ)→1/(iθ+i), σ≥1/2, θ>0. Full upper-half-plane transform convergence for σ≥1, or given zero-freeness right ofσ [L]; critical-line stability/all-root control open. [Strict-margin obstruction](rh-killed-routes.md#xi-stability-margin). Sources: FFP:{ZeroPieceRealization,GenusOneStabilityClassification,StabilityBoundaryOfXi,CauchyLimitLaw} [L].

ADO: [ZCG](#zcg)/[LA](#la) support. Exceptional nonrepelling ζ-values have Hausdorff dimension≤1, yet contain a dense residual set; nothing decides value0. FE pairs force critical-centre flatness O_ε(abs(γ)^(33/200+ε)·depth²), not their exclusion. Sources: ADO:{TheExceptionalValuesHaveSmallHausdorffDimension,TheExceptionalValuesOfZetaAreResidual,SubWeylFEPairFlatness} [L].

<a id="cht"></a>CHT: RW/ACT/OWU support. Attained margin m*: m*→0⇔RH; at pole weight1, critical log-conductor=−m*(c). Coordinate bands are intervals pinned to Λ(n), diameter and m*(c)√n≤Cexp(Kn−c/1104), c≥2, 2≤n≤exp(2c−1/6). Finite-energy logarithmic window solutions with forcing dominated by constant + finite nonnegative translates are bounded; their Green representatives satisfy u(±(a−t))√log(1/t)→∫Kf_± [L]. Open: weight-specific specialization, contact-uniform bounds, all-aperture cone nonemptiness. Sources: CHT:{TheWindowConeCollapses,TheMarginLawOfTheWindowCone,TheWindowReadsTheResidue,TheConeIsPinnedAtEveryAtom,TheBandsOfTheCone,TheWindowSolutionsAreBounded} [L].

APR: WL/MC/CTF/WD support. [Type-II norms](rh-killed-routes.md#type-ii-parity), [sublinear Type-I data](rh-killed-routes.md#type-i-parity), [finite convergent linear laws](rh-killed-routes.md#mertens-not-count) and [factor-stable bounds](rh-killed-routes.md#impure-euler-upper-bounds) do not supply square-root counting. Pole-corrected λΛ+2 shares Λ's error laws whenever √x·log²x=O(E). Real b₁=1, abs(b_n)≤1: excess κ∈(0,1/14) forces logN≥min(log²T/24,logT/(14κ)) [L]. Complex unit-bounded normalized mollifiers: excess K₀/logT forces logN≥log²T/(6K₀)−(4/3)logT, K₀>0 [L]. These are necessary bounds, not constructions. With logN=o(T), a factor 1−cp^(−s), c>√p forces liminf normalized moment≥c²/p>1. For abs(a_n)≤εn^(−η), 0≤η<1/2, class-wide O(ε²TlogT) at N≤T^θ iff θ(1−2η)≤1. Gallagher transfers logarithmic-window variance bounds to long second moments [L]; arithmetic upper bounds remain open. Sources: APR:{TheNecessaryLengthOfAMollifier,LongMollifiersImplyCriticalClustering,NoFiniteSystemOfLinearLawsDecides,TheLengthPrecisionLaw,TheLiouvilleTwinOnlySeesThePole,TheMollifiedSecondMomentSeesPurity,TheSelbergIntegralDictionary} [L]; CDG:NearLineLogMean/SubexponentialMollifierLengthAndWindowSpikes [L].

HWV: prime-form ceiling (logN−γ+ε)‖x‖² and d-star reserve (logd−ε)‖x‖² hold beyond explicit ε-dependent horizons; shallow stars/full gluing remain. Squarefree prime-complex topology supplies no signed cancellation. Sources: HWV:{TheDepthLawIsEffective,SquarefreePrimeComplexIsASphereBouquet} [L].

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
| ADO | ArithmeticDiscreteness | CHT | CriticalHardyTheoryOfTheWindowCone |
| APR | ArithmeticProduction | MZF | MultiscaleMollifiedZetaField |
| NGF | NodalGeometryOfTheDeBruijnFlow | VHR | VerifiedHeightRungs |
