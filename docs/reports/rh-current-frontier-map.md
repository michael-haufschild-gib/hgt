# RH proof-route ledger

**State:** RH open; 16 live routes; 23 candidates; no source producer completes RH.

**Corpus checked:** committed Lean through `965b0194814544d79204add94fb79311e1129bd0`; uncommitted files excluded from [L] claims.

**Status:** live = RH receiver + unexcluded producer problem; candidate = missing handoff or independent producer step; dead = stated mechanism refuted, circular or nonselective. Arrows = proposed proof path; only **Proved** records established steps.

**Evidence:** [L] cited Lean declarations, not freshly compiled; [P] paper only; untagged candidate facts retain source status. R:X = formal/GaloisForLFunctions/RHTower/X.lean; H:X = formal/GaloisForLFunctions/HTGeometry/X.lean; Pn:x = docs/drafts/pipeline/{0-backlog,1-in-progress,2-fully-proven,3-formalized,4-publication-ready,5-failed}[n]/x.md. F#### = [endpoints](endpoints.md); MUST/CANNOT/FAIL = [STATUS](STATUS.md); KR/no-go = [dead mechanisms](rh-killed-routes.md). E = evidence.

## Find a route

| Family | Live | Candidates | Dead mechanisms |
|---|---|---|---|
| Prime explicit formula / signed energy | [WL](#wl), [RW](#rw), [FU](#fu), [RP](#rp), [PA](#pa), [LI](#li) | [APF](#apf), [CTF](#ctf), [EGC](#egc), [EWJ](#ewj), [FEL](#fel) | [KR-GEN](rh-killed-routes.md#kr-gen), [KR-CRT](rh-killed-routes.md#kr-crt), [KR-FPR](rh-killed-routes.md#kr-fpr), [KR-REF](rh-killed-routes.md#kr-ref), [KR-CPF](rh-killed-routes.md#kr-cpf), [KR-TMD](rh-killed-routes.md#kr-tmd), [KR-TK](rh-killed-routes.md#kr-tk) |
| Möbius cancellation | [MC](#mc) | [HCF](#hcf), [MSC](#msc) | [KR-DEF](rh-killed-routes.md#kr-def) |
| Theta sign / heat / moments | [TT](#tt), [LA](#la), [TH](#th) | [HJ](#hj) | [KR-TEQ](rh-killed-routes.md#kr-teq), [KR-CAL](rh-killed-routes.md#kr-cal), [KR-ISG](rh-killed-routes.md#kr-isg), [KR-JPR](rh-killed-routes.md#kr-jpr) |
| Geometry / index / arithmetic rigidity | [TG](#tg), [HF](#hf) | [DR](#dr), [GTA](#gta), [IRK](#irk), [PBM](#pbm) | [KR-DSA](rh-killed-routes.md#kr-dsa), [KR-INT](rh-killed-routes.md#kr-int), [KR-TWN](rh-killed-routes.md#kr-twn), [KR-APW](rh-killed-routes.md#kr-apw), [KR-R1](rh-killed-routes.md#kr-r1) |
| Renewal / singular comparison | [RN](#rn) | — | [KR-TRC](rh-killed-routes.md#kr-trc), [KR-R2](rh-killed-routes.md#kr-r2) |
| Ward / collision | [WD](#wd) | — | [KR-UCF](rh-killed-routes.md#kr-ucf), [KR-R3](rh-killed-routes.md#kr-r3) |
| Suzuki / boundary limits | [SZ](#sz) | [SEC](#sec) | [KR-NEV](rh-killed-routes.md#kr-nev) |
| Physical realization | [PM](#pm) | [PTR](#ptr), [W1C](#w1c) | [KR-AUT](rh-killed-routes.md#kr-aut), [KR-SEL](rh-killed-routes.md#kr-sel), [HB](rh-killed-routes.md#retired-labels) |
| Singular source completion | — | [BSH](#bsh), [CDC](#cdc), [JAS](#jas), [PCS](#pcs), [RFHM](#rfhm), [SC](#sc), [WBF](#wbf) | [R, AF, F](rh-killed-routes.md#retired-labels) |
| Deterministic zeta recurrence | — | [BAG](#bag) | [KR-BAG](rh-killed-routes.md#kr-bag), [KR-TOR](rh-killed-routes.md#kr-tor), [KR-LLM](rh-killed-routes.md#kr-llm) |

## Live routes

<a id="wl"></a>
### WL — Weil lag function

- **Path:** Exact prime data → one-sided lag/Hodge bound → bounded Φ → RH.
- **Proved [L]:** RH ⇔ integer lags a_n=Φ(log n) bounded on either side; actual-prime versions and eventual bounds equivalent. Sharp ceiling a₁=2+γ−log(4π). Prime-mesh interpolation and vanishing local chord work proved; prime lags approach a₁ cofinally. Geometric barycentric schedules with controlled variance give equivalent signed-mean receivers. Three corrected lag values recover Λ(n)/n. Native scaled curvature is eventually positive exactly at odd prime powers; centered-prime Green reconstruction retains its affine term with error≤2.
- **Needs:** One source bound at √X scale: bound a_p above or below uniformly, or bound the corresponding signed barycentric means. Interpolation controls gaps, not sampled values.
- **Excluded:** Smaller sharp ceiling; fixed finite prime truncation; genus/fixed-part selector; generic lag-Gram positivity.
- **E:** R:PrimeLagLowerBoundRH; R:WeilLagPrimeQuadraticMesh; R:WeilLagLocalWorkHuxley; R:WeilLagBarycentricMean; R:WeilLagDiscretePrimeCurvature; R:WeilLagNativeCurvatureSign; R:WeilLagCurvatureGreenRegularization. Dead: KR-GEN.

<a id="rw"></a>
### RW — Restricted Weil ground energy

- **Path:** Exact prime−Gamma−polar form → μ₀(a)≥0 for every aperture a → RH.
- **Proved [L]:** All-aperture constrained positivity equivalent to RH; even-pole or odd-pole positivity suffices. Small-aperture positivity proved. Two-prime edge kernel classified; constrained interpolation proved without cofinal rate. Compact C² source bound: M=∫abs(F̂)²,P=∫abs(F̂)²/(τ²+¼)²≤16M; E_arch≥(b−C+¼)M−e^(4b)P/4, all b; optimized logarithmic M/P bound. Finite-height zero information gives finite-level lower bounds, not positivity. Exact full-ground Euler–Lagrange/zero-side identity. Cofinal nonnegative symmetric-decreasing full ground states imply RH; nonnegative nonzero full grounds with Barta edge mass≤½ total mass at every sufficiently large aperture also suffice. Cofinal even Fourier-real-rooted full grounds with nonzero mass, uniform L¹/mass≤M e^(Ka), and inverse-square zero sum≤a/[200(K+2)], K≥0, imply RH.
- **Proved [L]:** Literal Fejér box energy equals twice the completed prime-error primitive plus an explicit archimedean term; either eventual one-sided O(U) bound implies RH. Lower bounds sampled at U=log n suffice. Literal odd/even parity poles give conditional weighted deletion/addition laws; βΛ with β<1 makes odd-pole energy eventually negative.
- **Needs:** Joint all-aperture Gamma/prime-edge/polar lower bound; source-derived Xi energy floor; full-test Hodge bounds transferred to constrained V₀. Arbitrary coherent overlap must retain all cross terms. Produce the cofinal ground-state shape/localization or real-rootedness and mass/zero-sum bounds; receiver hypotheses remain open. Alternatively prove one-sided O(U) literal Fejér box energy or its weighted prime Riesz bound at log-integer apertures.
- **Excluded:** Raw compressed prime norm exponent: already 1 unconditionally. Edge-only mass gap; finite point-sample domination; positive fixed matched-mass margin; primitive surrogate omitting M/4; bare Gamma truncations K_i≤e^(rN),r<πe⁻². Their remainder-corrected joint forms remain open.
- **E:** R:PoleVanishingWeilPositivityPrimeTwo; R:CCMPrimePoleSchurKernel; R:CCMPrimePoleSchurGammaInterpolation; R:WeilWorkExposingRayPacketCoercivity; R:WeilWorkExposingRayGammaTruncation; R:CCMFullGroundZeroSideEigen; R:CCMNonnegativeGroundStateRH; R:CCMSymmetricDecreasingGroundStateRH; R:CCMGroundEnergyZeroSumBound; R:WeilFejerBoxEnergyRH; R:WeilParityPoleDeletionAdditionLaws. Dead: KR-CRT, KR-APW.

<a id="fu"></a>
### FU — CCM-FU signed prime scheduling

- **Path:** Signed prime/Möbius source → eventual upper bound A(M)/M≤B for completed Abel moment A → RH; fourth-power apertures suffice.
- **Proved [L]:** Checkpoint affine reduction, Abel–Route-P identity and exact energy bookkeeping. Prime-power contribution harmless; prime-only sector carries obstruction. Growing cores can have macroscopic negative mixed curvature. One-sided Abel equivalence retains every polar/lattice term. Positive Suzuki Green inverse and integer-to-real aperture transfer closed. Quartic interpolation costs O(M); abs(A(N²)−completed square-sample sum)≤9N².
- **Needs:** One exhaustive moving-core schedule paying energy, covariance and endpoint terms at every cutoff; signed cancellation retained. Prove the arithmetic upper bound at fourth powers, or the equivalent square-sample bound in MC.
- **Excluded:** Fixed blocks/clocks, bounded quotient depth, short clock span, positive processed-core metrics, scalar graph energy and sublogarithmic transport.
- **E:** R:CCMFUSuzukiCheckpointAffineReduction; R:CriticalAbelRoutePAsymptoticBridge; R:MobiusDivisorUniformGrowingCoreNegativeCurvature; R:CCMFUSuzukiMobiusDivisorOneSided; R:MobiusRieszQuarticSampling; R:MobiusRieszSquareSourceQuadrature.

<a id="rp"></a>
### RP — Route-P / SP-E history floor

- **Path:** Literal matched−quantile prime history → defect(K)≥−B(K+2) eventually → RH.
- **Proved [L]:** Linear-floor equivalence; unconditional negative linear excursions. Exact hyperbola/centroid/square-debt identities. Complete unweighted hyperbolic pair deletion=o(M²); low-LCM signed payment=O(M²). Native undamped signed balance has total mass zero. Biased covariance uniformly comparable to native head energy on finite physical windows. Reciprocal/mixed-primitive jump calculus retains every prime-square endpoint.
- **Needs:** Source-derived indefinite linear floor for complete history; joint centroid/square payment; signed high-LCM and moving-core control; coefficient-faithful ordered-history transport through singular source domain.
- **Excluded:** Positive/passive/scalar landings; finite graph coercivity; delayed repair with one all-later-cutoff head budget; absolute high-LCM payment. Native critical L¹/L² admission and ratio-one terminal caps fail.
- **E:** R:SPEQuantileRieszRoutePLinearFloorCriterion; R:RoutePHyperbolicPairDeletion; R:RoutePLcmPairPayment; R:RoutePNativeUndampedBalance; R:RoutePNativeCovarianceWindow; R:RoutePNativeSignedMixedPrimitive.

<a id="pa"></a>
### PA — Prime–archimedean source passivity

- **Path:** Continued exact prime−archimedean trace → Im T(z)≤0 on 0<Im z<½ → RH.
- **Proved [L]:** Finite-frequency trace sign; exact eta reflection/source recovery. High-frequency-only passivity also sufficient. Finite Euler/FE carriers have depth-dependent localization horizons; no cofinal source sign.
- **Needs:** Uniform signed high-frequency numerator bound; all-order source lower bound; source-derived opposing dyadic sign/cancellation. Growing KMS/Wightman realization must retain full arithmetic source.
- **Excluded:** Fixed finite passive/thermal/KMS systems; passive scalar completion; positive reciprocal-power carriers; real-flux-only transfer.
- **E:** R:PrimeArchEndpointFrequencyAccretivity; R:PrimeArchCentralPairedFourthTraceBand; R:EtaReflectionSourceRecovery; R:EulerExponentialCarrierCriticalLine. Dead: KR-FPR, KR-TK.

<a id="mc"></a>
### MC — Möbius cancellation at the half power

- **Path:** Exact signed Möbius source → half-power cancellation/subpower energy, or Σ_{1≤s<N}(ψ(s²)−s²)≤BN² → RH.
- **Proved [L]:** RH ⇔ M(x)=Oε(x^(½+ε)) ⇔ Möbius Hilbert energy E_N=Oε(N^ε). E_N≥c logN; M(x)=Ω±(√x). Prime/semiprime/triprime matching and low-breadth transport proved, not complete cancellation. Physical wavelet, moving-cusp and prime-only transition-covariance receivers exact; finite-prime deletion preserves them. Signed largest-prime/Ramaré decompositions retain all cross terms. Square-sampled source equals a short signed bilinear form plus O(N²). Complete small-modulus residue action O(NU), U≤N; terminal centered row O(N logN); deleting width H costs≤18H³logN for 4H≤N. Low-product divisor remainder O(N²) when 1≤Q≤N and Q⁵(1+logN)²⁴≤N². For J(t)=Σλ_Liouville(n)e^(−nt)/n, eventual J(t)≥−C√t as t↓0 implies RH and simple nonreal critical zeros.
- **Proved [L]:** Liouville lower bound J(t)≥−C√t(1+log(1/t)^k) implies RH and critical-zero order≤k+1. Global Hilbert bound E_N≤c(log(N+1))^k+C forces 2m≤k+1 for every critical-zero order m.
- **Needs:** Signed full bilinear source≤BN²: principal counterterm and high-product remainder jointly; paid small-modulus/low-product/terminal regions do not bound the whole. Alternatively full matched-source cancellation in Hilbert/wavelet receivers. Liouville and Hilbert logarithmic bounds have no independent source producer.
- **Excluded:** Uniformly bounded Hilbert energy; universal insertion contraction/expansion; local Hall or parity-preserving matching alone; absolute replacement of signed discrepancy; scalar convolution-square-root construction. Coefficient-independent quadratic bound/PSD repair of square kernel; fixed smoothing order for growing prime packets. At exact smoothing threshold normalized positive packets escape every fixed logarithmic window.
- **E:** R:MobiusHilbertFormEquivalence; R:MobiusHilbertSharpLogarithmicConstant; R:CausalMobiusThetaPhysicalWavelet; R:CausalMobiusThetaTransitionClock; R:CausalMobiusThetaPrimorialInnovation; R:MobiusPrimeInsertionLiteralPackets; R:MobiusSquareResidueShortBilinear; R:MobiusSquareBilinearCutoff; R:MobiusSquareDivisorProductBudget; R:MobiusSquareBilinearTerminalRow; R:MobiusRieszPrimePacketEscape; R:LiouvilleExponentialSumSimplicity; R:LiouvilleExponentialSumMultiplicity; R:MobiusHilbertMultiplicityLogExponent. Dead: KR-DEF.

<a id="tt"></a>
### TT — Theta-tail and heat–Cassini currents

- **Path:** Theta source → signed covariance / directed natural-window means → bounded ξ-mass current or strict-half Wold decay → RH.
- **Proved [L]:** Near-increment summability for 2t+η<1; finite prime-power subtraction harmless. Exact odd-four Schur/transport decomposition. Seam and tail positivity; global nonlinear source barrier; complete exact-boundary sign. Finite source polynomials and determinant reductions retain every cofactor. These do not establish interior/all-rank positivity. Exact kinetic degrees: third minor 16, slope 17; leading displacement coefficient strictly negative for v>0,k>−⅓ at every center.
- **Needs:** Signed nonlocal integrated covariance across rapidities; physical-scale arithmetic law for directed means. Compact-middle/interior sign in complete source domain; arbitrary-rank continuation of finite controls.
- **Excluded:** Pointwise nonnegative mixed curvature; timelike flattening; inherited scalar odd compensation; coarse affine/nonlinear cones as global sign certificates. Boundary positivity alone is insufficient. All-nonnegative displacement coefficients, including divided differences; this is not an actual-source sign counterexample. [L] Any kernel criterion stable under damping Φ↦Φ/∏(1−ic_ju) (some c_j≠0; e.g. Φ/(1+b²u²), every b≠0) or Φe^{−εu²}/∏(1−ic_ju), or Φ/φ(iu) for any LP φ with a real zero, fails for Φ (CANNOT-497/499, Newman; R:RiemannKernelDampedTransformNotLaguerrePolya; R:RiemannKernelGaussianDampedNotLaguerrePolya; R:RiemannKernelLaguerrePolyaSymbol).
- **E:** R:XiHeatCassiniWoldNaturalNearIncrementBudget; R:XiMassCenteredDivisorMixedCurvature; R:ThetaCuspCoupledOddTransportSchur; R:ThetaCuspOddTransportGapTail; R:ThetaCuspRatioQuadraticForceSecondCompletion; R:ThetaCuspRatioBoundaryCertificate/GlobalSign; R:ThetaCuspRatioKineticLeading/SlopeLeading.

<a id="la"></a>
### LA — Line anchor: Laguerre and Hadamard sign from the theta source

- **Path:** Literal theta source → Hadamard/Laguerre or all-degree Jensen sign → critical-line confinement.
- **Proved [L]:** RH ⇔ Re(ξ′/ξ)≥0 on Re s>½ ⇔ all Xi Jensen polynomials hyperbolic. Finite-height Laguerre margins, high-order horizontal-slice signs and finite-low-order reduction proved. Typical-height improvements do not cover exceptional heights. First Laguerre sign alone weaker than RH.
- **Needs:** All-height source sign; remaining low-order slices and exceptional heights; arithmetic separator for near-double off-line pairs at Dirichlet length comparable to height.
- **Excluded:** Generic first-Laguerre/finite-moment positivity; automatic high-shift Jensen hyperbolicity; first-jet or nearest-zero restatements. Xi has no Laguerre–Pólya preimage under any nonconstant real-rooted polynomial differential symbol; real-shift averages of Xi have imaginary zeros. These exclude LP-filter producers, not the direct theta-source sign path.
- **E:** R:XiLogDerivReCriterion; R:XiLaguerreMarginUnconditional; R:XiSliceFiniteOrderReduction; R:XiSliceLogLogOrderDensity; R:XiFirstOrderLaguerrePolyaMaximality; R:XiRealRootedPolynomialPreimage; R:XiDerivativeLaguerrePolyaPreimage; R:XiRealShiftAverageImaginaryZeros; H:FirstLaguerreNotRealRooted. Dead: KR-JPR.

<a id="tg"></a>
### TG — Topological sub-unit gate: boundary winding

- **Path:** Pre-divisor Gaussian Euler/Burnol source → faithful cubic transgression with nonnegative residual → integer trace<1 → RH.
- **Proved [L]:** Completed-Xi Hardy cubic trace equals enclosed multiplicity. Primitive budget B_base<1; operator seam norm<1 gives index control. Actual-disc winding, zero-free contraction, finite-height density bounds and principal Burnol cap lift proved. Source/covariance admission and fixed-Schwartz-test transfers do not identify full arithmetic cubic with that budget. Stable cone K₁≅ℤ; physical cone, theta first-exit and Wiener–Hopf presentations identify the unit generator, not the missing arithmetic cubic.
- **Proved [L]:** Cone crossed-product Schrödinger representation is faithful; full and reduced cone norms agree. Matrix Wiener–Hopf lift is Fredholm with index equal to determinant winding. Neither identifies arithmetic cubic with primitive budget.
- **Needs:** Construct matrix-complete E_base=E_residual+Tr T_D with E_residual≥0, retaining reflection-odd prime−Gamma data. Faithful source-to-Hardy identification; full signed cubic control; all-disc sub-unit bound. Fixed-scale o(1) bad-disc fraction remains open.
- **Excluded:** Holomorphic chiral loss; source-side free-orbit quantization; bounded trace-ideal transport; positive observer wall substituted for arithmetic handoff. Generic modular/positive source data do not control seam.
- **E:** R:FormationAnchoredCubicSpecialization; R:RestrictedProjectionIndexOperatorNormCriterion; R:BurnolBaseCapPrincipalLift; R:SoninGammaClockNuclearLimit; R:PluckerCovarianceObserverSubunitDefect; R:PhysicalPluckerConeExtension; H:ApertureStableKTheory; H:ApertureTransgressionPresentations; H:ConeCrossedProductFaithful; H:MatrixWienerHopfIndex. Dead: KR-DSA, KR-R1, KR-TRC.

<a id="hf"></a>
### HF — Positive Hodge form on arithmetic cohomology (Deninger / Meyer / F₁)

- **Path:** Arithmetic cohomology → positive Hodge form with Frobenius–Hodge compatibility → RH. Alternative: full-positive weights λ(n) → arithmetic/spectral rigidity λ=Λ → RH.
- **Proved [L]:** Geometric Hodge/prime-blind duality receivers; null repair and restricted shrinking-profile symbol floors. Pole-budget compact completion and attained Gamma minima; full energy nowhere weakly continuous. At positive covariance tolerance: dual optimum attained, dimension-independent measurement stability, complementary slackness and zero diagonal weights; at fixed law continuity includes tolerance zero. Exposing coefficients eventually positive with log(weight_n)/n→−2πe⁻²; every finite box tail positive. All-integer polar recovery: full C² sources β<½, one-pole sources β<1; critical energy passage open. For w(n)=(λ(n)−Λ(n))/√n, n≥2, with finite positive excess, fixed-probe asymptotic positivity⇔uniform asymptotic log-panel positivity; whole-line potential convergence⇔subexponential normalized deviation. Fine-mesh histories recover coefficients exactly, not their growth. Producer core: (c) is closed (MUST-718, any real masses on critical zeros), so only (N1) and PBAP remain. RH ⟸ PBAP + one strictly positive prime-blind radical multiplier (row 715). PBAP on the nonnegative cone (HF L349) is reduced in Lean to one window inequality (nonnegative tests, length log 2): R:PrimeBlindNonnegativeConeReduction, via quantile transport (H:QuantileRearrangementEnergy) and the Lévy–pole form (R:WeilArchReLevyPoleForm). The window inequality itself is numeric (margin ≈ 0.15). Uniqueness side: positive integer-blind measures exist at every exponential rate < π/2 (B_β·sech^k, loop row 720 [P]), so (N1)/C-PIN fails only through zero-faithfulness (the sign of the BRS V₁), not through positivity or decay.
- **Proved [L]:** Every nonempty d-coordinate packet has an exact minimal certificate of d+1 actual normalized Gram tests; erasing any test gives a basis and a positive balancing relation. Under fixed positive cost normalization, full-cutoff certificates cost more than every fixed polynomial. Arbitrarily precise bounded-history errors preserving any finite prefix generically have unbounded and signed-nonsummable moments at every real shift; regular finite-dimensional families admit a common normalized C₀ receiver.
- **Needs:** Source-derived nonnegative dual minimum or compatible positive Hodge geometry. Complete two-source Gamma/pole assembly; universal lower bound for full matched polar cone, multiplier zero included; critical β=1 fibre energy control. Finite Gram feasibility supplies no cutoff-uniform cost or full-source sign. Arbitrary full-positive λ additionally needs independent rigidity.
- **Excluded:** Finite-rank/integral-lattice substitutes; approximate prime weights below rigidity thresholds; weak compactness without pole budget; one-node cosine at boundary coefficient d<1; bare Gamma truncation; unweighted resonance extension; source-preserving positive Mellin filters other than δ₀. Countable log-panel positivity substituted for full Weil positivity, even with one finite deficit; bounded recovery histories used as moment bounds; totalized potential sums without convergence.
- **E:** R:WeilPositivityPrimeBlindDuality; R:WeilWorkPBAPJointSymbolFloor; R:WeilPaperSpectralCompactness; R:WeilPaperAffineCovarianceCertificates; R:WeilPaperCovarianceToleranceContinuity; R:WeilWorkExposingRaySublogFibreDensity; R:WeilWorkExposingRayCriticalBoundary; R:WeilPaperCovarianceDualAttainment; R:WeilPaperCovarianceMeasurementStability; R:WeilPaperCovarianceComplementarity; R:WeilWorkExposingRayTailAsymptotic; R:WeilLogShiftFiniteExcessCriterion; R:WeilLogShiftSubexponentialDomain; R:WeilLogShiftRecoveryHomeomorphism; R:WeilLogShiftGramMinimalCardinality; R:WeilLogShiftGramSimplexBasis; R:WeilLogShiftSuperpolynomialGramCost; R:WeilLogShiftArbitraryPrecisionGenericity; R:WeilLogShiftC0RecoveryReceiver. Dead: KR-INT, KR-APW.

**Conditional rigidity paths:** normalized full Weil positivity of λ assumed throughout; cubic path additionally assumes complete correspondence. None constructs λ.

| Path | Proved [L] | Needs | E |
|---|---|---|---|
| Arithmetic | Full-positive λ≤Λ everywhere or λ≥Λ everywhere ⇒ λ=Λ, without sign/growth hypotheses. Full positivity ⇒ Σ_{n≤N}λ(n)=N+Oε(N^(½+ε)), harmonic deviation L≤0, nonnegative forward variance and primorial forward means→0. Harmonic-small + absolutely harmonic-summable composite deviation ⇒ λ=Λ. With extra strict multiplicativity and prime-power deviation bound θ<1: harmonic sum in (0,1], finite Euler ceilings, Σ_p abs(f(p))/√p<∞. | General multiplicativity; uniform ζ-quotient bound on every strict half-plane; L=0 or detecting lower bound. | R:WeilWorkSingularArithmeticForwardVariance; R:WeilWorkSingularArithmeticCompositeRigidity; R:WeilWorkSingularArithmeticPrimeSummability; R:WeilFullConeMinorantRigidity. |
| Spectral quantization / phase | Full positivity constructs boundary measure. Half-integer masses, finite floor-residual mass, or one cofinal O(T^α),α<1 residual count ⇒ λ=Λ. Exact weighted bilateral periodic phase with any exponential weight r>1 ⇒ rigidity. Valuation U_p holomorphic and zero-free on abs(z)<√p, U_p(0)>0,U_p(1)=1. Canonical Gaussian phase cost Q=2E_centered+O(T^(5/6)); either λ=Λ and RH, or Q≥κT eventually. | Produce quantization, sublinear residual/phase cost, or exact weighted periodic representation. Prime independence, endpoint positivity, multifrequency extension. | R:WeilHalfIntegerMassRigidity; R:WeilWorkQuantizationRealPeriodicRigidity; R:WeilWorkSettledPhaseValuationZeroFree; R:WeilWorkSettledPhasePhaseCostDichotomy. |
| Deficit cancellation | Off-line copies contribute 1; on-line copies contribute (1−μ_atom/m)⁺ to D. liminf D(T)/T=0 ⇒ λ=Λ and RH; 4I≤D, D²≤16NI. Exact Cauchy mass D, mixed Bessel/prime-kernel budgets, product-kernel critical Mellin inversion and all-height moments. Order-zero integer correlation positive; first-order comparison negative. | Complete signed moment cancellation with paid cost; actual saddle/Gaussian moment and Xi-density contour estimates. Small horizontal displacement does not bound deficit count. | R:WeilWorkDeficitCoefficient; R:WeilWorkDeficitCriticalMellin; R:WeilWorkDeficitPrimeKernelBudget. |
| Cubic multiplicity | Under complete cubic correspondence, including E-zero confinement: central mass<¼, E(½)≠0, atom identity 3μ_atom=ord E. Either λ=Λ and RH, or infinitely many ord E<ord ξ; negative integer residues exactly encode deficits. Full Maass inversion, reciprocal tests and cutoff Mellin defect retained. | Exclude or control density of infinite deficits; boundary regularity; full cubic rigidity. Bounded continuous second primitive does not regularize actual defect. | R:WeilWorkHigherDenominatorFiniteDeficit; R:WeilWorkHigherDenominatorInversionTrace; R:WeilWorkHigherDenominatorCutoffDefect; R:WeilWorkHigherDenominatorPositiveFilter. |

<a id="th"></a>
### TH — Theta moment positivity

- **Path:** Exact theta/prime−Gamma moments → all-degree Hankel/Bezoutian PSD → RH.
- **Proved [L]:** Hermite finite-polynomial criterion; every fixed degree positive at sufficiently small degree-dependent heat time. Full form=norm energy−phase debt; same-time critical-node floors and heat-dissipation bounds proved. Literal theta fourth log derivative negative. C5 enriched current positive on 2≤t≤u; seam, Green recovery and moment transfer proved. Fixed-node tail Cauchy limits positive, not uniform in growing rank.
- **Needs:** All-degree positivity at one fixed positive heat time/all-time PSD; same-time phase ratio≤1; C5 current on 0<t≤u,t<2; full signed discrete-prime remainder and growing-rank transfer.
- **Excluded:** Common all-degree cutoff inferred from fixed-degree limits; reverse heat retention; finite point/spectral-window floors; full-tail positive Cauchy reserve; generic log-concavity/finite moments; coarse eighth-moment absorption.
- **E:** R:HankelPowerSumHermiteCriterion; R:XiHeatFiniteUniformPositivity; R:XiGaussianFullGapNodalBudget; R:XiGaussianNativeHeatDissipation; R:ThetaCuspC5OuterClockCurrent; R:ThetaCuspC5CurrentMomentTransfer; R:ThetaTailChargedEnergyCollapse.

<a id="rn"></a>
### RN — Theta renewal phase and singular cofinal comparison

- **Path:** Theta renewal/connection source → divisor-faithful complex winding or boundary-work sign → RH.
- **Proved [L]:** Exact source/determinant and reciprocal-square receivers; finite-packet comparisons. Positive resistance network and one-port/Kron identities retain charged boundary term. Actual Xi modes charged; original weighted-domain admission selects Xi divisor. Prime-two/cusp laws distinguish restricted theta families. These identities do not orient full divisor.
- **Needs:** Arithmetic square-lattice/Euler-sensitive winding law; signed prime−continuous cancellation; singular source-to-seam transport preserving full divisor. Sign of complete boundary work; exceptional theta-power parameters.
- **Excluded:** Positive renewal mass, reflection and finite deletion alone; bounded/fixed-range symmetrizers; trace-ideal/physical-ordinate transport; global source logarithm; dyadic self-similarity as independent selector.
- **E:** R:HedenmalmThetaSourceCompressedInverseDeterminant; R:XiReciprocalSquareFixedCauchySource; R:ThetaQuantileTwoEndedSelector; R:ThetaQuantileKronReduction; R:ThetaCuspChargePolynomialRigidity. Dead: KR-R2, KR-TRC.

<a id="wd"></a>
### WD — Ward orientation and horizontal collision

- **Path:** Coefficient-faithful directed source current → global negative-cross control / collision charge<2 → RH.
- **Proved [L]:** Ward edge-energy quantization; symmetric-disc excess even; horizontal slice positivity equivalent to RH after finite-low-order reduction. High-order and positive-density slice signs proved. Actual-zero singleton/horizontal-isolation density estimates retain overlap deficits; abstract packet inequalities retain mixed-class leakage. Sampled block pair-field count removes selected simple critical points under the on-line norm cap and explicit pair-field threshold; no actual-field bound supplied.
- **Proved [L]:** Sampled-block odd-angle certification bounds horizontal excess by unselected simple-line points plus uncertified mixed points. Under explicit absorber and on-line norm hypotheses, quadratic mixed deficit d≤3−2√2 costs zero in the sharp count.
- **Needs:** Global one-sided cap family with uniform integrability; all-prime directed comparison; low-order signs at every height. Eliminate actual mixed-class loss for full horizontal Lamzouri inequality; density does not give all-fibre isolation. Prove actual owner odd-angle or absorber/deficit bounds, including the on-line norm cap and off-line pair-field thresholds, for every zero block.
- **Excluded:** Symmetric smoothing, scalarized/unlabelled exchange, generic collision transversality; sub-quantum source margin replacing unquantized growth; trace-only overlap criterion.
- **E:** R:XiWardEdgeEnergyPhaseQuantizationUniversalityLaw; R:XiHorizontalCollisionChargeEndpoint; R:XiSymmetricDiscIndexParity; R:XiSliceFiniteOrderReduction; R:HorizontalSingletonDensityNinth; R:HorizontalIsolationBlockPairField; R:HorizontalIsolationBlockFailureCount; R:HorizontalSimplicitySharpDeficitCount. Dead: KR-R3.

<a id="li"></a>
### LI — Paired Li and prime–Gamma Li balances

- **Path:** Literal prime−Gamma history → signed lower bound / finite primitive floor → Li positivity → RH.
- **Proved [L]:** Li positivity receiver, including fixed progressions; exact Cayley−Chebyshev and even-cross balances. Source/history, Gamma coupling and Green identities retain signed forcing. Actual Euler jets have both signs; positive local windows and sharp first-negative-order laws classified.
- **Needs:** Eventually Re H_N≥K_N−C on 0<t≤c log(2N+1),some valid r and 0<c<r/4; alternatively finite eventual lower bound for literal primitive P. Moving-history outside correlation/first-crossing sign.
- **Excluded:** All-even Euler-jet positivity; positive Gamma couplings or asymptotic ratios substituted for signed source bound; scalar Cassini orientation.
- **E:** R:LiEvenCrossRealEulerJetBridge; R:LiEvenCrossEulerFirstNegativeOrder; R:LiEvenCrossActualCurrentPositiveWindow; R:LiEvenCrossEulerSourceBoundaryLimit.

<a id="sz"></a>
### SZ — Suzuki screw and shifted-kernel limits

- **Path:** Complete signed source boundary pairing → screw nonnegativity / canonical shifted-Xi confinement → RH.
- **Proved [L]:** Screw/shifted-Xi receivers; exact supported modulation phase recovery and Schur law. Boundary pairing, aperture transfer and explicit quantile debit retained. Finite-head/tail decompositions do not fix complete source sign. Positive Green inverse gives one-sided receiver. Observer boundary/M→0; terminal history costs O(L³/(M√M)), hence O(M) for L³≤M^(5/2), 2(L+2)≤M. Native Cayley synthesis converges a.e. along the full sequence with one null set for countable inputs and finite mixtures.
- **Needs:** Source Wronskian law controlling moving infinite head and weighted shell leakage in topology retaining cusp cancellation; uniform moving-source passage to unshifted Xi. Linear bound for remaining interior signed/positive-history action; a.e. reconstruction alone supplies no sign or uniform moving-source bound.
- **Excluded:** Eventual frequency monotonicity; discarded cusp/tail cancellation; finite-aperture or finite-head positivity used as full floor.
- **E:** R:SuzukiScrewPointwiseNonnegativityCriterion; R:SuzukiCanonicalShiftedXi; R:CCMSuzukiCrossApertureCurvatureLeakage; R:CCMRestrictedWeilModulationPhaseRecovery; R:CCMOutgoingQuantileEntropyDebit; R:CCMUnitRieszSuzukiGreenPositiveInverse; R:SuzukiObserverJetBoundaryAsymptotics; R:SuzukiObserverJetTerminalLayer; R:PaperSuzukiCayleySynthesis.

<a id="pm"></a>
### PM — Physical-model routes: FZZ parity delay and recoil Ward transmutation

- **Path:** FZZ/PW-B physical source → complete admitted Ward/energy identity → Haar approximation or √Y-growth receiver → RH.
- **Proved [L]:** FZZ parity-delay/Mellin and dyadic-clock receivers. Witness signature/negative-index laws; exact leading compensation and retained weak retarded realization. Physical formulations reduce to arithmetic cancellation/approximation, not an independent positive mechanism.
- **Needs:** Nonnegative witness half-mass/Haar-target approximation; L² admission at positive dampings approaching zero. PW-B: complementary-rate two-response insertion, ordered cap and all-divisor extinction. Pure-Xi no-collision and distributional/action realization.
- **Excluded:** Generic HB scattering positivity; fixed native-L² on-shell realization; passive/separated-sign production; unconditional QNM/left-source equivalence. Fixed logarithmic convergence also requires critical-zero simplicity.
- **E:** R:FermiNymanBeurlingWitnessSignature; R:FermiNymanBeurlingHaarTarget; R:FZZParityAreaResponseDyadicClockBridge; R:ThetaCuspHawkingBMPWRetardedWeakNative. Dead: HB.

## Route candidates

<a id="apf"></a>
### APF — Arithmetic paired Fredholm

- **Path:** Prime source → zero-independent divisor exhaustion → vanishing Fourier traces → RH receiver.
- **Available:** Source winding/trace and completed K₁ finite-ancestor classification. [L] Matrix Wiener–Hopf lift has Fredholm index wind(det U), without arithmetic trace cancellation. Literal arithmetic cycle traces reconstructed a.e. from ζ–Mellin Fourier coefficients, with a common exceptional set; reconstruction does not annihilate coefficients.
- **Needs:** All Fourier-trace coefficients zero; source-derived exhaustion. Index+cokernel exhaustion is circular. Core (row 707): the reconstructed coefficients are ζ–Mellin values at the zeros, so their vanishing is the zero side of the explicit formula with the off-line terms removed, i.e. the Weil-positivity receiver.
- **E:** CANNOT-100; H:MatrixWienerHopfIndex; R:PaperZetaCycleFourierReconstruction.

<a id="bag"></a>
### BAG — Deterministic zeta self-return

- **Path:** Full reflected AFE → deterministic positive-density self-return on every closed right-strip disc → RH.
- **Available:** Self-return receiver [L]; off-line-root returns have density zero. Full reflected random AFE target has probability ≥c(n²)^−ε inside every finite phase cell, uniformly at heights [n²,2n²]; random, not physical orbit. Complete sharp cubic reduces to near-cone action plus o(N/log²N). At physical prime height r, zero-defect axes/intersection=(1−r⁻²)×full inverse-profile action; nonzero local channel=r⁻²×same action. Entire nonzero local channel negligible at log²N/N scale; original cubic=complete axes action plus vanishing normalized error.
- **Available [L]:** Smooth ζ partial sums have a uniform compact-disc expansion with explicit ζ-residue and polar term, without assuming zeros absent; this does not give physical-orbit recurrence.
- **Needs:** Signed complete axes action o(N/log²N) over all physical prime heights; coupled pole/near-cone/tail payments; growing moments/moving cofactors; deterministic common-height self-return. Finite Euler products and random-product laws do not supply this. Core (row 707): in the Bohr lift ζ(s+iτ) = F(s;(p^{−iτ})_p), F is defined only almost everywhere for σ < 1, and ζ is the non-generic point z = 1. Strong recurrence ⟺ that point is a continuity point of the random Euler-product functional on compacts of the strip ⟺ RH.
- **E:** R:ZetaStrongRecurrenceReceiver; R:FullReflectedAFECompactTarget; R:ChiCubicNearConeReduction; R:ChiPrimeGaussianCubicLocalAxisRigidity; R:ChiPrimeGaussianCubicLocalAxesReduction; R:ZetaSmoothedPartialSumsDisc. Dead: KR-BAG, KR-TOR.

<a id="bsh"></a>
### BSH — Arithmetic mate curvature

- **Path:** Literal prime−Gamma section → mate identity → source orientation.
- **Available:** Mate curvature=character curvature×‖y(j+1)‖²+boundary ideal.
- **Needs:** Construct literal section and mate identity before closure; ordinary/Boolean closed completion fails. Core (rows 564, 714): the mate identity's orientation term is the radial character `(2Re ρ − 1)log n` of the prime–Gamma section. Constructing the literal section with the identity in force is equivalent to placing every zero on the line. No source is known that forces it without a divisor statement.
- **E:** P1:bsh-own-research-facts; no-go-369.

<a id="cdc"></a>
### CDC — Constitutive dagger

- **Path:** Arithmetic presentation → neutral constitutive grade → source law.
- **Available:** Canonical pre-divisor potential; three-slot proof erasure iff neutral grade; exact fusion K=8E/(1−2E).
- **Needs:** Arithmetic presentation surviving singular completion while breaking inverse/co-shift covariance. Core (rows 564, 714): `admitsRadiallyCalibratedDaggerConfluence_iff_re_eq_half` [L]. A calibrated descending potential exists exactly at `Re s = ½`, so the open source theorem (one fixed pre-divisor potential descending on every closed Ξ-error fibre) is RH stated fibrewise.
- **E:** R:ConstitutiveDaggerConfluence; R:CompletionProofExchangeCostFusion.

<a id="ctf"></a>
### CTF — Chronological tail

- **Path:** Bounded chronological Bose rows / Möbius subset sums → arbitrarily small L² error → RH.
- **Available:** [L] RH ⇔ rows abs(a_k)≤1 approximate e^(−t) ⇔ Möbius subset-sum approximation ⇔ dual sampling inequality. Unbounded integer/prime Bose rows dense unconditionally. Bounded vanishing-error rows force a_k→μ(k); fixed node sets must contain every squarefree. Off-line zero ⇒ sharp Möbius error norm→∞; a bounded subsequence forces RH. Growing-moment rows pay tail≤8/logN; small-time window remains. Stretched kernel e^(−t^a): a≤1 unconditional density, a>1 target membership⇔RH. Exact integer-blind logarithmic-room threshold K≤π/2 forces vanishing; K>π/2 admits nonzero separators.
- **Needs:** Source construction of uniformly bounded vanishing-error rows, or independent dual sampling bound. Unconditional density, pointwise coefficient rigidity and shrinking tail do not pay the growing small-time window. Sharp-Möbius non-escape is sufficient, not asserted RH-equivalent.
- **E:** R:ChronologicalRiemannEquivalence; R:ChronologicalMobiusSubsetSums; R:ChronologicalDualSamplingCriterion; R:ChronologicalBoundedRowMobiusRigidity; R:ChronologicalMobiusEscape; R:ChronologicalZeroChargeTailBounds; R:StretchedBoseRiemannEquivalence; R:StretchedBoseCriticalLogRoomDensity; R:IntegerBlindLogarithmicCarlsonCritical; R:IntegerBlindLogarithmicCarlsonSharpness.

<a id="dr"></a>
### DR — Dyadic Xi roots

- **Path:** All dyadic roots on strict-right domain → nonvanishing → RH.
- **Available:** Every root level on common Littlewood zero-free cusp; all 2^k roots on connected domain force nonvanishing. [L] Tilted Xi monodromy reaches every finite quotient; coordinate relatively algebraically closed. Actual marked image cover has constructed simply connected analytic capping; any planar analytic open embedding is onto, existence not supplied. Marked Kummer square classes/half-fields explicit; finite-plane unramifiedness does not trivialize the common quadratic class.
- **Needs:** Global continuation/monodromy on entire strict-right domain. Capped topology/profinite surjectivity does not supply global dyadic roots. Core (row 707): every dyadic root of ξ exists on Re s > ½ iff ξ is zero-free there. The only non-restating source is a convergent zero-free representation of log ζ on ½ < Re s < 1, and its canonical form Σ Λ(n)n^{−s}/log n converges there iff RH. Davenport–Heilbronn shows the Euler product must enter at length ≍ t. Planar uniformization and full fundamental-group identification remain separate.
- **E:** R:XiSymmetricLittlewoodZeroFreeCuspDyadicRoots; R:ZetaPoleHalfCausalSource; R:XiTiltPuncturedMonodromy; R:XiTiltRelativeClosure; R:XiMarkedSquareKernel; R:XiFiniteMarkedUnramified; R:XiLegendreHalfCoordinates; R:XiCappedAnalyticAtlas; R:XiCappedNoBoundedEmbedding. Dead: KR-TWN.

<a id="egc"></a>
### EGC — Pole-safe contour

- **Path:** Shifted source contour → complete residue cancellation → RH receiver.
- **Available:** Complete shifted-residue row equals continued-source difference; centered negativity at each Xi copy.
- **Needs:** Outer noncentered decay/cancellation retaining all copies.
- **E:** R:XiMeromorphicCauchyPairSourceLanding; R:XiMeromorphicCauchyPairAllCopyCenteredCorrection.

<a id="ewj"></a>
### EWJ — Euler/Wold jets

- **Path:** Faithful third jets → admitted exhaustive source budget → receiver.
- **Available:** Source/depth-faithful third-jet budgets.
- **Needs:** Zero-independent admission and exhaustion; finite-jet feasibility insufficient. Core (rows 564, 714): Euler–Wold third-jet budgets admit and exhaust exactly when the zero-side explicit-formula terms with `Re ρ ≠ ½` vanish. Zero-independent admission is therefore the Weil-positivity receiver; finite-jet feasibility is blind (no-go-173).
- **E:** no-go-173.

<a id="fel"></a>
### FEL — Theta likelihood

- **Path:** Predeclared cofinal likelihood history → zero-to-contrast balance → confinement.
- **Available:** Probability, contrast, reflection gap and tail/vertical decomposition.
- **Needs:** Source-derived zero-to-contrast balance along that history. Core (rows 564, 714): the zero-to-contrast balance along a predeclared likelihood history is the explicit-formula balance between prime contrast and zero contrast. A source-derived balance is an a priori bound on the off-line zero side, i.e. existence in the HF sense (PBAP + one ray).

<a id="gta"></a>
### GTA — Transverse Schur charge

- **Path:** Source stage charge → transverse energy control → orientation.
- **Available:** Persistent nonnormality; one-hyperbolic-plane limit.
- **Needs:** Source control of transverse energy, not trace-faithful polarization alone. Core (rows 564, 714): `riemannHypothesis_iff_thetaSourceSchurPositiveQuarticChargeUniformDecay` [L]. Uniform decay of the transverse charge is RH; the needed source control of transverse energy has no input independent of the divisor.
- **E:** F0122; no-go-237.

<a id="hcf"></a>
### HCF — Critical feature variance

- **Path:** Arithmetic nonuniformity → cofinal trace ceiling → RH receiver.
- **Available:** Uniform-grid aliases→0; compact alias saving≤37/100 zero count.
- **Needs:** Arithmetic anti-equidistribution and cofinal ceiling.
- **E:** R:HedenmalmCriticalFeatureVarianceSavingCeiling; R:HedenmalmCriticalFeatureUniformGridAliasNoGo.

<a id="hj"></a>
### HJ — Hurwitz reflection

- **Path:** Rational source fibres → reflection residual zero → RH.
- **Available:** Rational fibres recover n^s; all-fibre modulus-two reflected equality equivalent to RH; E(n²)=4E(n)(1+E(n)). [L] Packets reconstruct n^s for every s and never use ζ(ρ)=0, and the reflected responses agree iff Re ρ=½ at every strip point, zero or not (R:XiHurwitzRationalFiberSeam); the residual is β=½ itself, so the route restates RH.
- **Needs:** Independent source proof of residual zero.
- **E:** R:PrimeTailSeedHurwitzReflection; R:XiHurwitzRationalFiberSeam.

<a id="irk"></a>
### IRK — Rotation-algebra trace

- **Path:** Arithmetic trace/Chern landing → integral constraint → orientation.
- **Available:** K₀ scalar action only integral; no rapidity selector.
- **Needs:** Arithmetic landing with information beyond K₀ alone. Core (rows 564, 707, 714): the `K₀` trace `rank + θ_{p,q}·chern` is integral only if `chern = 0`. The open step is an arithmetic module whose Chern class equals the off-line multiplicity and whose trace is an integer analytic count. No count weights off-line zeros by an irrational factor, so the `K₀` layer is decorative and the content is that count.
- **E:** F0164; CANNOT-177.

<a id="jas"></a>
### JAS — Joint ancestry

- **Path:** Singular all-grade ancestry → new creation/covariance law → orientation.
- **Available:** Singular carrier, theta value and all-grade chain.
- **Needs:** Changed inverse covariance/literal creation; avoid circular ancestry premise. Core (rows 564, 714): `exists_jasGammaThetaClosedFlatUnitResidueCertificate_iff_not_riemannHypothesis` [L]. The creator's current operator properties are compatible with any off-line copy, so a surviving JAS needs a new law excluding the unit residue (reflected prime-source linearity or trace cancellation). That law is RH-strength.
- **E:** F0128; no-go-228, no-go-229, no-go-230, no-go-231.

<a id="msc"></a>
### MSC — Möbius−Sonin transport

- **Path:** Nonpower source transport → divisor/conormal-preserving energy → receiver.
- **Available:** Real-power rigging preserves mass only when divisor moves to zero-free point.
- **Needs:** Nondiagonal, nonpower transport preserving original divisor and conormal. LP z-multipliers φ(D) are also excluded (CANNOT-497) [L]: every nonconstant real-rooted polynomial φ (R:XiFirstOrderLaguerrePolyaMaximality; R:XiRealRootedPolynomialPreimage; R:XiDerivativeLaguerrePolyaPreimage), and every transcendental LP φ with a real zero on the kernel side (R:RiemannKernelLaguerrePolyaSymbol). The transport must mix Dirichlet coefficients across n.
- **E:** R:HedenmalmGammaSewnSquarefreeFisherThresholdTrackedRigging.

<a id="pbm"></a>
### PBM — Prime boundary monodromy

- **Path:** Source boundary cancellation → no monodromy at infinity → orientation.
- **Available:** No producer theorem recorded. [P] Growth bounds cannot remove logarithmic charges; a monodromy-free series (Σ_p p^{−s} convergent on Re s>½) is von Koch's prime count, i.e. RH; the archimedean weld carries no charge to cancel.
- **Needs:** Source cancellation/no quantized monodromy at infinity.

<a id="pcs"></a>
### PCS — Singular co-shift

- **Path:** Singular ground → wall-class annihilation → confinement.
- **Available:** Explicit complex and wall-classifying ground.
- **Needs:** Annihilate wall class without erasing forward mode; source-natural boundary remains covariant. Core (rows 564, 714): F344. The reflection-odd singular class vanishes exactly on the line because the two co-shift eigenvalues differ by the radial character off it. Annihilating the wall class while keeping the forward mode is the statement that every zero has `Re ρ = ½`.
- **E:** F344; no-go-157.

<a id="ptr"></a>
### PTR — Photonic source

- **Path:** Prime-order nonlinear port → all-grade Xi interface → energy receiver.
- **Available:** Pointwise full-jet Gårding bound.
- **Needs:** Nonlinear/nonlocal port and all-grade Xi handoff. Core (rows 564, 714): the frozen complex transmission collar excludes critical prime conormals [L]. The variable-coefficient Maxwell transmission law that would carry this to the full source is unproved and is where the divisor information would have to enter.
- **E:** R:PhotonicCorotatingFullJetGarding; R:PhotonicFrozenComplexTransmissionConormalNoGo.

<a id="rfhm"></a>
### RFHM — Support grade

- **Path:** Phase/depth/compound-faithful source → broken inverse covariance → wall law.
- **Available:** Inverse-covariance/creation obstruction.
- **Needs:** New covariance/creation law retaining phase, depth and compounds. Core (rows 564, 714): no-go-229/231. Reversible prime sewing and direct prime-torus actions preserve inverse covariance, so they cannot see `Re ρ`. A new covariance or creation law retaining phase, depth and compounds is the RH input itself.
- **E:** no-go-229; no-go-231.

<a id="sc"></a>
### SC — Stokes/Witt−Krein

- **Path:** Cross-fibre indefinite invariant → source orientation.
- **Available:** Pointwise rigged fibres chamber-constant.
- **Needs:** Source-fixed indefinite restriction/cross-fibre invariant. Core (rows 564, 714): F188 / `SourceHorizontalRiggedKreinWallSingularityNoGo` [L]. Fibrewise Krein invariants are chamber-constant and the canonical polarization is wall-singular. A cross-fibre indefinite invariant that selects the wall would be a Pontryagin index equal to the number of off-line pairs (Krein–Langer), i.e. a Weil-form inertia statement.
- **E:** F188; no-go-170.

<a id="sec"></a>
### SEC — Adjacent prime seam

- **Path:** Exact eventual compactness → zero jump → confinement.
- **Available:** Essential norm equals jump; asymptotic smallness automatic and nonselective. [L] Compact-ideal trace cost is 0 exactly for equal endpoint charges, otherwise ∞; off-line points retain infinitely costly edges cofinally despite essential norm→0.
- **Needs:** Exact eventual compactness from arithmetic source.
- **E:** R:XiPrimeSeamAdjacentEssentialNormNoGo; R:PaperPrimeSeamIdealTrace.

<a id="w1c"></a>
### W1C — Clifford−Dirac

- **Path:** Arithmetic domain/scattering denominator → spectral confinement.
- **Available:** [L] Bare operator has neither point spectrum nor compact resolvent. Complex-fugacity Lee–Yang chains/trees with abs(α)≤1 retain real-rootedness. Each affine field of frequency λ forces a zero within π/λ; normalized locally uniform E·Ξ limits, E entire zero-free, obey eventual Σ_j max(λ_j−2π/T,0)≤log(T/2π)−1+C/√T at admissible T≥4; complex chains included. Integer-anchored Γ-site chains have a spurious early zero for every length and real coupling abs(c_k)≤1, so no normalized Xi limit. Unitary Euler factorization forces every diagonal factor to have modulus one. Unimodular-fugacity chains factor into free sites (zero set = union of progressions); the κ/(k+2) doubled-harmonic chain equals 2cos(xℓ)+2κRe[e^{ixℓ}Σn^{−1−2ix}] up to κ²H²e^{|κ|H}, i.e. ζ enters on the 1-line (Lagarias–Suzuki shape). [L] Ξ is LP-maximal (CANNOT-497 with Newman). [L] Real-shift averages cosh(hD)Ξ, h ≠ 0, have imaginary zeros (R:XiRealShiftAverageImaginaryZeros); only imaginary shifts cos(hD), h ≥ ½, are LP. [P] For 0<h<½ the non-real zeros of cos(hD)Ξ up to T number ≤ 4N(½+h,T)+O(log T) (phase on Re s = ½+h loses 2π per zero to its right), so they have density zero for every h>0, unconditionally (loop row 722). [L] 0 ≤ Λ_dBN(cos(hD)Ξ) ≤ max(¼−h²,0)/2 for every h>0 (R:XiCosineShiftHeatStrip). For every nonconstant real-rooted real polynomial φ, no LP ψ has φ(D)ψ = Ξ, via flat theta mass at the kernel's natural boundary (R:RiemannKernelStripLPMaximality; R:XiFirstOrderLaguerrePolyaMaximality; R:XiRealRootedPolynomialPreimage; R:XiDerivativeLaguerrePolyaPreimage). For every transcendental LP symbol φ with φ(0) ≠ 0 and a real zero, the kernel-side preimage ∫Φ(u)φ(iu)^{−1}e^{izu}du is not LP (R:RiemannKernelLaguerrePolyaSymbol). So no producer is an LP operator applied to an LP function. [L] The zero slack is exactly at the critical line: cos(hD)Ξ is LP for h ≥ ½ (and every h > 0 under RH) but lies in (1 − (2h/π)D)·LP for h ≥ 3/2 (every h > 0 under RH), by the triple angle cosh 3u = cosh u(2cosh 2u − 1) (R:XiCosineShiftLaguerrePolya; R:XiCosineFamilyLaguerrePolyaSlack). [L] The Gaussian side is shift-blind: e^{τD²}cos(hD)Ξ has non-real zeros for every τ, h > 0, and Λ_{dBN}(cos(hD)Ξ) = 0 exactly for h ≥ ½; RH ⟺ cos(hD)Ξ ∈ LP for every h > 0 (R:DeBruijnNewmanCosineShift). Only the finite-order rigidity sits at h = 0.
- **Needs:** Arithmetic domain/coupling or scattering denominator retaining Xi's divisor while satisfying field-density constraints; no Γ-site anchored or modulus-p^(−½) unitary Euler shortcut.
- **E:** R:WeightOneCliffordSpectralNoGo; R:ComplexFugacityLeeYangChain; R:ComplexFugacityLeeYangTree; R:UnitaryEulerFactorRigidity; R:LeeYangDatumFirstZero; R:LeeYangProducerFieldDensity; R:ComplexFugacityChainFieldDensity; R:ComplexFugacityChainDatum; R:ComplexFugacityChainUnimodular; R:ComplexFugacityChainFirstOrder; H:FirstOrderFilterVanishingIntervalBound; R:GammaSiteLeeYangChainXiObstruction.

<a id="wbf"></a>
### WBF — Source certificates

- **Path:** Arithmetic certificate stream → uniform-depth completion → Xi landing.
- **Available:** Gauge-invariant semantic/lineage fusion and polar energy; repair rank≥hidden lineage; weak-null critical streams defeat compact observers. [L] Every finite genealogy compression has compact-ideal cost 0, completed nonzero-fibre genealogy cost∞; operators, adjoints and Grams converge strongly but norm gap≥1, unchanged by compact repair.
- **Needs:** Arithmetic stream, depth-uniform completion, Xi handoff. Core (rows 564, 714): certificate genealogies have compact-ideal cost 0 or ∞ [L], with a norm gap `≥ 1` unchanged by compact repair. A depth-uniform completion landing on Ξ is a uniform positivity statement for the completed stream, equivalent to Weil positivity at every level.
- **E:** H:OperatorCertificateGenealogy; H:OperatorCertificateCofinal; H:PaperGenealogyTraceCompletion.

## Shared constraints

- Exact source: full Weil-positive perturbations of Λ with subcritical/absolutely small deviation force equality; approximate weights do not bypass HF rigidity. E: R:WeilLittleOVonMangoldtRigidity; KR-APW.
- Cofinal law: finite jets, finite packets and finite prefixes do not establish a global sign. Exact hypotheses of each finite-data no-go retained in [killed ledger](rh-killed-routes.md#route-class-obstructions).
- Orientation: reflection-even averages, translation positivity and localized fixed parts do not supply reflection-odd/divisor orientation. E: CANNOT-399, CANNOT-405, CANNOT-407; KR-GEN, KR-REF.
- Arithmetic rigidity: deformation-stable inequalities alone do not exclude off-line zeros. E: R:EstermannDeformationObstruction.
- Sharp scale: bounded lag/current receivers need finiteness at √X scale; a sub-unit margin cannot replace missing finiteness. E: KR-R1, KR-R3.
- Scoped no-go ≠ route retirement. KR-R1→TG, KR-R2→RN, KR-R3→WD, KR-BAG→BAG retain live residuals.

## Other receivers and falsifiers

| Form | Proved | Missing |
|---|---|---|
| Báez–Duarte approximation | d_N→0 ⇔ RH; liminf d_N²logN≥Σ_{distinct critical ρ, Imρ>0}2/abs(ρ)²; finite off-line packets give Blaschke floors [L]. Multiplicity-weighted floor liminf d_N²logN≥Σ_ρ2m_ρ²/abs(ρ)² over all critical zeros [L, MUST-874]; Burnol rate at the simple-zero value ⇒ RH ∧ simplicity [L, MUST-876]. R:BaezDuarteCriterionHardDirection; R:BaezDuarteBurnolAllCriticalZeros; R:BaezDuarteBlaschkeFloor. | Independent approximation producer. |
| BSY / Poisson–Jensen | Weighted log integral I≥0; I=0 ⇔ RH. Entire-mollifier near-one criterion [L]. R:BalazardSaiasYorCriterionEquivalence; R:BalazardSaiasYorMollifierClass. | Source proof I=0 or corrected near-one weighted mean square; short-window bounds insufficient. |
| Classical decay/discrepancy | RH ⇔ Riesz Oε(x^(¼+ε)), sequential Oε(k^(−¾+ε)), Farey D₁=Oε(n^(½+ε)), D₂=Oε(n^(−1+ε)); D₂ sum of squares [L]. R:BaezDuarteExponentLaw; R:FareyDiscrepancyExponentLaw. | Independent exponent-bound producer. |
| Newton geometry | Every Xi zero in a line-centered invariant disc ⇔ RH [L]. R:XiNewtonSchwarzPickCriticalLine. | Source proof of line-centered containment. |
| Certified falsifier | Negative admissible Hermite/Hankel/Pick/source-energy witness, first-Laguerre violation, or positive-time de Bruijn multiple zero ⇒ ¬RH [L]. R:LocalHermitePositivity; R:TraceFormSignature; R:DeBruijnNewmanCollisionCriterion. | One certified witness with its domain/isolation hypotheses; negative-time collisions insufficient. |

Full receiver inventory: [endpoints](endpoints.md). No producer attached to remaining divisor-side restatements.

## Alias lookup

C1→RW; CCM-FU→FU; CLG/TTF,K-RVM,S6F,TCD,UEB→TH; CSB,STC,U,MPLF,RHist,BPC,TQFQ,WS2,SQB→RN; D2,Q,RG,RG-ETA,TK→PA; E,EDQ,L,HDL,PSRC→MC; FZZ-P,PW-B→PM; G,HC→WD; O→WL/RW (genus mechanism dead); P,SP-E→RP; SV2,RG-HF→SZ; T1,T2,Route T→TT; Route T successor/ULF sub-unit anchor→TG; Deninger→HF. Other retired labels: [killed ledger](rh-killed-routes.md#retired-labels).
