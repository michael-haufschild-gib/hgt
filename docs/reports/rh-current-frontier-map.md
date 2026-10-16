# RH proof-route ledger

**State:** RH open. 21 live routes; 23 candidates. No route has a source-derived RH-closing sign or bound.

**Lean checkpoint:** 650c70e67663ed2c2555b9d3490e078f865445f6. [L] = tracked, root-imported Lean declaration (not recompiled for this ledger); [S] = source-only/unwired declaration, not counted as proved; [P] = paper claim. R:X = formal/GaloisForLFunctions/RHTower/X.lean; H:X = formal/GaloisForLFunctions/HTGeometry/X.lean. E = source modules, not extra premises. Paths are proposed; only Established facts are proved.

**Classification:** Live = exact RH receiver plus explicit source-producer problem. Candidate = incomplete source handoff or independent producer mechanism. Killed = scoped mechanism refuted/circular/nonselective; see [killed routes](rh-killed-routes.md). One route may have alternate receivers for one source architecture.

## Find a route

| Family | Live | Candidates | [Dead mechanisms](rh-killed-routes.md) |
|---|---|---|---|
| Prime explicit formula / signed energy | WL, RW, FU, RP, PA, LI, CTF | APF, EGC, EWJ, EWU, FEL, OWU, RB | KR-GEN, KR-CRT, KR-CCP, KR-BD, KR-FPR, KR-REF, KR-CPF, KR-TMD, KR-TK, KR-SRP |
| Möbius cancellation | MC | MSC | KR-DEF |
| Theta sign / heat / moments | TT, LA, TH, HCF | HJ | KR-TEQ, KR-CAL, KR-ISG, KR-JPR, KR-HFR |
| Causal hyperbolic–modular duality | CHMD | — | CHMD scoped compactness/order |
| Geometry / index / arithmetic rigidity | TG, HF | DR, GTA, IRK, PBM | KR-DSA, KR-INT, KR-TWN, KR-APW, KR-RAW, KR-R1 |
| Newton dynamics | XN | — | — |
| Renewal / singular comparison | RN | — | KR-TRC, KR-R2 |
| Ward / collision | WD | — | KR-UCF, KR-R3, KR-HUS |
| Suzuki / boundary limits | SZ | SEC | KR-NEV, KR-BD |
| Physical realization | PM | PTR, W1C | KR-AUT, KR-SEL, KR-PTR, KR-GAP, KR-COS, KR-POI, KR-ISG; HB |
| Singular source completion | JAS | BSH, CDC, PCS, RFHM, SC, WBF | R, AF, F |
| Deterministic zeta recurrence | — | BAG | KR-BAG, KR-TOR, KR-LLM |

## Live routes

<a id="wl"></a>
### WL — Weil lag function

- **Path:** Exact prime data → one-sided bound on Φ(log n) or prime lags → RH.
- **Established [L]:** Either one-sided bounded lag criterion is RH-equivalent; power-gap, prime-mesh, progression, and thin-exception sampling transfer source bounds. Explicit prime-lag/zero-free-strip exponent laws, curvature and Cayley reconstructions retain affine charge. Sampling and operator encodings do not produce a bound.
- **Open:** Source-derived exponent-zero one-sided prime-lag bound (or equivalent dips/exponentially thin failures); alternate no-off-line-chain plus bounded progression/density-zero exception.
- **E:** R:PrimeLagLowerBoundRH; R:WeilLagDenseSampling; R:WeilLagPowerGapExceptionalSampling; R:WeilLagPrimeWindowMeanReceiver; R:PaperLagCayleyDeterminantReconstruction.

<a id="rw"></a>
### RW — Restricted Weil ground energy

- **Path:** Complete prime−Gamma−polar form → nonnegative constrained ground energy at every aperture → RH.
- **Established [L]:** RH iff all-aperture negative index vanishes. Compact self-adjoint threshold pencil computes exact finite index and minimal positive repair. Odd/primitive positivity, full mixed Φ explicit formula, and exact Doob identity retain every prime cross-term; small apertures are positive. Literal Fejér box energy gives another one-sided receiver.
- **Open:** All-aperture lower bound for the actual signed form, including joint Gamma/prime-edge/polar terms; equivalent cofinal ground-state or Fejér-box source bound.
- **E:** R:WeilMarkovOddPositivity; R:WeilMarkovPrimitiveHyperplane; R:WeilMarkovOneBoundState; R:WeilFejerBoxEnergyRH; R:PaperRestrictedWeilGroundThreshold.

<a id="fu"></a>
### FU — CCM-FU signed prime scheduling

- **Path:** Signed Möbius/prime scheduling → completed Abel moment A(M)/M bounded above → RH.
- **Established [L]:** One-sided Abel receiver retains polar/lattice terms. Prescribed finite prime blocks admit a helper core with positive Boolean energy differences. A prime-exhaustive history can decrease complete clock energy at each insertion block's own cutoff, without a head-sign premise.
- **Open:** Pay fixed seed and signed drift between successive cutoffs, including earlier action, covariance, and endpoints; obtain uniform completed-Abel bound. MC's fixed-window actual-prime synthesis does not pay this history.
- **E:** R:CCMFUSuzukiMobiusDivisorOneSided; R:MobiusDivisorPreparedPrimeCube; R:MobiusDivisorPaidPrimeExhaustion; R:MobiusRieszSquareSourceQuadrature.

<a id="rp"></a>
### RP — Route-P / SP-E history floor

- **Path:** Literal matched−quantile prime history → eventual linear defect floor → RH.
- **Established [L]:** Linear-floor equivalence, signed hyperbola/centroid/square-debt identities, low-LCM payment, and exact Abel/RP tail representations. Full signed Cayley tails have noncompact positive and negative parts; compact repairs cannot force their sign.
- **Open:** Source-derived complete-history floor with joint centroid/square, high-LCM, moving-core, and singular-domain transport paid.
- **E:** R:SPEQuantileRieszRoutePLinearFloorCriterion; R:RoutePHyperbolicPairDeletion; R:RoutePLcmPairPayment; R:PaperAbelRoutePOrder.

<a id="pa"></a>
### PA — Prime–archimedean source passivity

- **Path:** Continued exact prime−archimedean trace → high-frequency passivity → RH.
- **Established [L]:** Finite-frequency trace and source recovery are exact. Signed current multiplier positivity on all upper half-strip slices is RH-equivalent; frequency cutoffs converge in norm. Absolute-current observations retain magnitude but erase orientation. Sharp prime-weight logarithmic-energy floor and rigidity do not give the sign.
- **Open:** Arithmetic sign of the high-frequency current numerator or equivalent all-order source lower bound.
- **E:** R:PrimeArchEndpointFrequencyAccretivity; R:PaperPrimeArchCurrentOperator; R:PaperPrimeArchSignErasure; R:PrimeWeightLogEnergyFloor.

<a id="mc"></a>
### MC — Möbius cancellation at half power

- **Path:** Signed Möbius source → half-power cancellation/subpower energy or square-sampled Chebyshev bound → RH.
- **Established [L]:** RH-equivalent Möbius Hilbert, Liouville, Riesz, and square-source receivers; exact signed bilinear and divisor decompositions pay small-modulus, low-product, and terminal regions. At every sufficiently large common scale, distinct actual primes realize any fixed compact Abel-clock target with arbitrarily small normalized diagonal cost and literal terminal singleton fibres.
- **Open:** Global signed bilinear bound: principal counterterm and high-product remainder jointly. Fixed-window realization does not bound scale-dependent targets, inherited histories, or cutoff drift.
- **E:** R:MobiusHilbertFormEquivalence; R:MobiusSquareResidueShortBilinear; R:MobiusDivisorPrimeClockRealization; R:MobiusDivisorPrimeClockTerminalControl.

<a id="tt"></a>
### TT — Theta-tail and heat–Cassini currents

- **Path:** Theta source → directed signed covariance/Wold decay or odd Weil-form sign → RH.
- **Established [L]:** Exact seam/tail and odd-four identities; sharp Wold boundedness threshold t<1/2 and natural-cutoff RH energy criterion. Odd/primitive Weil positivity has an exact half-line reflected-prime inequality and Φ-Doob form. Finite-prefix, sign-blind, and masked convergence do not control global sign.
- **Open:** Signed nonlocal covariance or full odd/primitive form positivity across all rapidities and test scales.
- **E:** R:XiHeatCassiniWoldNaturalSquareEnergySubhalf; R:PaperWoldDirectedCovarianceRH; R:WeilMarkovOddPositivity; R:WeilMarkovPrimitiveHyperplane.

<a id="la"></a>
### LA — Line anchor

- **Path:** Literal theta source → all-height Laguerre/Hadamard or Jensen sign → real-rooted Ξ → RH.
- **Established [L]:** Exact sign/zero-count receivers and finite-height/slice controls. Near-double off-line pairs and exceptional heights evade presently controlled finite data.
- **Open:** All-height arithmetic sign, including remaining low-order slices and an arithmetic separator for near-double off-line pairs.
- **E:** R:XiLogDerivReCriterion; R:XiSliceFiniteOrderReduction; R:PaperHeatSliceCriterion.

<a id="tg"></a>
### TG — Topological sub-unit gate

- **Path:** Pre-divisor Euler/Gaussian source → positive-residual cubic transgression and integer trace<1 → RH.
- **Established [L]:** Boundary winding/index and source-sensitive transgression identities; finite-scale and ideal/compactness gates do not orient the full reflection-odd prime−Gamma source.
- **Open:** Matrix-complete E_base=E_residual+Tr T_D with E_residual≥0 and all-disc sub-unit trace; alternate source-derived central-gap bound at exponent zero.
- **E:** R:FormationAnchoredCubicSpecialization; R:RestrictedProjectionIndexOperatorNormCriterion; R:GaussianCentralGapExplicitCriterion.

<a id="hf"></a>
### HF — Positive Hodge form on arithmetic cohomology

- **Path:** Original arithmetic cohomology → positive Hodge-compatible form, or full-positive arithmetic weight → RH.
- **Established [L]:** Full Weil positivity/PBAP are RH receivers; full-positive weights are rigidly Λ. Original Meyer quotient has global Xi-jet synthesis, faithful Hasse Hilbert admission, nondegenerate Paugam pairing, full-Jordan compact inverse with determinant Ξ, trace-class arithmetic flow/convolution and complete prime−Gamma−polar trace. One fixed Gaussian realizes every original class in the BV arithmetic graph; the original generator intertwines the literal native differential action and its compact Green inverse on the whole source image.
- **Source-only [S]:** Finite Weil nodal profiles and mixtures have unique optimal adjacent transport; no signed PBAP producer.
- **Open:** PBAP: source-derived nonnegative complete Weil form on unrestricted prime-blind tests, hence positive Hodge compatibility. Arithmetic cup/trace identification and Gaussian removal in native BV remain separate; spectral/source realization alone does not confine zeros.
- **E:** R:WeilPositivityPrimeBlindDuality; R:DeningerMeyerGlobalXiSynthesis; R:DeningerMeyerGlobalHassePaugamPairing; R:DeningerMeyerFredholmXi; R:DeningerMeyerFlowLefschetz; R:PaperThetaWholeMeyerGenerator; [S] R:FiniteWeilNodalMixtureTransport.

<a id="chmd"></a>
### CHMD — Causal Hyperbolic–Modular Duality

- **Path:** Exact Weil source → causal prime wave one-sided bound or theta-Doob resolvent odd-sector half-bound → RH.
- **Established [L]:** Toeplitz/sech positivity, one-sided Λ-prime-wave bounds, and absence of odd resolvent eigenstates above 1/2 are RH-equivalent. Full signed BV/Doob graph, bounded Weil operator, discrete finite-multiplicity spectrum above 1/2, and zero-sample/polar decomposition are constructed. Local odd sign and bounded kernel estimates do not give global positivity.
- **Source-only [S]:** Integrated Chebyshev-deficit/conjugated-kernel transport gives another equivalent one-sided pairing. No formal Möbius-tail sign payment in that unwired module.
- **Open:** Source-derived uniform one-sided signed discrepancy pairing, full Weil-operator positivity, or exclusion of odd bound states above 1/2.
- **E:** R:CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion; R:CHMDDoobSourceGraph; R:CHMDSpectralRiemannCriterion; R:CHMDOddSectorCriterion; [S] R:CHMDDeficitPrimitiveConjugatedTransportAndMobiusDilationInjection.

<a id="th"></a>
### TH — Theta moment positivity

- **Path:** Exact theta/prime−Gamma moments → all-degree Hankel/Bezoutian positivity → RH.
- **Established [L]:** Moment and heat-current receivers, finite-rank sign regions, and exact theta-source identities. Fixed-rank or bounded-window positivity does not select the all-rank branch.
- **Open:** All-degree positivity at one positive heat time or equivalent same-time phase/current sign with full discrete-prime remainder.
- **E:** R:XiHeatHankelFormOrthantPositivity; R:ThetaCuspC5OuterClockCurrent; R:XiGaussianHeatTraceCompleteMonotonicity.

<a id="rn"></a>
### RN — Theta renewal and singular comparison

- **Path:** Literal theta renewal/connection source → divisor-faithful winding or directed boundary-work sign → RH.
- **Established [L]:** Global compact native Green operator and whole-BV forcing solver retain the full arithmetic form. Every native generalized Xi root block equals the original Meyer packet with full multiplicity. Fixed-Gaussian whole-source native realization, full-range generator intertwining, and exact finite-packet repair/convolution preserve source data; none orients the signed work.
- **Source-only [S]:** Generic one-channel root projection/power solvability and exact native resonant moment order are not yet a root-imported native projection. Fixed Cauchy-pole quartet defect is nonnegative and vanishes iff RH; it is a zero-side receiver.
- **Open:** Mixed prime+Gamma≥pole inequality with all cusp terms, all-order seam/cusp projection, and arithmetic boundary-current orientation; Gaussian removal in native BV remains separate.
- **E:** R:PaperThetaNativeResolvent; R:PaperThetaNativeMeyerCompleteness; R:PaperThetaOriginalArithmeticRealization; R:PaperThetaWholeMeyerGenerator; [S] R:PaperThetaConfluentNativeChannel; [S] R:XiReciprocalSquareFixedCauchySource.

<a id="wd"></a>
### WD — Ward orientation and horizontal collision

- **Path:** Directed source current → global negative-cross control or collision charge<2 → RH.
- **Established [L]:** Exact Ward/collision receivers, source formation, global cap integrability, and strict-right multiplicity readout. The actual nonnegative cap vanishes iff RH; forming it is not a sign/cancellation proof.
- **Open:** Source-derived vanishing of global cap or full signed prime−Gamma contraction; uniform owner/absorber bounds for every zero block.
- **E:** R:XiWardCapGlobalIntegrability; R:XiWardGlobalCapRightZeroSum; R:XiWardCubicParabolicDirectionalMultiplicity.

<a id="li"></a>
### LI — Paired Li and prime–Gamma balances

- **Path:** Literal prime−Gamma history → signed lower floor → Li positivity → RH.
- **Established [L]:** Exact paired Li/source histories and finite primitive receivers; closed-ideal operators classify RH-equivalent compactness but do not supply arithmetic lower bounds.
- **Open:** Eventual Re H_N≥K_N−C on 0<t≤c log(2N+1), or equivalent finite lower bound for the literal primitive; retain first-crossing/outside correlations.
- **E:** R:LiEvenCrossActualClockGrowthLaw; R:LiSignAlongSquares; R:PaperLiNegativeOperator.

<a id="sz"></a>
### SZ — Suzuki screw and shifted-kernel limits

- **Path:** Complete signed boundary pairing → screw nonnegativity or shifted-Ξ confinement → RH.
- **Established [L]:** Screw/shifted-Ξ receivers, supported phase recovery, boundary/quantile identities, and positive Green inverse. Finite heads and almost-everywhere reconstruction do not give complete moving-source sign.
- **Open:** Source Wronskian law paying moving infinite head and shell leakage; uniform cusp-preserving passage to unshifted Ξ.
- **E:** R:SuzukiScrewPointwiseNonnegativityCriterion; R:SuzukiCanonicalShiftedXi; R:CCMUnitRieszSuzukiGreenPositiveInverse.

<a id="pm"></a>
### PM — Physical-model routes

- **Path:** FZZ or PW-B physical source → admitted Ward/energy identity → Haar approximation or growth receiver → RH.
- **Established [L]:** FZZ parity/Mellin and Haar receivers, witness signature, exact Fourier LlogL reconstruction with all cross-terms, and weak retarded realization.
- **Source-only [S]:** Literal complementary-rate retarded responses have compact-cutoff source-contact action and native-corrected wedge-exhaustion limit; action leaves are unwired.
- **Open:** Haar-target approximation and small-damping L² admission; PW-B source-contact action must imply optical magnitude, ordered cap, and all-divisor extinction. Pure-Ξ no-collision remains open.
- **E:** R:FermiNymanBeurlingHaarTarget; R:PaperFermiFourierCriterion; R:ThetaCuspHawkingBMPWRetardedWeakNative; [S] R:ThetaCuspHawkingBMPWNativeTwoResponseAction.

<a id="jas"></a>
### JAS — Joint ancestry

- **Path:** Arithmetic prime-product Weil form → level-one positivity on sufficiently large-prime tests → RH.
- **Established [L]:** Level-one full-product/dyadic constant-vector positivity and torus-density nonnegativity are RH-equivalent. Full signed L² torus density and finite-coordinate conditional expectations exist; typical phases and small prime budgets are positive unconditionally.
- **Open:** Source sign for exceptional constant vectors on sufficiently many shells, or all-amplitude damped shell positivity.
- **E:** R:JointAncestryLevelOneCapstones; R:JointAncestryLevelOneDensityCriterion; R:JointAncestryDampedShellCriterion.

<a id="ctf"></a>
### CTF — Chronological tail

- **Path:** Bounded chronological Bose/Möbius rows → vanishing L² error → RH.
- **Established [L]:** Bounded-row and dual sampling equivalences; unbounded rows are dense. Bounded vanishing-error rows force Möbius coefficients; off-line zeros force sharp-row escape.
- **Open:** Construct bounded rows with vanishing error, or prove dual sampling bound from arithmetic data.
- **E:** R:ChronologicalRiemannEquivalence; R:ChronologicalDualSamplingCriterion; R:ChronologicalMobiusEscape.

<a id="hcf"></a>
### HCF — Gaussian heat trace / critical feature variance

- **Path:** Exact arch−prime heat trace → one-sided vertical growth or rank-uniform Hankel positivity → RH.
- **Established [L]:** Heat-trace/chirp and all-rank Hankel criteria; fixed-rank positivity is unconditional. Singular Hankel blocks have exact inertia, Toda contact orders, escaping root branches, regular-head transfer, and signed kernel projections at every positive heat time, without genericity assumptions.
- **Open:** Source-derived one-sided prime-chirp bound or rank-uniform positivity selecting the no-transition branch.
- **E:** R:XiGaussianHeatRouteCapstone; R:XiGaussianHeatBlockInertia; R:XiGaussianHeatTodaMultiplicity; R:XiGaussianHeatRegularKernelProjections.

<a id="xn"></a>
### XN — Xi Newton invariant discs

- **Path:** Xi first-jet source → line-centered Newton self-map discs covering every zero → RH.
- **Established [L]:** Disc coverage/self-map and nonnegative interior margin are RH-equivalent. Actual-Xi margin satisfies ΔQ=4(r²−|z−c|²)|ξ″(z)|²≥0 inside each disc; boundary positivity alone does not force interior positivity.
- **Open:** Arithmetic construction of line-centered discs covering every zero with Q≥0 throughout; pay interior curvature Green potential.
- **E:** R:XiNewtonSchwarzPickCriticalLine; R:XiNewtonDiscSourceMargin; R:XiNewtonDiscCurvature.

## Route candidates

<a id="apf"></a>
### APF — Arithmetic paired Fredholm

- **Path:** Prime source → divisor exhaustion → Fourier-trace vanishing → RH.
- **Established [L]:** Fredholm index and actual cycle-trace Fourier reconstruction.
- **Open:** Zero-independent exhaustion/vanishing of all trace coefficients; the reconstructed coefficients already encode the off-line zero terms.
- **E:** R:PaperZetaCycleFourierReconstruction; R:PaperPrimeFredholmReconstruction.

<a id="bag"></a>
### BAG — Deterministic zeta self-return

- **Path:** Reflected approximate functional equation → unbounded physical self-returns on each right-strip disc → RH.
- **Established [L]:** Return receiver, weak-recurrence ladder, sharp physical cubic reduction and Fourier reconstruction. Random phase-cell returns and finite-window positive mass are not deterministic cofinal returns.
- **Open:** Complete signed axes/tail payment yielding common-height physical recurrence.
- **E:** R:ZetaStrongRecurrenceReceiver; R:ZetaWeakRecurrenceLadderCollapse; R:PaperZetaReturnSpectralCriterion.

<a id="bsh"></a>
### BSH — Arithmetic mate curvature

- **Path:** Literal prime−Gamma section → mate identity → orientation.
- **Established [L]:** Framed curvature/compact-ideal diagnostics distinguish on/off-line fibres; finite cutoffs are trace-blind.
- **Open:** Construct arithmetic section and mate identity without assuming the radial character is zero.
- **E:** R:DeningerOneSidedFramedMateCurvatureTransgression; R:PaperDeningerFramedCurvature.

<a id="cdc"></a>
### CDC — Constitutive dagger

- **Path:** Arithmetic presentation → neutral grade → source law.
- **Established [L]:** Calibrated dagger confluence holds exactly on the critical line.
- **Open:** One source-defined pre-divisor potential descending on all closed error fibres without assuming RH.
- **E:** R:ConstitutiveDaggerConfluence.

<a id="dr"></a>
### DR — Dyadic Xi roots

- **Path:** Global compatible dyadic roots on strict-right domain → zero-free Ξ → RH.
- **Established [L]:** Common zero-free cusp roots, finite monodromy/Kummer data and capped atlas; pole-regularized log-ζ convergence to every real σ>1/2 is RH-equivalent. Smooth prime-germ and naive positive-root producers fail in their stated classes.
- **Open:** Global continuation/monodromy and source convergence of the regularized series; finite covers do not supply a common root.
- **E:** R:XiSymmetricLittlewoodZeroFreeCuspDyadicRoots; R:XiTiltPuncturedMonodromy; R:RegularizedLogZetaAbscissa.

<a id="egc"></a>
### EGC — Pole-safe contour

- **Path:** Shifted contour source → complete residue cancellation → RH.
- **Established [L]:** Full copy correction converges on fixed shifts; Fourier reconstruction and source-ray decay retain all copies.
- **Open:** Expanding-contour cancellation/decay uniformly over the full copy sum.
- **E:** R:PaperEGCCompleteCorrection; R:PaperEGCFourierReconstruction.

<a id="ewj"></a>
### EWJ — Euler/Wold jets

- **Path:** Faithful third jets → exhaustive source budget → RH receiver.
- **Established [L]:** Exact finite-depth jets and compact-quotient character; fixed-history recovery misses transverse operator gaps.
- **Open:** Zero-independent admission and norm exhaustion, not finite-jet feasibility.
- **E:** R:PaperEulerWoldDepthHistory; R:PaperEulerWoldCompactCharacter.

<a id="ewu"></a>
### EWU — Even pole-weight uniqueness

- **Path:** One even-positive arithmetic weight → λ=Λ → RH.
- **Established [L]:** Even positivity at any finite pole weight forces λ=Λ and RH; even-polar and full-positive weight cones coincide. Single-source purification, exact fibres and blind minimizer attainment hold at every aperture.
- **Open:** Nonnegative attained blind minimum at every aperture, i.e. an arithmetic sign producer; attainment alone supplies no sign.
- **E:** R:EvenSectorPoleWeightUniqueness; R:EvenSectorFullPositivity; R:EvenSectorExactMomentRealization; R:EvenSectorBlindVariationalAttainment.

<a id="fel"></a>
### FEL — Theta likelihood

- **Path:** Predeclared likelihood history → zero/prime contrast balance → RH.
- **Established [L]:** Exact probability, conditional KL and finite reflection-gap accounting.
- **Open:** Source-derived cofinal zero-to-contrast balance; coarsening alone cannot select the line.
- **E:** R:PaperThetaObservationHistory.

<a id="gta"></a>
### GTA — Transverse Schur charge

- **Path:** Theta-stage source charge → uniform transverse decay → RH.
- **Established [L]:** Compactness/uniform decay of actual positive quartic Schur charge is RH-equivalent; finite truncations converge strongly even off RH. Several symmetrizing/positive-kernel substitutes fail.
- **Open:** Source-derived transverse-energy decay independent of the zero divisor.
- **E:** R:PaperThetaSchurSolidObservation; R:PaperThetaSchurModeCharge; R:PaperThetaSchurCompactGap.

<a id="hj"></a>
### HJ — Hurwitz reflection

- **Path:** Rational source fibres → reflection residual zero → RH.
- **Established [L]:** Hurwitz fibre/reflection and norm-observation receivers preserve the exact residual.
- **Open:** Independent arithmetic proof that residual vanishes.
- **E:** R:PrimeTailSeedHurwitzReflection; R:PaperHurwitzWallApproach.

<a id="irk"></a>
### IRK — Rotation-algebra trace

- **Path:** Arithmetic boundary defect → K₀/Chern landing → integral orientation.
- **Established [L]:** Finite-word traces, local winding and quotient-ideal diagnostics; trace rank+θ·Chern alone does not select the divisor.
- **Open:** Global arithmetic Poisson/projective lift with integral analytic count and correct source defect.
- **E:** R:PrimeRotationXiRelativeKTwo; R:PrimeRotationCanonicalTraceIntegrality.

<a id="msc"></a>
### MSC — Möbius−Sonin transport

- **Path:** Nonpower source transport preserving divisor/conormal → energy receiver.
- **Established [L]:** Real-power rigging moves the divisor; polynomial and broad LP multiplier transports cannot preserve the required Ξ preimage.
- **Open:** Nondiagonal, nonpower arithmetic transport mixing Dirichlet coefficients while preserving divisor and conormal.
- **E:** R:HedenmalmGammaSewnSquarefreeFisherThresholdTrackedRigging; R:XiRealRootedPolynomialPreimage.

<a id="owu"></a>
### OWU — Odd Weil-weight uniqueness

- **Path:** Odd-positive arithmetic weight → cut removal/ray sign → λ=Λ → RH.
- **Established [L]:** Odd positivity yields a Nevanlinna spectral measure and slit Herglotz continuation. Even mean-zero sign removes real-cut mass; one all-scale dilation ray plus odd positivity forces λ=Λ. Odd source purification, exact blind fibres and attained corrected ground eigenspace hold. Its transforms are precisely P(w²)F_G(w), deg P<dim S, with a common generator factor.
- **Open:** Nonnegative blind odd minimum, existence of an odd-positive arithmetic weight, and its all-scale ray sign. Ground factor need not be blind; no independent sign producer.
- **E:** R:OddWeilSpectralMeasure; R:WeilDilationRayCriterion; R:OddSectorBlindVariationalAttainment; R:OddSectorGroundPolynomialStructure.

<a id="pbm"></a>
### PBM — Prime boundary monodromy

- **Path:** Source boundary cancellation → no monodromy at infinity → orientation.
- **Established [L]:** Raw prime Dirichlet sum diverges for Re s<1; pole-regularized prime and log-ζ rows have the same RH-equivalent real abscissa but a nonzero compact-quotient gap 1/2. Regularization is not source cancellation.
- **Open:** Source-derived cancellation of regularized prime coefficients at infinity.
- **E:** R:RegularizedLogZetaAbscissa; R:PaperPrimeRegularizedIdeal.

<a id="pcs"></a>
### PCS — Singular co-shift

- **Path:** Singular ground → wall-class annihilation preserving forward mode → RH.
- **Established [L]:** Complex/wall ground is explicit. Finite-prime co-shift projections converge strongly but retain norm and compact-ideal wall gaps; fixed-history observations miss the gap. Reflection-odd wall class vanishes exactly on the line.
- **Open:** Source-natural annihilation of wall class without deleting the forward mode.
- **E:** R:PaperPrimeCoShiftCalkin; R:PaperPrimeCoShiftCofinalGap; R:PaperPrimeCoShiftSolidObservation.

<a id="ptr"></a>
### PTR — Photonic source

- **Path:** Prime-faithful lossless port/stack → real-rooted transfer limit Ξ → RH.
- **Established [L]:** Finite lossless stacks are real-rooted; field-density, thin-slab, cosine-defect and zero-count laws constrain any Xi limit. Finite Euler/local ports and fixed-depth resonance-free handoffs fail.
- **Open:** Gapless nonlocal prime-faithful continuum port preserving the exact Ξ divisor, or independent zero-loss theorem.
- **E:** R:PhotonicLosslessProductPortRH; R:PhotonicLosslessProductPortThinSlab; R:XiCosineShiftDefectZeroDensity.

<a id="rb"></a>
### RB — Robin/Nicolas divisor-sum criterion

- **Path:** Extremal divisor sums/primorial Mertens product → eventual Robin/Nicolas inequality → RH.
- **Established [L]:** Exact criteria; fixed k-free and positive exponent-defect classes satisfy partial margins.
- **Open:** Source sign on increasingly prime-saturated extremal integers/primorials at square-root remainder scale.
- **E:** R:RobinCriterionRiemann; R:NicolasInequalityRiemannConverse; R:RobinInequalityKFree.

<a id="rfhm"></a>
### RFHM — Support grade

- **Path:** Phase/depth/compound-faithful source → broken inverse covariance → wall law.
- **Established [L]:** Exact survival/KL/entropy accounting; reversible sewing remains inverse-covariant and cannot orient Reρ.
- **Open:** New source covariance/creation law retaining phase, depth and compounds.
- **E:** R:PaperRFHMSurvivalInformation.

<a id="sc"></a>
### SC — Stokes/Witt−Krein

- **Path:** Cross-fibre indefinite invariant → source orientation.
- **Established [L]:** Rigged fibres are chamber-constant; Fourier reconstruction has a common null set, but canonical polarization is wall-singular.
- **Open:** Source-fixed cross-fibre indefinite restriction/index selecting the critical wall.
- **E:** R:PaperKreinWallFourierCompletion.

<a id="sec"></a>
### SEC — Adjacent prime seam

- **Path:** Exact eventual compactness → zero jump → RH.
- **Established [L]:** Essential norm equals seam jump; compact-ideal cost is zero exactly for equal endpoint charges. Asymptotic smallness is automatic and nonselective.
- **Open:** Exact eventual compactness from the arithmetic source.
- **E:** R:XiPrimeSeamAdjacentEssentialNormNoGo; R:PaperPrimeSeamIdealTrace.

<a id="w1c"></a>
### W1C — Clifford–Dirac / centred Lee–Yang

- **Path:** Arithmetic operator/domain or centred ferromagnetic producer → real-rooted Ξ → RH.
- **Established [L]:** Bare operator lacks point spectrum/compact resolvent. Lee–Yang holds for finite ferromagnetic graphs; an Ising magnetization limit Ξ/Ξ(0) would imply RH. Field-density/centering constraints and LP-maximality exclude finite-order, fixed-depth and simple prime-log ports.
- **Open:** Source-defined couplings with centred slow-field law converging to Riemann's measure, or a faithful arithmetic scattering denominator; interaction-driven critical edge density required.
- **E:** R:WeightOneCliffordSpectralNoGo; R:LeeYangIsingGraphDatum; R:IsingLawConvergenceRH; R:RiemannKernelLaguerrePolyaSymbol.

<a id="wbf"></a>
### WBF — Source certificates

- **Path:** Arithmetic certificate stream → uniform-depth positive completion → Ξ landing.
- **Established [L]:** Finite genealogy Gram determinants recover coefficient magnitudes; critical relative determinants classify square-summable perturbations. Strong finite-prefix convergence and zero finite-prefix ideal cost coexist with infinite cost for nonzero completed genealogy.
- **Open:** Arithmetic stream and source-faithful depth-uniform completion landing on Ξ/Weil positivity; scalar Gram completion alone supplies no sign.
- **E:** H:PaperGenealogyFredholmRecovery; H:PaperGenealogyDeterminantGauge; H:PaperCriticalGenealogyCompletion.

## Shared constraints

- Finite jets, packets, and prefixes do not establish a cofinal sign; scoped failures and surviving routes: [killed routes](rh-killed-routes.md).
- Reflection-even or magnitude-only observations cannot supply reflection-odd arithmetic orientation. Full-positive perturbations of Λ under subcritical deviation are rigidly Λ. E: R:WeilLittleOVonMangoldtRigidity; R:EstermannDeformationObstruction.
- RH ⇔ zeros approach the line (ZAL) plus asymptotic abscissa law (AAL). Either condition alone misses residual off-line configurations. E: R:ZerosApproachLineAttainment; R:AsymptoticAbscissaLawProducers.
- Other RH receivers and falsifiers: [endpoints](endpoints.md); no independent source producer follows from a receiver.

## Alias lookup

C1→RW; CCM-FU→FU; CLG/TTF,K-RVM,S6F,TCD,UEB→TH; CSB,STC,U,MPLF,RHist,BPC,TQFQ,WS2,SQB→RN; D2,Q,RG,RG-ETA,TK→PA; E,EDQ,L,HDL,PSRC→MC; FZZ-P,PW-B→PM; G,HC→WD; O→WL/RW (genus mechanism dead); P,SP-E→RP; SV2,RG-HF→SZ; T1,T2,Route T→TT; Route T successor/ULF sub-unit anchor→TG; Deninger→HF. Retired labels: [killed routes](rh-killed-routes.md#retired-labels).
