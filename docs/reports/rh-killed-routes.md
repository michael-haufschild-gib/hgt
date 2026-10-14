# RH dead mechanisms and obstructions

**Scope:** dead = stated mechanism impossible, circular or nonselective. Survivor = retained theorem; **Needs** = changed problem outside obstruction. No-go for a shortcut does not retire its live route.

**Lookup:** [36 named mechanisms](#dead-mechanisms) · [19 retired labels](#retired-labels) · [route-class obstructions](#route-class-obstructions) · [ULF obstructions](#ulf-obstructions) · [endpoint no-gos](#endpoint-no-gos) · [scoped catalogue](#scoped-catalogue). Live routes/candidates: [frontier map](rh-current-frontier-map.md#find-a-route).

**Evidence:** codes as in frontier map; [L] cited Lean declarations, no fresh compilation; [P] paper only; REF = unlocated legacy evidence, unverified here. Conditional, model-only and class restrictions retained.

## Dead mechanisms

<a id="kr-aut"></a>
### KR-AUT — GL(2) automorphic positivity

- **Path:** Nonnegative trace formula + spectral estimates → zero confinement.
- **Obstruction:** ζ zeros occur as scattering poles, outside L² Parseval; nonnegative-test ceiling only c/logγ. [L] ceilings; [P] route verdict.
- **Survivor:** Kuznetsov/Parseval and deck-normalized spectral sieve. Twisted point-pair test-field Dirichlet threshold gives a Laplace eigenvalue in (0,¼); modular-λ winding tests have exact mass/gradient bounds. Neither places ζ scattering poles or gives an individual-zero producer [L].
- **Needs:** New arithmetic scattering/source control, not Laplace positivity alone.
- **E:** R:SelbergLedgerCeiling; R:KuznetsovExplicitIdentity; R:KuznetsovLargeSieveTheorem; R:RepPointPairSmallEigenCriterion; R:ModularLambdaTestEnergy.

<a id="kr-llm"></a>
### KR-LLM — Mollified Littlewood–Levinson

- **Path:** Off-line first moment / mollified mean square → no off-line zeros.
- **Obstruction:** Moment bounds do not imply pointwise vanishing. Gate floor exp(5R/3); fixed a>0,b₁=1,abs(b_d)≤1,length≤T^θ,0<θ<1 gives mean-square excess≥(1−θ)e^(−2a)T/16 [L]. Under assumed CGG main terms, polynomial mollifier optimum is `1−(1+θ)⁻³`; Feng orthogonal enlargement gives no gain, and θ=4/7 yields `988/1331<3/4` [L]. This is algebra conditional on the main terms, not a zero theorem.
- **Survivor:** Near-line density and sharp mollifier floors/optima.
- **Needs:** θ→1 or unbounded coefficients outside this class; even improved density needs individual-zero control.
- **E:** R:MollifiedGateConstantFloor; R:MollifiedMeanSquareGaussianPrimeFloor; R:SelbergExponentialNearLineDensity; R:ZetaCGGMollifierOptimum.

<a id="kr-gen"></a>
### KR-GEN — Genus / fixed-part selector

- **Path:** Fixed/equivariant vanishing → all zeros on wall.
- **Obstruction:** Localization erases free orbits.
- **Survivor:** Exact #support=#fixed+2#left; unlocalized boundary remains.
- **Needs:** Unlocalized source vanishing; WL/RW.
- **E:** R:BoundaryMapImage.

<a id="kr-ucf"></a>
### KR-UCF — Uniform free-orbit count

- **Path:** Mass/average control → angular energy below first quantum.
- **Obstruction:** Averages/reflection-even readers miss charge; holomorphic inverse-square sum≠angular energy; critical Sobolev does not give L∞.
- **Survivor:** Exact sub-quantum receivers; isolated-zero Hermite falsifier.
- **Needs:** Actual angular/Poisson source bound with all domain/isolation hypotheses.
- **E:** R:AngularEnergyQuantization; R:CriticalLinePoissonPotential; R:LocalHermitePositivity.

<a id="kr-teq"></a>
### KR-TEQ — Transverse equilibrium

- **Path:** Theta equilibrium + maximum principle → confinement.
- **Obstruction:** Xi ODE mechanism unavailable; cutset condition vacuous.
- **Survivor:** Equilibrium plus attained maximum ⇒ RH.
- **Needs:** Source equilibrium and nonattained-maximum control; LA.
- **E:** R:TransverseEquilibrium; R:TransverseMaximumPrinciple.

<a id="kr-cal"></a>
### KR-CAL — Pair heat / collision monotonicity

- **Path:** Backward heat pair control → RH.
- **Obstruction:** Negative-time collisions do not refute RH; proposed reverse pair/Lyapunov bounds unavailable.
- **Survivor:** Positive-time multiple zero refutes RH. Nonreal count finite, antitone, zero for t≥1/8; right-limit equals Xi off-real count [L].
- **Needs:** Independent exclusion of nonzero initial branch; LA.
- **E:** R:DeBruijnNonrealCountRightLimit; R:DeBruijnNewmanCollisionCriterion.

<a id="kr-dsa"></a>
### KR-DSA — Discrete escape indicator

- **Path:** Integral escape count → automatic vanishing.
- **Obstruction:** Escape indicator re-encodes off-line count.
- **Survivor:** Pre-divisor primitive/sub-unit budget.
- **Needs:** Source-to-divisor transgression; TG.
- **E:** CANNOT-193r; MUST-130r; P3:escape-multiplicity-offline-indicator-lean.

<a id="kr-int"></a>
### KR-INT — Integral finite-rank Frobenius

- **Path:** Integral lattice + Frobenius norms → purity.
- **Obstruction:** Three distinct prime actions incompatible with nonreal ρ in stated finite-rank lattice; torsion unitary.
- **Survivor:** Precise finite-rank obstruction; infinite-rank scaling geometry remains.
- **Needs:** Infinite-rank compatible Hodge construction; HF.
- **E:** R:DeningerCarrierNoIntegralLattice; R:FrobeniusTorsionLaw.

<a id="kr-twn"></a>
### KR-TWN — Twin / half-divisor parity

- **Path:** Twin factorization → even divisor → confinement.
- **Obstruction:** Requires analytic square root first; odd critical multiplicities defeat fixed parity.
- **Survivor:** Root-tower/nonvanishing receiver.
- **Needs:** Global continuation/monodromy; DR.
- **E:** R:TwinRigidity; R:TwinFactorization.

<a id="kr-nev"></a>
### KR-NEV — Termwise Nevanlinna / HB sign

- **Path:** Maximum principle → full Xi sign.
- **Obstruction:** Required zero-free domain already unknown; termwise argument circular.
- **Survivor:** Exact sign receiver.
- **Needs:** Independent source sign; SZ/PA.
- **E:** R:NevanlinnaSignCriterion; R:SuzukiXiDonoghueTarget.

<a id="kr-isg"></a>
### KR-ISG — Prime-Ising and invalid ferromagnetic limits

- **Path:** Balanced prime Ising trees → Lee–Yang Xi limit.
- **Obstruction [L]:** Balanced prime trees and integer-anchored Γ-site chains fail the Xi limit. For every ferromagnetic Ising graph sequence, constant normalization cannot converge to `E·Ξ`: total field must diverge and phase must asymptotically center at half-field. Centred Griffiths–Simon sequences containing harmonic masses `1/(2k)` from any `K≤7` also fail. GHS plus Lebowitz inequalities do not imply Lee–Yang.
- **Survivor [L]:** Arbitrary ferromagnetic graphs satisfy Lee–Yang; centred convergence in law, moments or low-frequency real-rooted approximation to `Ξ` implies RH. Slow-field producers require vanishing free variance and interaction-driven magnetization. Field-density and first-zero budgets remain necessary.
- **Needs:** Source-faithful centred critical graph sequence outside harmonic/anchored classes; W1C.
- **E:** R:PrimeIsingTreeBalancedCentering; R:LeeYangResolutionLaw; R:LeeYangPrimeStabilityNoGo; R:RiemannSiegelLeeYangChain; R:GammaSiteLeeYangChainXiObstruction; R:LeeYangProducerFieldDensity; R:ComplexFugacityChainFieldDensity; R:LeeYangIsingGraphDatum; R:IsingGraphCenteringLaw; R:IsingHarmonicMagnetizationNoGo; R:IsingSlowFieldCriticality; R:IsingLawConvergenceRH; R:IsingMomentConvergenceRH; R:FerromagneticInequalitiesLeeYangBlind.

<a id="kr-fpr"></a>
### KR-FPR — Fixed finite passive realization

- **Path:** Finite passive source carrier → Xi passivity.
- **Obstruction:** Exact fixed finite realization impossible.
- **Survivor:** Passivity receiver; growing carriers allowed.
- **Needs:** Cofinal arithmetic source sign; PA.
- **E:** R:PrimeArchPassiveResponseRH; R:MobiusIncidencePassiveCompletionNoGo.

<a id="kr-def"></a>
### KR-DEF — Deformation-stable inequalities

- **Path:** Euler/FE-compatible estimates → RH.
- **Obstruction:** Single-prime Euler deformation preserves stated inequalities and plants off-line zeros.
- **Survivor:** Sharp need for deformation-sensitive arithmetic rigidity.
- **Needs:** Cross-modulus/source rigidity; MC/HF.
- **E:** R:EstermannDeformationObstruction.

<a id="kr-crt"></a>
### KR-CRT — Fixed-aperture finite-horizon positivity

- **Path:** Finite Hodge certificate → all-height exclusion.
- **Obstruction:** Finite aperture/depth cannot reach arbitrary height or arbitrarily shallow zeros.
- **Survivor:** Conditional Nyquist horizon ~2πe^(2a), depth loss and negative-index law.
- **Needs:** Source positivity at every aperture; RW/HF.
- **E:** R:TiltedClusterNyquistExclusion; R:TiltedWeilSpectralSeparation.

<a id="kr-trc"></a>
### KR-TRC — Trace-ideal transport

- **Path:** S₁/fixed-AP source carrier → faithful Xi divisor.
- **Obstruction:** Riemann–von Mangoldt capacity mismatch; Xi inverse S₂ but not S₁; bounded bridge false.
- **Survivor:** det₂ and logarithmic-squared Ky Fan capacity.
- **Needs:** Singular, divisor-faithful comparison; RN/TG.
- **E:** R:SourceInverseTraceIdealNoGo; R:MertensClockDefectTraceClass.

<a id="kr-apw"></a>
### KR-APW — Approximate prime weights

- **Path:** Sieve/smoothed/prefix weights → full Weil positivity → RH.
- **Obstruction:** Full-positive λ≤Λ or λ≥Λ forces λ=Λ without growth hypotheses. Subcritical absolute/one-sided deviation likewise rigid; nontrivial deviations have critical abscissa one. Approximation cannot evade exact arithmetic.
- **Survivor:** Sharp rigidity boundaries; conditional harmonic/composite, spectral and deficit rigidity. Finite-block deficit forces a quantitative visible excess-mass budget [L].
- **Needs:** Construct full-positive source and handle mixed critical singular deviation; HF.
- **E:** R:WeilLittleOVonMangoldtRigidity; R:WeilFullConeMinorantRigidity; R:WeilFiniteBlockExcessMass; R:WeilWorkSingularArithmeticCompositeRigidity; R:WeilWorkQuantizationRealPeriodicRigidity.

<a id="kr-jpr"></a>
### KR-JPR — Automatic Jensen hyperbolicity

- **Path:** High-shift hyperbolic Jensen polynomials → RH.
- **Obstruction:** n³log²(n+2)≥Kd⁵ hyperbolicity unconditional; this regime nonselective.
- **Survivor:** First failure degree≥cn^(3/5)log^(2/5)(n+2).
- **Needs:** Control outside automatic saddle regime; LA.
- **E:** R:XiJensenPolynomialRiemannHypothesis.

<a id="kr-tor"></a>
### KR-TOR — Independent phase transfer

- **Path:** Steinhaus/torus AFE statistics → physical zeta orbit.
- **Obstruction:** Torus and flow log-means differ; physical phase law missing.
- **Survivor:** Exact required AFE phase-law identity.
- **Needs:** Prove deterministic physical phase law; BAG.
- **E:** P1:rs-phase-locking-geometric-mean-law.

<a id="kr-ref"></a>
### KR-REF — Translation implies reflection positivity

- **Path:** Toeplitz prime Gram positivity → Hankel reflection positivity.
- **Obstruction:** Reflection diagonal negative at arbitrarily large squares; factorial multiplier not PSD.
- **Survivor:** Carrier must retain valuation grade and abundant two-torsion.
- **Needs:** Different grade-faithful reflection carrier; WL/RW.
- **E:** CANNOT-397; CANNOT-392r; MUST-398.

<a id="kr-cpf"></a>
### KR-CPF — Pole-minus-source Carleman positivity

- **Path:** Common radial positive covariance → Xi positivity.
- **Obstruction:** Carleman pole fails to dominate prime-2 atom; polar–Gamma counterterm has no finite radial form [L].
- **Survivor:** Exact prime/divisor signed rate measures.
- **Needs:** Joint signed compensation in another admitted domain; RW.
- **E:** CANNOT-294.

<a id="kr-tmd"></a>
### KR-TMD — Global formation primitive

- **Path:** Construct global primitive → RH.
- **Obstruction:** Primitive existence is RH endpoint itself.
- **Survivor:** Integral formation index and compact-descent receiver.
- **Needs:** Independent source proof of vanishing.
- **E:** F0082; CANNOT-62.

<a id="kr-tk"></a>
### KR-TK — Thermodynamic ensemble change

- **Path:** Cooling/ensemble limit → independent positivity.
- **Obstruction:** Limits reduce to same scalar PA defect.
- **Survivor:** PA receiver.
- **Needs:** Complete signed source sign; PA.
- **E:** PA; F0155.

<a id="kr-bag"></a>
### KR-BAG — Finite Euler recurrence

- **Path:** Finite Euler carriers + vanishing tail / conditioned means → zeta recurrence.
- **Obstruction:** Finite Euler zero-free winding barrier; conditioning retains smooth-ratio cross terms; vanishing dual edge insufficient.
- **Survivor:** Full reflected AFE random targets and complete cubic/axes reductions; live BAG candidate.
- **Needs:** Signed complete physical axes action and deterministic common-height self-return; BAG.
- **E:** R:FullReflectedAFECompactTarget; R:ChiPrimeGaussianCubicLocalAxesReduction.

<a id="kr-sel"></a>
### KR-SEL — Selberg eigenvalue gaps

- **Path:** Laplace gap → zeta zero confinement.
- **Obstruction:** Eigenvalue gaps do not locate scattering poles.
- **Survivor:** 3/16, arithmetic spectral gaps and finite-level quarter-gap infrastructure.
- **Needs:** New scattering-pole arithmetic input; PM/HF.
- **E:** R:SelbergConjectureStatus; R:SelbergThreeSixteenths; R:SelbergMaassStripHardyGap.

<a id="kr-r1"></a>
### KR-R1 — Anchored chiral-loss passage

- **Path:** Weak H^(1/2) Euler→Xi passage + negative chirality<1 → RH.
- **Obstruction:** Anchored losses balance κ₋=κ₊; bounded Gaussian passage ⇔ RH, diffuse failure not finite-energy bubbles [L]. Only this passage mechanism retired.
- **Survivor:** Disc cubic=winding; zero-free contraction; finite-height/density seam bounds.
- **Needs:** Fixed-source matrix-complete cubic transgression and all-disc sub-unit bound; TG.
- **E:** R:AnchoredPhasePassageRigidity; R:GaussianPassageBoundedUnderRiemannHypothesis; R:XiRightDiscPhaseIndexRiemannHypothesis.

<a id="kr-r2"></a>
### KR-R2 — Dyadic renewal winding

- **Path:** Prime-2 self-similarity R₂ → zero winding.
- **Obstruction:** Anchored R₂ loops realize arbitrary odd winding [L]; Mellin-diagonal self-similarity alone nonselective. Full RN route not retired.
- **Survivor:** R₂ distinguishes undeformed theta within polynomial family; R₂+inversion gives zero-charge cusp [L]. R₂+weight-½ modularity forces scalar theta [P].
- **Needs:** Euler/square-lattice-sensitive winding law; RN.
- **E:** R:ThetaGroupDeformationPrimeTwo; R:ThetaCuspChargeModularCriticality; R:ThetaCuspChargePolynomialRigidity.

<a id="kr-r3"></a>
### KR-R3 — Holomorphic collision quantum

- **Path:** Holomorphic two-prime excess<2 → no off-line collisions.
- **Obstruction:** Holomorphic excess is zero or unbounded; collisions FE-forced and stable. Quantum slack supplies no growth bound [L]. Pair/second-moment residual not retired.
- **Survivor:** Quantization and RH receivers; high-order slices; singleton/isolation density.
- **Needs:** Actual negative-cross/mixed-class control; every-height low-order sign; WD.
- **E:** R:XiHolomorphicTwoPrimePencilGrowthDichotomy; R:XiLineUnimodularClockExcessCriterion; R:XiSliceFiniteOrderReduction.

<a id="kr-raw"></a>
### KR-RAW — Raw positive prime Dirichlet series

- **Path:** Convergence of raw `ΣΛ(n)n^(−s)/log n` or `Σ_p p^(−s)` on `Re s>½` → zero-free log ζ / monodromy.
- **Obstruction [L]:** Both diverge at every `Re s<1`, with or without RH; nonnegative coefficients fix abscissa 1.
- **Survivor [L]:** Pole-subtracted coefficients `(Λ(n)−1)/log n` and `1_P(n)−1/log n` have convergence on every real `s>½` iff RH.
- **Needs:** Independent signed Chebyshev/prime-count cancellation for regularized series; DR/PBM.
- **E:** R:LogZetaDirichletDivergence; R:RegularizedLogZetaAbscissa; CANNOT-500/501; MUST-883.

<a id="kr-bd"></a>
### KR-BD — Cofinal Markov ground-state positivity

- **Path:** Beurling–Deny/Markov inequality for even regular screw kernel at every aperture → nonnegative grounds → RH.
- **Obstruction [L]:** First Beurling–Deny inequality for that kernel plus any scalar L² shift holds iff `2a≤log(plastic constant)`; no cofinal Markov passage through this form. Prime atoms only help the inequality.
- **Survivor [L]:** Sharp sub-horizon disjoint-support sign; independent cofinal nonnegative-ground receiver remains valid.
- **Needs:** Global spectral or arithmetic ground-state mechanism outside Markov class; RW/SZ.
- **E:** R:SuzukiScrewBeurlingDenyAperture; MUST-887.

<a id="kr-ptr"></a>
### KR-PTR — Local Maxwell collar prime landing

- **Path:** Rotating local Maxwell transmission collar admits literal critical prime conormals → Xi interface.
- **Obstruction [L]:** Full variable-coefficient interface sidebands decay rapidly; critical prime conormals cannot be admitted. Fixed prime-log/integer half-rate stacks also violate lossless field-density bound.
- **Survivor [L]:** Lossless temporal-stack entries have real zeros; Xi is their locally uniform product limit iff RH. Thin-slab continuum/nonlocal ports remain outside obstruction.
- **Needs:** Exact arithmetic source-to-continuum handoff retaining Xi divisor; PTR/W1C.
- **E:** R:PhotonicCorotatingCollarTraceRegularity; R:PhotonicLosslessTemporalStackRealZeros; R:PhotonicLosslessProductPortRH; R:PhotonicLosslessProductPortDensityLaw; R:PhotonicLosslessProductPortThinSlab.

<a id="kr-hfr"></a>
### KR-HFR — Fixed-rank heat-Hankel completion

- **Path:** Positivity of finitely many heat-Hankel determinants at every heat time → RH.
- **Obstruction [L]:** Rank-`N` tests cannot see off-line zeros above `O(N√log N)` ordinate height. At small heat time, all-rank positivity on the coefficient orthant or stable-root cone holds unconditionally. A bounded `aN` window constant is below the known RH-equivalent growing-window criterion.
- **Survivor [L]:** Large-time matched-rank inertia counts off-line pairs exactly; positive-node tests detect them. RH ⇔ positivity in every `a=K/N` window, for every `K>0`, equivalently every growing window constant.
- **Needs:** Rank-uniform arithmetic sign or unbounded window growth; HCF/TH.
- **E:** R:XiGaussianHeatHankelHeightHorizon; R:XiGaussianHeatHankelLinearHorizon; R:XiGaussianHeatHankelLargeTimeDetection; R:XiGaussianHeatHankelLargeTimeInertia; R:XiGaussianHeatHankelPositiveNodeWitness; R:XiGaussianHeatHankelSincLevelWitness; R:XiHeatStableTestPositivity; R:XiHeatHankelFormOrthantPositivity.

<a id="kr-hus"></a>
### KR-HUS — Averaged Husimi slice positivity

- **Path:** Positive Gaussian-height-averaged slice at every resolution → pointwise Xi-slice positivity → RH.
- **Obstruction [L]:** Same Husimi identity holds for an Euler-blind Gaussian-cosine source with non-real transform zeros and a negative slice coefficient; Husimi density has zeros at every resolution.
- **Survivor [L]:** Exact averaged positivity with its uncertainty cost; direct slices detect mixed off-line classes in a nonempty interval.
- **Needs:** Theta-specific pointwise coefficient sign beyond the averaging bandwidth; WD.
- **E:** R:XiSliceHusimiPositivity; R:XiSliceHusimiZero; R:XiSliceHusimiEulerBlind; R:XiDirectMixedMultiplicityLaw.

<a id="kr-gap"></a>
### KR-GAP — Fixed-gap lossless realization

- **Path:** `Ξ(t)=Re G(t+ih)` for a lower-Pólya function `G` and fixed `h>0` → RH.
- **Obstruction [L]:** No such realization exists: it would make all zeros simple with rigid consecutive gaps, contradicting the zeta anti-crystal law. Allowing finitely many shallow resonances in a fixed strip does not evade the obstruction.
- **Survivor [L]:** Exact positive sech/Poisson handoff from `Re ξ(1+it)` to `Ξ`; any lossless Hermite–Biehler realization has infinitely many resonances arbitrarily close to the real axis.
- **Needs:** Prime-faithful gapless/nonlocal port; PTR/W1C.
- **E:** R:XiGaplessRealizationLaw; R:XiGaplessRealizationAccumulation; R:ZetaZeroAntiCrystalLaw; R:XiCosineShiftSechHandoff; R:XiCosineShiftPoissonFlow.

<a id="kr-ccp"></a>
### KR-CCP — Restricted-Weil parity selector

- **Path:** Cofinal even ground states of the restricted Weil form → RH.
- **Obstruction [L], scoped:** A finite off-line top layer with even ordinate relations has arbitrarily large apertures whose ground states are all odd. The same occurs for every fixed-shape cluster at sufficiently large height, regardless of relations. Thus parity selection fails for these off-line spectra; the general infinite-spectrum case is not classified.
- **Survivor [L]:** Exact finite-top ground-energy asymptotics and Cauchy/Takagi phase law; full all-aperture energy receiver remains.
- **Needs:** Joint prime–Gamma–polar source lower bound, not parity alone; RW.
- **E:** R:CCMParityTopLayerNoGo; R:CCMParityTopLayerGroundEnergyLaw; R:CCMParityLargeHeightCluster.

<a id="kr-cos"></a>
### KR-COS — Local cosine-to-Xi port

- **Path:** Finite-order/local/compactly carried operator maps `cos(hD)Ξ` to `Ξ` and preserves real zeros.
- **Obstruction [L]:** No finite-order polynomial-coefficient differential port, finite imaginary-shift port, compactly supported shift-average port or compactly carried analytic port gives the exact map for `h≠0` in its stated class, before zero preservation is considered.
- **Survivor [L]:** Exact nonlocal sech/Poisson source handoff; cosine defect counts bound deep zeros and are power-saving sparse at each fixed positive depth.
- **Needs:** Nonlocal prime-faithful zero-loss mechanism for the actual Xi source; PTR.
- **E:** R:CosineProducerLocalPortObstruction; R:CosineProducerShiftPortObstruction; R:CosineProducerMeasurePortObstruction; R:CosineProducerAnalyticPortObstruction; R:XiCosineShiftDeepZeroBudget; R:XiCosineShiftDefectZeroDensity.

<a id="kr-poi"></a>
### KR-POI — Positive Poisson zero preservation

- **Path:** Positive sech/Poisson port preserves real zeros of every real-rooted source → Xi real-rootedness.
- **Obstruction [L]:** For every nonzero port depth, a two-tone real-rooted source `cos 2t+r cos t` gains a nonreal zero exactly when its lower-tone ratio crosses `cosh c/cosh 2c`.
- **Survivor [L]:** Port is exact, positive, injective and dense-range on the actual source; zero-loss remains possible only with Xi-specific structure.
- **Needs:** Actual-source zero-count or phase law through the port; PTR.
- **E:** R:PoissonPortTwoToneZeroLoss; R:XiCosineShiftSechHandoff; R:PaperPoissonContinuumPort.

## Retired labels

- **A** (no-go-097). Kill: fixed source-faithful physical-phase transport is the identity; universal positive Markov feasibility, source-trace Hankel positivity and canonical residue closability are exactly RH; finite Euler orbits and higher grades blind. Survivor: phase-natural rigidity, trace/resolvent identities, moment-germ inversion. E: REF.
- **AF** (no-go-180). Kill: copywise convergent class-law certificates exist exactly at centered rate zero, global ones exactly under RH; nonneutral adaptive responses evacuate admission mass; the charged Xi boundary loop keeps a positive uniform floor against every zero-winding approximant. Survivor: charged loop with quantitative separation; a successor needs the singular archimedean cusp or a global charged aggregate. E: REF.
- **AP** (no-go-164). Kill: Big-Witt/scaling-site completed-Xi pullback impossible in the stated architecture; surviving stability and preperiodicity conditions are RH. Survivor: Witt, sheaf, Galois, perfect-closure geometry. E: REF.
- **B** (no-go-100). Kill: scaling/grading and distinct prolate parameters cannot share the required unitary transport. Survivor: relative graph and boundary deformation. E: REF.
- **C2/I** (no-go-101). Kill: finite theta/dyadic width saturates its coordinate; the missing width is RH-bearing. Survivor: Cauchy/Hurwitz interfaces (→ PA). E: REF.
- **D1** (no-go-102). Kill: finite/local moment positivity does not orient the completed all-degree source. Survivor: continued D2 tail (→ PA). E: REF.
- **F** (no-go-136). Kill: bounded/sublinear compact Sonin completion has the wrong order, loses its floor or collapses the source; literal regularized F2 weld and Hausdorff synchronization excluded (no-go-137, 139). Survivor: principal/relative/singular assemblies outside these premises. E: REF.
- **FD2** (mechanism no-go-237). Kill: trace-faithful polarization cannot supply the missing divisor orientation; full-defect decay fails. Survivor: exact Xi occurrence, persistent nonnormality (→ candidate GTA). E: REF.
- **G2** (no-go-142). Kill: the required relative-Volterra germ is RH. Survivor: G's marked Ward boundary (→ WD). E: REF.
- **H** (no-go-145). Kill: even Taylor factorization erases orientation. Survivor: relation-valued indefinite primitive. E: REF.
- **HB** (no-go-341). Kill: generic cusped-Fuchsian Green/Stokes/KMS structure survives off-line scattering deformations; fixed native-L² on-shell realization fails [L]. Survivor: retarded weak realization and √Y-growth receiver. Needs: distributional/action admission and pure-Xi no-collision; PM. E: R:EisensteinMaassSelbergLineModel; R:ThetaCuspHawkingBMOnShellClearedNativeL2NoGo; R:ThetaCuspHawkingBMRetardedCompactWeakRealization.
- **IW** (no-go-163). Kill: internal Weyl-model existence is the desired divisibility; global existence is RH. Survivor: cyclic clock–shift model, divisibility classification. E: REF.
- **J** (no-go-146). Kill: for `L_m=6 log m`, `m ≥ 25`, bad energy `≥ log m/20` at every Julia scale; no uniform unrenormalized budget; off-diagonal cancellation cannot remove unit-diagonal mass. Survivor: residual-jet, determinant and radius bilinear-response laws. E: REF.
- **K** (no-go-150). Kill: the quadratic spectral mechanism cannot retain the marked source; every exact self-adjoint Xi determinant carrier is forced to reciprocal-Xi singular values, Schatten abscissa one, genus one. Survivor: changed infinite operators (→ TH, RN). E: REF.
- **M** (no-go-151). Kill: the saturated Gamma–Jacobi carrier has no positively normalized inclusion-compatible cyclic reader; anchored cofinal flatness is RH. Survivor: complete receiver (F0095). E: REF.
- **N** (no-go-152). Kill: response equality, endpoint contractivity and bounded polar work are each RH. Survivor: shared receiver for L, P, G. E: REF.
- **R** (no-go-156). Kill: global intrinsic formation/completion vanishing is RH; bounded ingress/egress cannot carry nonzero cofinal anomaly; canonical Noether action vanishes on every carrier. Survivor [L]: marked Roos/wall class h_a, h_a=0 iff a=0; internal positive energy zero, external tensor curvature survives off wall. Needs: source law annihilating full divisor class; CDC/JAS/WBF/TG. E: R:NilpotentMonodromyCriticalLineChain; R:RouteRExternalTensorMonodromy; R:RouteRHyperbolicNoetherAction; R:XiNoetherAdjointDomain.
- **RBH** (mechanism no-go-225). Kill: complementary/wall finite parts and separated-sign or passive production are blind or RH receivers. Survivor: changed nonseparated, nonlinear or singular datum (→ PM). E: REF.
- **SNR** (no-go-186). Kill: the reporter aperture realizes an arbitrary positive target height independently of the source. Survivor: a source-native aperture invariant is required. E: REF.

## Route-class obstructions

Each obstruction applies only to its stated hypotheses.

- Zero-side thin lag sampling — Single-base, two incommensurable bases, and any countable family of progressions can miss a non-attained off-line top in locally finite positive/sector-positive configuration models [L]. Positive weights can also have subexponentially rare excursions; exponentially rare excursions force on-line. Survivor [L]: actual integer/prime-power sets with power-saving gaps decide RH via arithmetic thickness; a non-meagre set of spacings decides RH by Baire; one bounded progression plus ZAL decides RH. No-chain plus bounded-above lag outside lower-density-zero scales decides RH; an attained off-line top forces positive-density excursions. No counterexample to actual zeta. E: R:WeilLagFunctionSingleBase; R:WeilLagTwoBaseWolffConfiguration; R:WeilLagCountableChain; R:WeilLagSubexponentialExcursionBlind; R:WeilLagFunctionExponentialExceptionCriterion; R:WeilLagPowerGapSampling; R:WeilLagFunctionProgressionBaire; R:WeilLagFunctionDensityZeroExcursion.
- Smooth compact nonpositive-energy blindness — For a mean-zero smooth compact core blind at every integer `n≥2`, the critical-line second moment equals `2πΨ_f(1)`; `Ψ_f(1)≤0` forces `f=0` [L]. Survivor [L]: any nonzero blind core must have `Ψ_f(1)>0`; divisor-weighted moments, periodization, primitive energy and collar laws constrain this case. The result does not exclude a positive-energy or noncompact witness. E: R:CosDilationKernelPositivityRigidity; R:CosDilationDivisorMomentPeriodizationRigidity; R:CosDilationPrimitiveEnergyRigidity; R:CosDilationCollarAnnihilationRigidity.
- Finite-pole full integer blindness — Finite Poisson superpositions achieve every finite blind cutoff; with poles distinct modulo integer translates, they cannot be blind at all sufficiently large integer frequencies [L]. Survivor [L]: twisted-arc minimum principle constructs an all-integer-blind decay-class witness (N1); PBAP remains open. E: R:FinitePoissonDecayWitness; R:FinitePoissonBlindRigidity; R:TwistedArcMinimumPrincipleProof.
- Compact short-support full blindness — A continuous dilation core with support ratio `β/α<5/3` and integer-blind cosine–dilation kernel vanishes [L], without a sign premise on `Ψ_f(0)`. Survivor [L]: Gauss–Farey recursion and the all-integer N1 witness; larger support remains unexcluded. E: R:CosDilationBlindFiveThirdsSupportVanishing; R:InversionSymmetricFourierBlindRigidity; R:TwistedArcMinimumPrincipleProof.
- Nonunit Weil pole weight — Full-cone positivity at pole weight `β` forces `β=1`; prime-blind positivity at `β≠1` is impossible [L]. Survivor [L]: the exact `β=1` cone is `{Λ}` under RH and empty otherwise; PBAP at that weight remains open. E: R:WeilPoleWeightForcedOne; R:WeilConeUniquenessUnconditional.
- Pole-free Dirichlet transfer of ζ-cone uniqueness — Large conductor makes the Dirichlet archimedean symbol nonnegative with zero weights (odd `q≥4π`, even `q≥128π`); odd conductor `q≥5` also admits a single-node Weil-positive weight [L]. Thus ζ's pole-based cone uniqueness does not transfer to these pole-free symbols. Survivor: retain conductor, parity and arithmetic source. E: R:DirichletArchimedeanSymbolPositivity; R:OddDirichletSingleNodeConductorThreshold.
- Unmasked full Wold operator admission — Literal full matrix has no bounded ℓ² realization for `t≥½` [L]; finite square norms diverge. Survivor [L]: near-window compactness for `2t+η<2`, critical even-composite bounded/noncompact compression, and a fixed ±1 full-matrix mask compact for `t<¾`; no unit-modulus mask is bounded at or above `¾`. Integrated arithmetic covariance and source sign remain open. E: R:PaperWoldBoundedDomain; R:PaperWoldCompositeDomain; R:PaperWoldWalshDomain; R:PaperWoldPhaseBoundedDomain.
- Positivity alone — reflection, Hermitian, KMS, Markov, positive carriers; positivity supplies no upper bound (CANNOT-03, HARD LOCK P). [L] Positive prime-shift current/scaling energy can coexist with a negative source Bezoutian; Gamma/pole shift coefficient has both signs. At arbitrarily large actual prime resonances, `0<Q(|u|)<Q(u)` with both energies positive, surviving every continuous local scalar potential; the opposite modulus ordering also occurs. No universal modulus monotonicity or positive Noether Xi jump form (R:ThetaNoetherEulerFluxSeparation; R:ThetaGammaPolarScalingKernel; R:ThetaPrimeResonantModulusDecrease; R:CCMPrimeResonantNoetherWitness; R:CCMThetaModulusObstruction).
- Local positivity/conservation alone — arbitrary fine finite localization has positive/coercive pieces and exact mass/energy balance, but its signed continuous invariant `C=Q+2P` has no uniform lower bound per mass; all-chain prime error is bounded while continuous error is unbounded below. Finite separated prime-island spaces remain positive in all dimensions but are not dense/nested. No global full-form sign follows (R:CCMFiniteLocalizationCover; R:CCMPrimeLocalizationStabilization; R:CCMContinuousRayleighUnbounded; R:CCMPrimeIslandCoercivity).
- Prime-edge-only coercivity or raw pole-compressed norm exponent — exact pole-constrained fixed-aperture sources have nonzero mass and `E_a→0`; supported coherent Γ cost stays positive, so neither mass nor full supported cost is `≤C E_a`. The edge-null sequence escapes positively through Γ. Two-prime edge kernel is only the pole vector; constrained kernel vanishes, but qualitative interpolation has no cofinal rate. Independently, `‖P_{V₀}T_aP_{V₀}‖≥e^a/(64a)` unconditionally by high-frequency resonance (CANNOT-474); its norm exponent is always 1. Near-null theta radical caps positive level-`a` Weil margin by `O(exp(12a−πe^{2a−1/2}))`. Survivor: archimedean-relative Γ+edge+polar joint form control (R:CCMPrimePoleSchurConstrainedEscape; R:CCMCoherentGammaSchurSeparation; R:PoleFreePrimeTranslationResonance; R:WeilMarginSuperexponentialLaw).
- **DG-PRIME-CD0** Pointwise nonnegative cutoff-prime curvature. Kill [L]: throughout `log2<a<log(5/2)`, Γ₂(log2) is unbounded below in every positive exact-pole form-norm ball, with arbitrarily small full |Q|; not a negative Weil witness. Survivor [L]: sharp four-squares minus rank-one defect, zero iff six samples constant after compensation. At a=log2 compact endpoint values vanish, Γ₂≥0, equality iff all six real samples zero. At every aperture, all ordered two-jump samples at any finite probe set can be made silent on a form-norm dense exact-pole fibre; its Rayleigh infimum stays μ₀(a). Integrated Γ+prime+polar compensation open. E: R:CCMPrimePoleCurvatureRankOne; R:CCMPrimePoleCurvatureCompactOnset; R:CCMFiniteCurvatureProbeGroundRigidity; R:CCMPrimePoleCurvatureBounds; P3:rw-prime-curvature-compact-source-onset; P3:rw-finite-curvature-probes-ground-rigidity; P5:prime-jump-nonnegative-curvature.
- Scalar retained-frequency covariance as a cofinal positive-margin certificate — smooth exact-pole near-radical spaces have dimension `≥e^{2a−4}/20` and `|Q_a|≤exp(−e^{2a−4})‖f‖²`; any scalar positive-frequency Gram ceiling exceeds `α≥2exp(−e^{2a−4})` for large aperture. Survivor [L]: exact signed retained-kernel bound with strict positive outer-shell saving; source sign and uniform energy bound open. E: R:CCMSmoothNearRadical; R:CCMFrequencyCovariancePacking; R:CCMRetainedKernelStrictSaving.
- Bounded raw critical cubic prime kernel on `ℓ²(primes)` — `h(p)=log p/p`, `K(p,q)=√(h(p)h(q))·2√(log p log q)/(log p+log q)` has unbounded positive Rayleigh quotients; no bounded operator has those matrix entries, over ℝ or ℂ. Survivor [L]: finite kernel identities; a cofinal source-framed/singular relative cubic boundary remains open. E: R:PrimeLogCriticalCubicKernelNoBoundedOperator.
- Finite physical point-sample repair — at any finite distinct interior samples, exact-pole constrained smooth sources isolate one coordinate with value 1 and arbitrarily small form norm and `|Q|`; no positive-diagonal finite sample matrix has a bound by `C|Q|`. Stronger exact survivor: every arbitrary finite sample prescription has a form-norm dense source fibre and leaves the constrained ground infimum unchanged. Fourier/nonlocal features and stronger topologies not excluded (R:CCMConstrainedPointCapacity; R:CCMFinitePointGramObstruction; R:CCMFiniteSamplingGroundRigidity).
- Natural Wold critical square-energy producer — Kill [L]: ΣR_N² and ΣR_N²/(1+log N) diverge; quantized critical-wall residue survives both repairs. Survivor [L]: some wall s₀=ρ−1, Re s₀=−1/2, multiplicity m≥1, forces prefix energy >c log N cofinally for every 0<c<m²/|s₀|². Positive no-go closure/sharp critical loading formalized; equality/asymptotic not asserted. Signed covariance/directed arithmetic means remain open. E: R:XiHeatCassiniWoldNaturalSquareEnergyEndpoint; R:XiHeatCassiniWoldNaturalLogCriticalEnergy; R:XiHeatCassiniWoldNaturalCriticalPrefixLoading; R:XiHeatCassiniWoldNaturalPrefixEnergyAbelBounds.
- TT pointwise centered curvature / phase-only timelike cancellation — Kill [L]: distinct-prime p,q curvature at third prime r equals `2logp logq−8(logp+logq)−4logr+36`, unbounded below. Dephased timelike kernel differs from1 by ≤5|a|L²/u; nonnegative packets retain full pair mass up to this error. Survivors [L]: exact divisor/cofactor curvature and complete twisted-product law; natural Wold near-increment absolute sum finite for 2t+η<1. Open: full signed far covariance. E: R:XiMassCenteredDivisorMixedCurvature; R:XiMassTimelikeBilinearFlattening; R:XiHeatCassiniWoldNaturalNearIncrementBudget.
- TT radius-polynomial / inherited diagonal flux repair — Kill [L]: twelfth-jet border retains positive sixth Gaussian moment against every fixed lower-jet combination; canonical odd-three diagonal load creates an odd-four negative direction at scale7, unaffected by nonnegative new-diagonal load. Survivors [L]: exact positive admissible load interval below canonical coefficient, all-order reflected Cauchy tail. Open: coupled head/border matrix flux. E: R:ThetaCuspPolynomialFluxBorderDegree; R:ThetaCuspInheritedOddCompensationBoundary; R:ThetaCuspReflectedCauchyTail.
- All-even LI Euler-jet positivity — Kill [L]: every positive actual mass has both jet signs cofinally, cubic source poles ±8m. Survivor [L]: exact first-negative order log(1/v)/log4, two-layer boundary drift, actual-current positive window `(n+1)²v≤25` and entire clock margin; eventual actual F≥0 would force RH. E: R:LiEvenCrossRealEulerJetBridge; R:LiEvenCrossEulerFirstNegativeOrder; R:LiEvenCrossEulerSourceBoundaryLimit; R:LiEvenCrossActualCurrentPositiveWindow.
- Fixed-prefix/fixed-fraction LI completion compensation — Kill [L]: log(2N)<2π gives e^(−2t)F_N→−1; N=1 has F₁<−(91/50)sinh(2t) for all t>0. Full completion C>0, but actual eta/gap-to-C ratio→−1; every loss fraction θ<1 fails, including joint growing windows. Survivor [L]: exact F_N=C−K_N+H_N, positive Gamma/dyadic completion, finite-partition Volterra positive area and completed contiguous MODEL sign. Open: literal arithmetic Re H_N≥K_N−C, not inferred from normalized F_N→0. E: R:LiClockPairedEtaShortPrefixAsymptotic; R:LiClockPairedEtaPositiveCompletion; R:LiClockPairedEtaArithmeticJointCancellation; P3:li-clock-first-prefix-gamma-exact-sign; P3:li-clock-finite-partition-volterra-positive-area; P3:li-clock-contiguous-comparison-window.
- LI radial-density monotonicity — Kill [L]: every literal N≥2 partition ratio is neither monotone direction, including a.e. versions. Survivor [L]: sharp Borel/moment ceiling κ=(Z_U/Z_A)²>1; normalized infinite density ratio λ∈(0,5040/5041); noncommuting limits/opposite gap escapes; exact signed mixed forcing 2H*B_W=D_N, B_W≥1 with common-disk guards. Critical transition t=L/4+u√L and strict-supercritical exterior laws; quarter-disk vanishing-error bounds fail. Open: inverse-clock sign. E: R:LiClockPairedEtaPartitionDensityRatio; R:LiClockPairedEtaInfinitePartitionDensityTail; R:LiClockPairedEtaPartitionMixedSource; R:LiClockCriticalAngularAsymptotic; R:LiClockPairedEtaInfinitePartitionSupercriticalRatio.
- LI increasing mixed-kernel slope — Kill [L]: genuine q=B_W′/B_W has t²q_∞′→−1; a strict decrease persists in every sufficiently large finite logarithmic window. Survivor [L]: exact full mixed-source integral, all fixed derivative limits and literal relative forcing. Pointwise inverse-clock sign remains open. E: R:LiClockPairedEtaPartitionMixedLimit; R:LiClockPairedEtaPartitionMixedSignBoundary.
- LI eventual one-sign derivative/forcing — Kill [L]: h=F′ and G=h″−ω²h each have both strict signs cofinally, unconditionally. Survivor [L]: admitted whole-line massive Green identity; RH-conditional resonant variation/threshold-density laws; primitive P+P⋆B′=tB′ and RH ⇔ eventual finite P lower bound. Aggregate positive areas/forcing inverses do not produce original clock sign. E: R:LiEvenCrossActualClockDerivative; R:LiEvenCrossActualClockDerivativeOscillation; R:LiEvenCrossActualClockPrimitiveVolterra; R:LiEvenCrossActualClockPrimitiveNegative.
- LI ordinary natural-jump degree compound Poisson — Kill [L]: actual degree law not CP for any p>0, including zero intensity/zero jumps. Survivor [L]: broader arbitrary-weight mixture membership; p>1 exact degree/Gamma positive CP convolution, integer-time product/order coupling and bounded-monotone integral order. Whole Gamma-law positive-jump CP ⇔ RH for p>1 [L]; original signed density/fractional-time positivity open. E: R:LiClockThetaSignedGammaPositiveJumpCriterion; R:LiClockThetaSignedGammaCoupling; R:LiClockThetaSignedGammaJumps; P3:li-clock-signed-gamma-coupling; P5:li-clock-degree-compound-poisson.
- LI absolute exponential history envelopes — Kill [L]: norm-majorant/envelope-budget ratio→∞ for every M,γ>0; guarded failure need not be nonvacuous, no M15 counterexample. Survivor [L]: complete source/score admission; at guarded first zero `303Cout=I_U−I_R−303I_K`, I_U,I_R,I_K≥0, `I_R≥(1−θ)I_U` for one θ∈(0,1). M15 iff `I_U−303V≤I_R+303I_K`; positive boundary and D-history retained, primitive P-history still signed. Open: actual signed budget. Finite guarded-zero classification/empty iff RH [L]; exact guarded budget β_budget<ρ, so eventual guards are vacuous. E: R:LiEvenCrossActualClockTerminalHistory; R:LiEvenCrossActualClockScoreBudget; R:LiEvenCrossActualClockSourceCorrelationEnvelope; R:LiEvenCrossActualClockHistoryBarrier; R:LiEvenCrossActualClockHistoryRetention; R:LiClockThetaCompactGammaMarking; R:LiClockThetaScoreMeasure; R:LiEvenCrossActualClockScoreCorrelation; P3:route li/li-clock-terminal-history-boundary.
- Heat transport as same-time Xi positivity — `|H_t−H_s|≤(83/81)(K_s−K_t)` controls change only; for every `s<t` and nonzero polynomial ideal, normalized native energy at `s` can become arbitrarily small at all later times, with full residual and mixed terms small. No degree-uniform reverse retention or auxiliary negative-spectral-interval Gram floor. Survivor: independent same-time phase/source sign (R:XiGaussianNativeHeatDissipation; R:XiGaussianHeatRetentionObstruction; R:XiGaussianSpectralIntervalObstruction).
- TH coarse eighth-moment growth absorption — Kill [L]: dominant-pair coarse residual negative at modular center; bare atom defeats cubic monomial loss at q=5/3; factor-sixteen reserve fails at enlarged q=3/2. Survivors [L]: full pair-relative transfer>0, original transfer<0, sourceGrowth>0; C5 seam, Green recovery, local inverse-clock order, enriched Bose budget and complete current>0 on 2≤t≤u. Open: coupled current on 0<t≤u,t<2, full C5 comparison and arbitrary-degree positivity. E: R:ThetaCuspCurvatureDefectGrowthResidualCenterObstruction; R:ThetaCuspCurvatureDefectGrowthPureNextSource; R:ThetaCuspCurvatureDefectGrowthGlobalPropagation; R:ThetaCuspC5OuterClockCurrent.
- TT fixed coupled odd-four seam direction — Kill [L]: original direction 168q−56 has a common negative actual seam vector for every C4≤10^13, canonical C3 retained. Survivor [L]: optimal direction −B/D3 gives a positive-definite seam at C4=10^13; a continuous actual-source direction attains that value and exactly cancels Schur transport residual. Open: scalar Schur-gap positivity and controlled join to the proved tail direction; integrated/all-rank closure. E: R:ThetaCuspCoupledOddSeamObstruction; R:ThetaCuspCoupledOddDirectionTransport; P5:tt-coupled-four-fixed-direction-seam.
- TH pointwise-positive C5 compensation kernel — Kill [L]: actual compensation kernel negative on diagonal. Survivor [L]: -K and -K_t represented by positive source/Green kernel; compensation/Green ratio strictly decreasing, at most one sign crossing. Open: sign of full source-weighted integral, not pointwise kernel positivity. E: R:ThetaCuspC5PositiveDescentIntegral.
- RN uniform local source orientation — Kill [L]: source log jets have both signs beyond every order; normalized row neither globally convex nor concave; source-only single-axis sign cannot force both ports; center inverse feedback exceeds scalar drift. Survivors [L]: full-tail rank-two PD; global confluent coordinate residual>0 for every y>0; exact joint-center Hessian and source-deficit convexity give ONE e>0 with both actual ports>0 for ALL 0<z<y<e. Open: global finite-pair/general-anchor compensation, arbitrary rank and arithmetic RH transfer. E: R:ThetaCuspLogJetOscillation; R:ThetaTailNormalizedRowCurvature; R:ThetaTwoNodePortBoundaryClassification; R:ThetaTwoNodeCenterFeedback; R:ThetaTailConfluentCoordinateGlobal; R:ThetaTailNormalizedSchurHessian; R:ThetaTailCenterSourceConvexity; R:ThetaTailSmallNodePorts.
- TG raw linear-prime nuclear admission — Kill [L]: original S_p=p^(−1/2)C_a(D_p+D_(1/p)) has p Re Tr S_p→2(Phi_a(1)+1)>0; trace/operator family not summable. Survivors [L]: exact positive trace coefficient; complete ORIGINAL proper-prime-power nuclear summability; Γ relative remainder response, physical maximal domain and fixed-Schwartz-test Hardy nuclear/cubic limit. Open: native principal prime–polar energy, completed joint arithmetic cubic and strict sub-unit bound. E: R:SoninLinearPrimeTraceObstruction; R:SoninProperPrimePowerNuclearAssembly; R:SoninGammaRemainderResponse; R:SoninGammaClockPhysicalDomain; R:SoninGammaClockNuclearLimit.
- TG prime-only jet LCM support — Kill [L]: j=μ*ω has complete LCM self-convolution −j; nonprime/beyond-cutoff labels contribute. Survivors [L]: exact Möbius/gcd prime-power incidence; complete prime–polar reciprocal-maximum covariance = positive cumulative-square energy + terminal square, both unequal cross terms retained. Γ physical-domain and fixed-test Hardy gates closed separately. Open: original x^(−2) arithmetic energy and joint Hardy/sub-unit transfer. E: R:SoninPrimePolarJetLcmCovariance; R:SoninGammaClockPhysicalDomain; R:SoninGammaClockNuclearLimit; P5:tg-prime-only-jet-lcm-support.
- Arbitrary-coefficient Möbius-source positivity — the actual two-index short-source matrix at `T=2log 2` has determinant `−1`; no PSD argument for every coefficient vector. This does not test the literal Möbius vector. Survivor: `D(T)=B(T)+O(e^{T/2})`; continuous boundary-corrected `W=B+2Σ_{n≤⌊e^{T/2}⌋}μ(n)R(log n)` satisfies `|D−W|≤(T²+34T+112)/8`. RH ⇔ either `B` or `W` is `O(e^{T/2})`; signed work cancellation open (R:CCMPrimeDeficitShortSourceMatrix; R:CCMPrimeDeficitShortQuadraticWork; R:CCMPrimeDeficitEntryBoundaryBounds).
- Stationarity/fixed Euler renewal as Möbius bound — Kill [L]: stationary μ action survives arbitrary long-tail changes yet comparison source has value Te^(T/2); fixed modulus P>0 retains `(1+γ)(φ(P)/P)²Te^T` signed renewal pole, not even O(e^T). Survivor [L]: complete finite source pole=`e^T[((1+γ)T+d)m₀²−2(1+γ)m₀m₁]`; nullspace exactly harmonic-neutral m₀=0. Moving-label remainder≤C(T+1)²(Σ|v_i|)²; diffuse μ completion pays complete linear channel and absolute diagonal at critical scale. Open: signed unequal-label/tail-block quadratic work. E: R:CCMPrimeDeficitCoefficientAction; R:LogarithmicReconstructionSymmetryTest; R:CCMPrimeDeficitEulerSignedPole; R:CCMPrimeDeficitCompletePole; R:CCMPrimeDeficitNeutralWork.
- Universal dyadic insertion energy ordering — literal Möbius four-atom insertion ratio tends to `283/192>1`, while literal eight-atom ratio tends to `q<4/5`; neither contraction nor expansion is universal. Survivor: collective signed annular insertion law for the full cofinal source (R:MobiusPrimeInsertionLiteralPackets).
- Global Mertens centering as bounded Γ–Hankel replacement — for any array and `0<r<2`, `E_N(a_N;r)+E_N(a_N−P_N²;r)→∞`, `P_N=∏_{p≤N}(1−1/p)`; neither term alone must diverge. Survivor [L]: literal signed cross/noncomparable cancellation or a non-global, source-faithful centering. E: R:GammaHankelGlobalCenteringCost.
- MC termwise completed double-pair payment — Kill [L]: full a,2a pair retains μ(a) sign for odd squarefree a, q≥2048a, 1≤r≤2; both signs cofinally. Survivor [L]: sharp positive signed margin ≥a*q^(−r−1)/64, exact dyadic cofactor kernel, critical upper boundary ≤1/q and full-block cutoff-completion cost ≤6/q (r=1,A=q−1). Open: collective signed cofactor estimate. E: R:RouteECompletedDoublePairParity; R:RouteEDyadicCofactorKernel; R:RouteECofactorCutoffStability.
- MC small signed factor-count vertical interpolant — Kill [L]: complete finite signed interpolant at σ=3/4 has norm ≥exp(D^(4/3)/(4096logD))/2 for large D, `7π/(16logD)≤t≤15π/(32logD)`, N≥floor(2D^(4/3)). Survivor [L]: highest-parameter dominance including all lower binomial terms. Open: signed Mellin inversion/pole cancellation; no Möbius-energy or RH refutation. E: R:MobiusFactorCountPrimeWork; R:MobiusFactorCountEulerGrowth; R:MobiusFactorCountInterpolationDominance.
- RP absolute complete-fibre / pointwise coprime payment — Kill [L]: absolute high-LCM fibre variation V satisfies `V(4N)/((4N)^3*sqrt(4N))≥1/(4N)` eventually; sampled critical series diverges. Native coprime cross term is <−u(t)² for some t, so pointwise coprime positivity fails. Survivors [L]: complete fibre=2a(p)a(q) for distinct primes p,q≤M with pq>M; exact zero-limit coprime-square Mellin budget with positive first coefficient. Open: signed cancellation BETWEEN full LCM fibres and integrated moment-cancelled coprime history; no continuous-integral divergence inferred. E: R:RoutePLcmAbsoluteObstruction; R:RoutePCoprimeSquareMellin; R:RoutePCoprimeSquareNative; R:RoutePCoprimeSquareSign.
- PM analytic weighted inputs as canonical Haar convergence — Kill [L]: PNT/log-saving weighted inputs admit power models with divergent canonically centered variance above exponent ½; fixed raw Möbius Fermi sequence has a cofinal positive Haar-error floor. Survivors [L]: literal logarithmic approximation converges in L²(t dt); exact canonical variance decomposition, sharp power-boundary classification; canonical fixed-log convergence forces critical-zero simplicity. Actual canonical convergence not excluded/proved. E: R:FermiNymanRawMobiusTailFloor; R:FermiNymanLogMobiusWeightedEndpoint; R:FermiNymanLogMobiusAuxiliaryVariance; R:PMAnalyticPowerBoundary; R:PMLogMobiusBoundaryMultiplicity.
- PM damping/prime-cutoff contraction — Kill [L]: norm-increasing canonical prime steps arbitrarily near ε=0; every subunit budget exceeded. Large damping forces later growth, excluding eventual damping monotonicity. Hilbert tangent D∉L²(dt); every finite quotient norm budget exceeded near zero. Survivors [L]: admission ε≥½; all-positive-ε L¹, linear Haar convergence, exact tangent/mean log2 and weighted L²(t dt). Zeroth-order cofinal small-positive admission open. E: R:PMPowerDampedMobiusEndpoint; R:PMPowerDampedMobiusPrimeGrowth; R:PMPowerDampedMobiusLargeDamping; R:PMPowerDampedMobiusL1Convergence; R:PMPowerDampedMobiusDerivative; R:PMPowerDampedMobiusDerivativeMellin; R:PMPowerDampedMobiusDerivativeBoundary; P5:pm-power-damping-hilbert-tangent.
- PM uniform prime-subset/prime-aperture norm budgets — Kill [L]: every finite all-subset norm budget uniform near ε=0 fails; at each fixed 0<ε<½ canonical prime-aperture norms→∞. Survivors [L]: odd-Möbius dyadic Haar resolvent energy2/mean0; arbitrary finite deleted-prime source has exact positive smooth-Haar Gram energy ≥reciprocal Euler product, diverging with prime cutoff; common absolute aperture budget ε>½. Endpoint ε=½ aperture classification and actual infinite-source admission below½ open. E: R:PMPowerDampedMobiusDyadicResolvent; R:PMPowerDampedMobiusDyadicDeletion; R:PMPowerDampedMobiusHaarGram; R:PMPowerDampedMobiusHaarSeries; R:PMPowerDampedMobiusSmoothHaar; R:PMPowerDampedMobiusFiniteDeletion; R:PMPowerDampedMobiusFiniteSmoothSource; R:PMPowerDampedMobiusPrimeThreshold; P5:pm-dyadic-prime-deletion-unit-budget; P5:pm-finite-prime-deletion-energy; P5:pm-canonical-prime-aperture-threshold.
- PM raw positive-divisor Haar cutoff — Kill [L]: energy/N→α_ε²(2−2log2)>0 at every ε>0; L¹ error floor |α_εlog2|. Survivor [L]: sharp rescaled boundary profile, energy2−2log2/mean−log2. Density repair gives clipped centred source with endpoint trace |R_ε(N)|²/N; full-sequence L² convergence under admission iff trace→0; cofinal trace-zero sequence exists. Endpoint Haar correction removes trace, converges at every integer cutoff under admission; corrected uniform energy budget ⇔ admission ⇔ exact integral/discrete centred divisor energy. Actual small-positive bound open; strict coefficient variance forces diagonal/logN→v_ε>0; admitted source forces off-diagonal/logN→−v_ε, unconditional for ε≥½. This cancellation law has no proved small-positive energy bound. E: R:PMPowerDampedMobiusPositiveHaarPrefix; R:PMPowerDampedMobiusHaarBoundaryProfile; R:PMPowerDampedMobiusCenteredEnergy; R:PMPowerDampedMobiusDiscreteEnergy; R:PMPowerDampedMobiusClippedHaarSource; R:PMPowerDampedMobiusHaarCutoffTrace; R:PMPowerDampedMobiusEndpointHaar; R:PMPowerDampedMobiusSecondMoment; R:PMPowerDampedMobiusCovarianceCancellation; P5:pm-positive-divisor-haar-boundary-profile; P3:pm-centered-haar-cutoff-trace; P3:pm-endpoint-corrected-haar-prefix.
- PM separate Ramanujan pair/support budgets — Kill [L]: actual Möbius-aligned q,pq cross energy eventually positive for fixed non-prime-power squarefree q>1, ε>0; completed-prime-support energy exceeds every multiple of bounded logarithmic coefficient-square mass at 0<ε<1/2. Nearby-prime cofactor covariance is unbounded even after reciprocal-mean removal. Survivors [L]: exact prime-insertion Gram identity, positive continuous dilation profile and natural-cutoff signed source-change boundary. Open: complete natural-denominator energy, not support-independent or termwise control. E: R:PMPairedRamanujanGram; R:PMRamanujanCompleteAperture; R:PMRamanujanCutoffPrimeBalance; R:PMRamanujanNearbyPrimeResonance.
- PM isolated growing-cofactor sector budget — Kill [L]: at cutoff P² and 0<ε<1/2, whole large-prime/cofactor sector L_P has divergent original-head energy. Survivor [L]: for complete prefix S_P=L_P+C_P on 1≤N<P, `E(S_P)/E(L_P)→0`, `E(C_P)/E(L_P)→1`, `Re⟨L_P,C_P⟩/E(L_P)→−1`; exact leading cancellation of two divergent sectors. Finite complete-band Mellin symbol retains ζ(s)/s times full signed divisor polynomial. Open: residual global energy for ε↓0; head cancellation still leaves a positive-power ceiling. E: R:PMRamanujanGrowingCofactorHead; R:PMRamanujanComplementarySourceBounds; R:PMRamanujanComplementaryCancellation; R:PMRamanujanBandMellin.
- PM compact normalized complete-band profiles — Kill [L]: ∀ε>0 ∃c>0 ∀totally bounded K⊂L² ∀B ∃real X≥max(1,B), normalized full natural band distance≥c from EVERY F∈K, in frequency/original log carriers. Integer version: ∃c>0 ∀fixed G ∀B ∃n≥B with distance≥c; integer bands neither converge nor are Cauchy. Survivor [L]: real-cutoff common-radius escape, exact floor/one-atom transfer to integers, fixed Fourier/dilation transport. Bounded noncompact motion not excluded; no uniform compact-family integer/every-dyadic assertion. Open: dyadic sampling and small-damping complete-energy ceiling. E: R:PMRamanujanBandSpectralEscape; R:PMRamanujanBandPhysicalSeparation; R:PMRamanujanBandNoncompactEnergy; R:PMRamanujanBandIntegerSeparation; P3:pm-ramanujan-band-integer-separation; P5:pm-compact-normalized-profile-closure.
- PM exact prime-power geometric spectra — A hyperbolic subgroup whose every trace is a prime-power length trace cannot contain primitive lengths `log p` and `log q` for distinct primes [L]. A finite unitary quantum-graph scattering matrix whose secular determinant factors exactly over prime blocks must be block diagonal [L]. Survivors: mixed, nonfactorized arithmetic dynamics or a different source-faithful spectral realization; no Xi landing follows. E: R:HyperbolicPrimeLengthSpectrumObstruction; R:QuantumGraphPrimePowerDecoupling.
- SZ prescribed/raised shift as direct Xi target — Kill [L]: actual prescribed-shift V2 carrier→0 locally uniformly on upper half-plane; every raised-shift schedule collapses on 1/2<s<1. Xi target has nonzero first defect. Survivor [L]: every nonzero admissible fixed-source limit requires relative margin (E+d)/(E+c)→0 and actual defect y=dx−p with e^(−a)‖y‖≥η>0, ‖y−(C/‖C‖)y‖/‖y‖→0. No raised-family whole-domain or single-ground-eigenspace conclusion. Open: sub-prescribed spectral-edge signed residues, unshifted positivity and Xi identification. E: R:SuzukiTaV2PrescribedCarrierCollapse; R:SuzukiRaisedMetricShiftCarrier; R:SuzukiSpectralMarginNecessity; R:SuzukiSpectralSourceDefectQuasimode; P5:sz-prescribed-shift-direct-xi-identification.
- MC summable scalar Dirichlet square root — Kill [L]: ∃δ>0, ∀0<t<δ, w_t(n)=e^(−nt)/n has no absolutely summable complex Dirichlet-convolution square root. Survivor [L]: complete prime-phase source has an interior simple zero at every sufficiently large real scale; actual center, cofactor responses, repeated primes and derivative retained. Literal Liouville sign/half-power cancellation open. E: R:LiouvillePrimeBandSimpleZero; R:LiouvilleExponentialWeightNoSquare; P3:mc-exponential-weight-phase-zero; P5:mc-exponential-weight-scalar-square-root.
- MC separate moving hyperbola head / shifted-pole repair — Kill [L]: A_θ=Σ_(m≤x^θ)μ(m)W(x/m), P=Σ_(n≤x)λ(n)(x/n−1); EVERY0<θ<¾,d∈ℝ,c≠0 has δ>0 with dP+cA_θ=Ω±(x^(1−θ/2)), unconditionally. Separate subcritical payment fails at EVERY such cut. Survivor [L]: exact transported exponent/rightmost-zero contraction separation; any eventual one-sided bound at that exponent forces RH. θ=½ gives A_θ−ζ(2)xΣ_(m≤√x)μ(m)/m=o(x^¾); separated shifted pole and exact coefficient rigidity retained. Open: joint head/remainder cancellation; c=0 raw P/K NOT excluded. E: R:LiouvilleTriangularShortHead; R:LiouvilleTriangularPoleSeparation; R:LiouvilleHyperbolaCutoffOscillation; R:LiouvilleHyperbolaCutoffWide; R:LiouvilleHyperbolaCutoffThreeQuarter; R:LiouvilleHyperbolaCutoffSharp.
- MC absolute squarefree-discrepancy contraction — Kill [L]: for actual E(x)=Σ_(n≤floor x)μ(n)²−ρx, ρ=6/π², absolute response exceeds 1 near a=½. Survivor [L]: signed response q(a)=a/ρ∫₁∞E(x)x^(a−2)dx is <1 for real 0<a<½, tends to 1; complex q(a)=1 iff ζ(1−a)=0 on 0<Re a<½. Absolute-minus-signed gap uniformly positive for ¼≤a<½. Actual signed Liouville comparison open. E: R:SquarefreeDiscrepancyMellin; R:SquarefreeDiscrepancyCriticalGap.
- RP independent biased two-channel saving — Kill [L]: every fixed k<1 improvement fails cofinally for native θ=1−1/p projection. Survivor [L]: covariance=(A_p−θA₁)²+(1−θ²)A₁²; divided by M→2c₀²/p, c₀>0. Full biased signed covariance uniformly comparable to native energy on finite causal windows for nonnegative damping, all common-prime/off-diagonal pairs retained. No absolute energy ceiling. Joint positive-damping work/high-LCM/history payments open. E: R:RoutePBiasedPrimeProjection; R:RoutePNativeSignedPairComparison; R:RoutePNativeCovarianceWindow.
- RP separate late-prime mixed payment — Kill [L]: native critical h has infinite L¹ mass; full mixed work is not absolutely admitted on any late ray for ε<½. Its literal primitive Q exceeds every C exp(bt) cofinally for 0<ε<½,b<½−ε. Survivors [L]: t²J(t)→−D/3; exact removal jumps, admitted damped reciprocal coefficients and corrected FTC retain all atoms. No eventual-sign/oscillation claim. Joint square, positive-damping negative work, signed high-LCM and both history debts open. E: R:RoutePNativeLatePrimeMixedAdmission; R:RoutePLatePrimeReciprocalFTC; R:RoutePNativeMixedGrowthBarrier.
- RP causal mass-compensation replacement — Kill [L]: for damping∈[0,1], complete coprime source of a+λ∫₀ᵀa is admitted iff λ=0. Survivor [L]: mass primitive has total D/3>0; dilation source/e^T→λD/3, complete coprime source/e^T→(λD/3)²/ζ(2); exact energy retains original square and terminal mass square. Cutoff-dependent zero-total-mass completion/native positive-damping energy open. E: R:RoutePNativeMassCompensation; R:RoutePNativeMassPrefixMoments; R:RoutePNativeMassCoprimeAdmission; R:RoutePNativeMassCoprimeAsymptotic.
- TT coarse affine third-slope cone — Kill [L]: actual q>b(h), b=1/12−7h/72, plus strict coarse cone still admits negative static slope. Survivor [L]: along t=r*b(h)+a*h², `Q=h²B`, `B(0)=54C(144a−r²)`, C>0; both strict sign regions, equality open. Actual nonlinear law `q−(9−u²)q²>b` holds for EVERY x>0. Uniform nonlinear-cone tail and full finite-clock axis positive; exact boundary `t=b*s`, `r=s(1−h²b*s)`, `Q=h³C`, `C=(9−h²r)D`; quotient valid through zero-speed seam. Open: global physical boundary/interior quotient sign, full source quadratic, fourth Schur gap/join/all rank. No actual-source counterexample. E: R:ThetaCuspRatioAffineConeObstruction; R:ThetaCuspRatioQuadraticSlopeBoundary; R:ThetaCuspRatioQuadraticBarrierStrict; R:ThetaCuspRatioNonlinearConeTail; R:ThetaCuspRatioAxisCompleteSlope; R:ThetaCuspRatioNonlinearBoundaryQuotient.
- LI cofinal small absolute literal-clock values — Kill/survivor [L, source-only review]: `S=liEvenCrossActualCurrentClockSeries` satisfies `liminf|S|=0` unconditionally; cofinal |S|<ε for every ε>0 cannot select RH. Under ¬RH, S exceeds every positive/negative threshold cofinally and has cofinal zeros. Full attained top-reciprocal packet and strict tail gap retained. No primitive-P floor or signed-history payment. E: R:LiEvenCrossActualClockSineOscillation.
- RW cofinal free-lag scalar trace certificate — Kill [L]: ∀large a ∀α>0, every valid G≥0, α−G≤S_a and pole-constrained Fourier-density bound R with GR integrable satisfies `α−∫GR≤−(π/96)e^a/a`; includes optimal-residual/finite-shell certificates. No negative supported Weil witness. Survivor [L]: exact source-form/symbol identity, attained minimal residual, four-band mass>1, exact Chebyshev moments/layer-cake bounds. Sharp layer a*e^(−a)*S_a(t/(4πa))→−4t*sin(t) locally uniformly and R_a/(2a)→1 uniformly ALL frequencies [L]. Open: all-aperture joint source floor. E: R:FreeLagTraceCertificateObstruction; R:FreeLagSymbolBoundaryLayer; P3:rw-free-lag-trace-boundary-layer.
- TH quadratic clock-current relaxation — Kill [L]: constant-shape enriched current with C=1+6Z is strictly negative for every Z>0. Survivor [L]: at Z=z²/18, retained rational clock correction −z⁴/[3(15+3z+z²)] gives strictly positive model current for every z>0. Not an actual-theta counterexample. Actual adverse clock energy and common fourth-source correlations must stay coupled; inner current/all-degree sign open. E: R:ThetaCuspC5ClockQuarticCancellation.
- RN global pointwise negative canonical current — Kill [L]: Ican=C_y−λC_t−λ_tC>0 at some t>0,0<x<y. Survivors [L]: I/J≤q/2+c″(0)/(6q); positive node-variation coefficient≥c″(0)/4; negative coupled boundary layer Ican(x,x,rx)→−γ/[2(1+r)²], γ=I/J−q/2>0; normalized finite-prefix limit=∫₀ᵀW₀L−γ/2, locally negative. Full weighted pair sign/general anchors/arbitrary rank open. E: R:ThetaFinitePairCurrentGerm; R:ThetaFinitePairBoundaryCurrent; R:ThetaFinitePairProfileFlux.
- RN favorable coarea score/covariance — Kill [L]: actual score not antitone; every positive node pair has an adverse two-mass kernel. Complete diagonal covariance C(x)/x⁴→−Var_μ(a)<0. Survivors [L]: strictly positive source-curvature quadrature for mass-score derivative; exact finite variance loss over dμ=2t k(t)²dt/H(0,0). Coupled potential-versus-covariance/weighted Schur sign open; not an arbitrary-rank counterexample. E: R:ThetaGaussianCoareaScore; R:ThetaGaussianCovarianceMeasure; R:ThetaGaussianCovarianceLimit.
- TG universal physical arithmetic selector — Kill [L]: prime/prime-power masks unbounded on original reciprocal-maximum ground grid. Survivor [L]: bounded binary selector iff mask eventually constant; contractive iff constant; every switch forces norm²≥n+2; actual finite-rank positive converse. Specific signed centered source energy remains open. E: R:SoninGroundGridArithmeticSelection.
- TG raw Gamma ground repaired by distant clocks — Kill [L]: literal symmetric Γ ground cutoffs diverge; mean-zero annulus probe annihilates every distant finite prime–polar source and forces ε‖joint‖²≥a/(32·72²), positive a,b and sufficiently small ε. Survivors [L]: exact local invariant, forced homogeneous reference, absolutely admitted remainder; full remainder response/physical maximal domain/fixed-test Hardy limits closed. Completed joint arithmetic cubic/sub-unit law open. E: R:SoninGammaClockEndpoint; R:SoninGammaDistantClockSeparation; R:SoninGammaRemainderResponse; R:SoninGammaClockNuclearLimit.
- TG fixed-carrier meromorphic current continuation — Kill [L]: for any b≥0,c<0 no SoninL²-valued meromorphic family on Re z>c agrees with complete damped current on Re z>½; no bounded-operator family has its ground column. Survivor [L]: two actual physical probes cancel expanding leg; finite polar endpoint correction is an entire vector, both dilation directions/all prime powers retained. Original logarithmic boundary admission/varying carrier/relative quotient open. E: R:SoninDampedPrimePolarCurrent; R:SoninDampedCurrentMeromorphicObstruction.
- SZ exact independent two-prime phase density — Kill [L]: physical phase law singular to independent uniform phases; normalized Weil ground law is not any independent-law density. Survivor [L]: log 2/log 3 phase map is Borel injective; measurable inverse recovers full spectral measure/every nonnegative cost, including shifted Γ. Finite-correlation approximation and joint supported sign open. E: R:CCMPhysicalTwoPrimePhaseLaw.
- SZ uniform ramp energy / eventual one-sign flux — Kill [L]: visible Γ energy exceeds every bound cofinally in every fixed cusp window while |signed action|>poleSharpConstant/8; incoming deficit/full action have both cofinal signs beyond fixed threshold. Survivors [L]: signed exterior current→0, exact cusp concentration and RH-conditional modulus-preserving full-divisor Bohr law. Bounded signed action/canonical-head positivity remain open. E: R:CCMExponentialRampCuspConcentration; R:CCMPrimeDeficitBohrFlux.
- SZ eventual pointwise symbol floor / frequency monotonicity — Kill [L]: full Γ–polar–prime symbol at frequency 0 has arbitrarily late positive-length windows above B and below −B for every B; literal cosh pole-profile supported energy has both signs of fixed-step increments beyond every frequency threshold when log 2<2a. Survivors [L]: complete signed-window law; fixed-source modulation recovers finite prime-phase quadratic differences with Γ increments/polar charges→0. No negative supported-energy or ground-sign conclusion. E: R:SuzukiCompletedCurrentSignedWindows; R:CCMRestrictedWeilModulationPhaseRecovery.
- SZ exterior constant-lift positivity — Kill [L]: literal packet parameters (8πa,4πa,2) force corrected symbol<0 outside every fixed window eventually, all degrees. Survivor [L]: packet ground average=0, packet→1 locally; complete corrected-symbol tail→tail(SD)−head(D), negative tail energy eventually>c for every c<1. Γ/polar/all visible prime powers retained. Arbitrary exterior repair/canonical-head sign not excluded. E: R:CCMExteriorPacketNegativeEnergyEscape.
- PM imaginary-damping interpolation — Kill [L]: ∃δ>0, ∀|y|<δ, literal A_(iy)∈L²(dt) iff y=0. Survivor [L]: exact complex source and cleared Mellin admission transport critical zeros vertically; unconditional Hardy zero/analytic isolation gives punctured gap without simplicity. Positive-real small-damping admission open. E: R:PMPowerDampedMobiusComplexBoundary.
- PM separately bounded prime-update currents — Kill [L]: Q_ε(8P²)/(8P²)^κ→∞ for 0<ε,0≤κ<½−2ε; sufficiently small positive ε, M⁻_ε(8P²)/(8P²)^κ→∞ for κ<1−2ε. Survivors [L]: positive first slab, negative square slab (all repeated primes retained), exact E=E_seed+Q−2(M⁺−M⁻); eventually M⁺≥(1−δ)M⁻ for every δ>0. No ratio limit/bounded remainder. Open: lower bound M⁺−M⁻−Q/2 and small-damping full energy. E: R:PMPowerDampedMobiusPrimeCurrent; R:PMPowerDampedMobiusPrimeSquareSign; R:PMPowerDampedMobiusNegativePrimeCurrent; R:PMPowerDampedMobiusPrimeEnergyBalance; R:PMPowerDampedMobiusPrimeCompensation.
- MC sub-square-root Mertens cancellation — Kill [L]: M(x)=Ω±(√x), so M=o(√x) impossible. Survivor [L]: either one-sided O(√x) bound forces RH and simple critical zeros; RH-equivalent O_ε(x^(1/2+ε)) producer remains open. E: R:MertensSquareRootOmega.
- Thin prime deletion/damping as a subhalf Möbius shortcut — Kill [L]: under nonnegative nonvanishing zeta-multiple partner and vanishing residue at 1, partial sums O(x^θ) force ζ zero-free Re s>θ, hence θ≥1/2. Survivor [L]: same half-power receiver for coprime deletion with Σ_deleted1/p<∞ and multiplicative thin-partner damping. Actual cancellation open. E: R:ZetaMultipleLandauZeroFree; R:CoprimeMobiusSumsZeroFree; R:DampedMobiusSumsZeroFree.
- Finite-channel STC gluing — nonzero three-prime triangle charge forbids a one-prime potential; ordered curvature has unbounded rank. Gap-sinc packets have negative index `⌊N/2⌋`, so any rank-`r` repair leaves `≥⌊N/2⌋−r` negative directions. Continued prime-square Gram has a negative diagonal; source work alone does not bound seam energy. Survivors: positive non-rank-one Γ–Stokes calibration, compact finite-rank Hilbert chamber, source-specific unbounded/singular landing (R:STCCofinalTriangleHolonomy; R:STCOrderedCurvatureRank; R:STCHyperbolicGapKreinSignature; R:STCPrimeSquarePositivityWall; R:STCSourceWorkSeamEnergy; R:STCGammaPrimeHilbertChamber).
- Holomorphic continuation of the literal theta source across a strip edge — charged rational cusps are dense on both `|Im x|=π/4` boundaries; no continuation. Survivor: rotated one-sided connection and Abel ray+arc boundary pairing reconstruct Xi inside the strip, without a zero-location sign (R:ThetaRationalCuspBoundary; R:ThetaCuspAbelBoundaryPairing).
- Faster-than-theta tail as a divisor-preserving correction — full Xi-divisor preservation with `|u(x)|≤Ce^(−a e^(b|x|))`, `a>0`, `b>2`, forces `u=0`; even sources vanishing at all simple critical zeros need `b>3`. Survivor [L]: exponent `2` is sharp: nonzero `k^(4m)` obey `b=2`, `a<π` and preserve the full divisor. E: R:ThetaTailDivisorCapacity; R:ThetaTailSimpleCriticalThreshold; R:ThetaTailCapacitySharpness.
- Imaginary-axis bounded quotient as theta rigidity — Gaussian-pair control has bounded imaginary-axis quotient but violates theta's sectorial `D(δ)∼δ²/4` ray bound; axis control alone is insufficient. Survivor [L]: exact relative-source sectorial Gamma bound; its source hypotheses remain essential. E: R:ThetaTailSectorialGammaBound; H:GaussianPairControlQuotient.
- Theta Bernstein/deletion/renewal signs alone — prime-deleted sources retain Xi's divisor but converge locally to a zero-free seed; one-sided Bernstein-positive two-anchor gauges admit off-line zeros. Positive renewal mass `<1/6`, exact analytic reflection, arbitrary finite seam jets and positivity after every finite prime deletion still admit source perturbations with off-line strip zeros. Symmetric prime-power/divisor gauges with both anchors force original source, not zero confinement. Survivor: literal square-lattice/Euler-sensitive phase law (R:ThetaPrimeDeletionBernsteinPureRay; R:ThetaPrimeDeletionSpectralEscape; R:ThetaOneSidedBernsteinGauge; R:ThetaReflectionPreservingZeroSurgery; R:ThetaPrimePowerBernsteinGauge; R:ThetaDivisorBernsteinGauge).
- Fixed-reserve half-anchor phase majorant — if an actual selected critical Xi node is omitted from finite residual reserve, the signed-derivative cofactor bound diverges as heat time grows; it cannot prove all-time `I≤J`. Full-gap-rate bound survives, but its ratio `≤1` is open (R:XiGaussianDerivativeHalfAnchorObstruction; R:XiGaussianFullGapNodalBudget).
- Finite data — fixed packet, aperture, moment list, jet order, determinant or Gram test admits off-line extensions. Positive strongly log-concave theta deformations preserve any finite moment depth and the complete real-zero divisor yet add off-real zeros; compact-tail implants preserve exact theta tails and finite moments yet add off-real zeros (real-divisor preservation not claimed for implants). Survivor: literal full source arithmetic/complete divisor plus an independent orientation law. E: R:ThetaDerivativePacketSpectralBoundary; R:ThetaCompactTailImplant; R:ThetaCompactStripZeroEngineering.
- FE, entireness, positive Λ, Gamma factor, integral multiplicativity with free Gamma factor — explicit off-line systems satisfy each (CANNOT-01, 64, 65, F119, CANNOT-190).
- One fixed functional of the source — every unconditional identity is pair-even in `δ`; fixed-kernel certificates resolve only down to `(1/2π)log(t/2π)` (CANNOT-182r).
- Deformation-robust inequalities — hypotheses surviving one Euler-factor deformation give nothing (MUST-389; KR-DEF, KR-APW).
- Reflection-even real readers — norms, energies, signatures, Gram determinants, indices, capacities agree on partners (CANNOT-399).
- Localized/equivariant invariants — compute only the fixed part (CANNOT-405/407; KR-GEN).
- Pointwise averages and displacement mass — degree one under scaling, blind to the unit-height bump (MUST-433, CANNOT-425).
- Continuous functionals of the zeros — the quantum jumps (CANNOT-422).
- Log-height free-orbit count ceilings — cannot force a nonnegative integer count to vanish; require a uniform bound below its first positive quantum. This does not exclude von Koch's ψ/π logarithmic bounds or arbitrary finite lag ceilings (CANNOT-437).
- Self-adjointness, unitarity, spectral realization, generic Krein self-adjointization — arbitrary real spectra realizable; repairs preserve nonreal divisors (CANNOT-08, CANNOT-96).
- Recurrence, periodicity, closed observation — recurrent quotients coexist with escaping histories (CANNOT-07).
- Cohomological exactness, Hodge/Cartan contraction, square-zero totalization — off-line curved sectors are contractible; algebraic exactness relocates the anomaly (CANNOT-11, CANNOT-162, CANNOT-435).
- Compact-open or semicontinuous descent — escaping bubbles and multiplicity collisions (CANNOT-18, CANNOT-47).
- `L²`/a.e. quotients — isolated shells invisible (CANNOT-29).
- Abstract universal-law formalisms detached from arithmetic — strictification, promotion, `L_∞`/MC, properness, recurrence, positivity capstones exist unconditionally (CANNOT-13, CANNOT-35, CANNOT-59, F79).
- Receivers as producers — a proved RH-equivalent premise read as progress (F01, CANNOT-24, CANNOT-192r).
- Manufactured costs — every selector is optimal for some manufactured positive cost (CANNOT-28, F69).
- Sub-quantum budgets on holomorphic source readers — anchored holomorphic passages conserve the integer at finite energy; holomorphic clocks realize quantized zero-side forms only as 0/∞ growth; a sub-unit margin is idle, any finite bound is RH (KR-R1, KR-R3, CANNOT-458).
- Self-similarity or dyadic transport of boundary data — acts on Mellin transforms by units; generic odd anti-periodic dyadic data realize every winding `−(2k+1)` (KR-R2, no-go-479).
- FE + integer spectrum + source-strip analyticity — weakly holomorphic `θ₃(1+t₁h+t₂h²)` deformations have off-line strip zeros [L] (KR-R2).
- Hecke-semigroup eigenstructure of boundary data — common eigenvectors of the `r↦n²r` transfer operators are all Helson series, which admit off-line zeros (KR-R2).
- Structural properties of a renewal waiting-time law — log-concavity does not confine the level `E_μ[Si(zT)]=π/2` (uniform law) (KR-R2).
- LI positive-kernel/monotone-ratio inverse — Kill [L]: actual resolvent and causal inverse negative at positive clocks; both resolvent signs cofinal, both undamped signed masses infinite. Every complete positive kernel tail has a negative inverse value. Positive coefficients, increasing forcing ratios, literal slope and arbitrary finite forcing/response jets admit negative-inverse comparison inputs; large perturbations leave the actual narrow ratio band. Survivor [L]: unique signed Volterra inverse, exact r₊/r₋/|r| damping threshold p>β, exact matched jets. Open: actual r⋆g≤g; no RH counterexample. E: R:LiClockThetaResolventSignedMass; R:LiClockThetaForcingRatioShape; R:LiClockThetaTailInverse; R:LiClockThetaTailCounterInput.
- LI absolute forcing-history domination — Kill [L]: ∀A ∀T, some t>T has g⋆K>A g and g⋆K′>A g′. Survivor [L]: positive literal massive forcing, exact origin ratios ν₁t²/12 and ν₁t²/4, signed inverse `−S=g−r⋆g`. Open: signed history comparison, not an absolute-envelope bound. E: R:LiClockThetaMassiveForcing; R:LiClockThetaForcingHistoryMajorant.
- LI fixed-history/constant primitive-mixture transfer — Kill [L]: every fixed alternating-history truncation has cofinally unbounded error; no countable nonnegative constant primitive mixture represents rT(r) on any (0,R]. Survivor [L]: absolute full history, clock-dependent parity brackets, positive repeated-primitive/matched-dilation floors and exact guarded cost decomposition. Open: adaptive lower-endpoint sign/source exclusion. E: R:LiEvenCrossActualClockCausalHistory; R:LiEvenCrossActualClockCausalHistoryFlattening; R:LiEvenCrossActualClockPositivePrimitives; R:LiEvenCrossActualClockFiniteGuardCosts.
- LI raw positivity/cumulant promotion — Kill [L]: positive reciprocal raw coefficients have cofinal ratio drops; κ₄(0)=−6M₁<0, κ₃<0 near positive origin, centered fourth Ward score negative. Survivor [L]: raw radius 1/z, ratios→z, exact logarithmic/Lah recurrence and strictly positive third Lah bracket for 0<z<300. Open: all-order logarithmic derivative signs on p>1/300; raw/low-order positivity insufficient. E: R:LiClockThetaReciprocalRawGerm; R:LiEvenCrossActualClockCumulantBoundary; R:LiEvenCrossActualClockThirdLahBracket; R:LiClockThetaTiltedWardHierarchy.
- LI mass-calibrated score-floor ⇒ Hankel sign — Kill [L, model]: positive strongly log-concave Gaussian–Hermite density has literal raw mass, log-curvature≥30 and polynomial score-floor surplus 111104/110843, but size-three Hankel determinant negative for every sufficiently small τ>0. Survivor [L]: exact determinant `6^(−18)τ²(−196+324τ+16τ²)` and full source-floor calibration. Actual theta/Euler membership absent; no actual-source/RH counterexample. E: R:PrimeArchGaussianHermiteDensity; R:PrimeArchThetaGaussianHermiteCountermodel; P3:route li/li-mass-calibrated-score-floor-obstruction.
- MC periodized uniform-cycle norm budget — Kill [L]: literal periodized observer uniform-cycle squared norm→∞. Survivor [L]: exact signed cycle/smooth–rough/largest-prime reduction; composite innovations vanish, total prime innovation norm<√2, prime-only transition subpower iff RH for 0<δ<1. Open: signed covariance/head subpower law, not an observer-norm ceiling. E: R:CausalMobiusThetaUniformCycle; R:CausalMobiusThetaPrimorialInnovation; R:CausalMobiusThetaLargestPrime.
- RN positive/bounded reflected moving-cusp carrier — Kill [L]: R∞ has both negative-cusp signs and no negative-tail L² admission; 0<c<2 finite-stage weighted energies finite but P‖k_S‖²_(H_{c/P²})→∞ along every prime exhaustion. Survivor [L]: all-fixed-derivative local limit, exact signed-totient reconstruction, one-unit divisor shear and sharp positive-tail threshold c<2. Open: signed arithmetic orientation, not bounded cofinal energy or global nonnegativity. E: R:ThetaMovingCuspDualSource; R:ThetaMovingCuspTotientReconstruction; R:ThetaMovingCuspSpectralShear; R:ThetaMovingCuspWeightedEscape.
- BSY uncorrected finite Dirichlet-polynomial near-one producer — Kill [L]: real finite Gram ratio≥49/48 with Σa_n/n≠0; no ratios→1. Survivor [L]: corrected entire bounded-half-plane mollifiers `M=−sP/(s−1)`, P(1)=0, give RH iff weighted mean-square ratios→1. Open: independent corrected-mollifier producer. E: R:BalazardSaiasYorMollifierClass.
- Channelwise compact/Calkin-small formation repair — Kill [L]: compact channel defects can assemble an infinite kernel/noncompact global defect or fail Bessel boundedness. Even invertible rank-one perturbations with γ_n=1/(n+1) assemble nonclosed range/no bounded decoder. Copies `V_n K U_n*` of ANY nonzero compact K assemble with norm=essential norm=||K||, noncompact. Survivor [L]: global strong resolution/weak Gram residual `C*C=cI+G`, c>0, ||G||<c gives frame/decoder. Compact packet A repairs carrier C iff C closed range, finite kernel, A separates kernel; exact unitary covariance. Uniformly bounded block assembly upper semi-Fredholm iff infγ>0 and total kernel dimension finite; injective block pseudoinverses assemble iff positive γ floor. Orthogonal P,Q with PQ compact admit projection Ψ modulo compact P+Q. Actual bilateral Sonin compressed shells are locally identity+compact/Fredholm and obey the same exact global γ/kernel gate. Open: native γ floor/kernel budget and arithmetic global frame, not channelwise compactness. E: H:FormationQuotientCountermodels; H:GlobalGramResidualCoverage; H:ConstitutiveCompactCofinalFusion; H:BlockFormationSemiFredholm; H:LocalFredholmCofinalFailures; H:ProjectionSumCalkinLift; H:SoninShellBlockGate.
- Positive two-sided additive dust with nonzero calibration — Kill [L]: γ:R→V additive, sign-symmetric admitted U, γ(U) in pointed positive cone ⇒ γ|U=0; faithful additive calibration ℓ(γu)=c*u, c≠0, forces admitted u=0. FE automorphism only transports vanished legs; no arithmetic admission proved. Survivors [L]: one-sided positive linear dust nonzero; signed linear dust loses positivity; constant positive family nonadditive/nonzero. Missing guards essential; exact dust/cumulant separation and guarded Mellin reconstruction retained. E: H:PositiveTwoSidedDustSelection; H:FormationCumulants; H:MellinAnchorReconstruction.
- TT polynomial-only seventh Y^4 head — Kill [P]: unique polynomial recurrence core P has `P(5,U)=−32768(9−U²)^3`, violating literal zero seed for U²<9. Survivor [P]: full `H4(n,U)=P(n,U)+32768(9−U²)^3*4^(n−5)`, n≥5; native scaling 12^m*H4(m+6,U). Complete sixth/seventh heads, lower seed modes, reflections and M11/M12/S12/S13 give explicit p12/p13. Mode's M11 shape H satisfies `344H=(172Y−963)²+298647>0`. Positive native geometric amplitude does NOT imply positive signed Q6 contribution: retained reflection/source derivative produces increasing `R(Y)=344Y³−3990Y²+20223Y−64152`, Y=3k+1; R(7)=−109,R(8)=18400, for V=U²∈(0,9), mode negative on 5/4<k≤2, positive for k≥7/3. Complement sign unclaimed. Actual q7 positivity/mass increment [P] reduces full Q6 to flat mass. Terminal/actual Q6 negative sixth-coefficient asymptotic source-closed [L]; seventh-mode decomposition above remains [P]. No new route retirement. Open: full absorbed-surplus VALUE certificate, residual/source quadratic/fourth gap/all rank, exact seventh-mode formalization. No extra positive-source premise or actual-theta/RH counterexample. E: P1:tt-surplus-top-coefficient; P1:tt-third-slope-nonlinear-cone; P1:tt-surplus-even-coefficient-orientation; R:ThetaCuspRatioTerminalActualCoefficient; P5:tt-ordinary-absorbed-surplus-coefficients.
- TT ordinary absorbed-surplus coefficients — Kill [L]: complete actual Q6/(3k+1)^10→−(8192/3)*189994*12^18; eventually EVERY complex mass M leaves a negative sixth coefficient in Q−Q8E8+Q8ME7, so no all-nonnegative real ordinary-coefficient representation. Survivor [L]: same absorbed PRINCIPAL value strictly positive on0<e≤1/36 via exact mixed e/(1−36e) decomposition; full graded transport h^22*Absorb(Q,M)(e/h²) retained. Open: full interior absorbed VALUE, source quadratic/fourth gap/all rank. Not an actual-source value/RH counterexample. E: R:ThetaCuspRatioTerminalActualCoefficient; R:ThetaCuspRatioTerminalAbsorbedPrincipal; R:ThetaCuspRatioTerminalAbsorbedTransport; P5:tt-ordinary-absorbed-surplus-coefficients.
- TT global kinetic concavity — Kill [L]: EACH1/14≤h≤4/5 admits an entire small-positive-s family strictly inside the nonlinear cone with positive full second derivative; source not concave on[0,Z0]. Survivor [L]: exact complete curvature law plus positive clock-zero principal9C(1−9z²),C>0; direct source controls and boundary-to-interior value comparison remain viable. Open: actual-source interior sign, full quadratic/fourth gap/join/all rank. No actual-trajectory/RH counterexample. E: R:ThetaCuspRatioKineticAxisCurvature; R:ThetaCuspRatioKineticInteriorCurvature; R:ThetaCuspRatioKineticClockPrincipal; P5:tt-global-kinetic-concavity.
- TT fixed-endpoint coarse source-control box — Kill [L]: EACH1/10≤h≤1/8,r=361/25 has V>0, control18(h,V,1/3)<0 and P(h,V,1/3)<0; no global nonnegative controls/value on this box. Survivors [L]: control18=19P−ZP′; P(0)>0, both endpoint derivatives<0, auxiliary polynomial root in(0,1/3); exact actual source projects BELOW its nonlinear-boundary endpoint Z0<1/3. Open: controls1–4 of negative first derivative or actual-endpoint full VALUE. Auxiliary root not a zeta zero; no actual-trajectory/RH counterexample. E: R:ThetaCuspRatioKineticControl18Obstruction; R:ThetaCuspRatioKineticControl18Endpoint; R:ThetaCuspRatioKineticFixedEndpointValueObstruction; R:ThetaCuspRatioKineticActualBoundary; P5:tt-fixed-endpoint-source-controls.
- TT convex kinetic first derivative — Kill [L]: h=4/5,0≤r≤361/25,V>0 gives P'''(0)<0, so P′ nonconvex on EVERY[0,Z],Z>0. Survivor [L]: positive drift-independent clock-zero normalized core, small-clock initial third-derivative positivity for each fixed r, intrinsic normalized clock root in(0,4/5). Open: direct negative first derivative/full physical source VALUE, compact quadratic/fourth gap/all rank. E: R:ThetaCuspRatioKineticSlopeConvexityObstruction; R:ThetaCuspRatioKineticThirdInitialClockTransition; P5:tt-kinetic-slope-convexity.
- Positive-unital promotion of the closed Plücker observer — Kill [L]: positive unit-trace closed observer T has ||T||<1; every positive unital operator-system map has ||Φ(T)||≤||T||, hence cannot reach ANY norm-one target. Survivor [L]: exact purity defect Σw_nw_kΔ_nk, canonical full physical covariance purification, coherent marked shift index−1/self-commutator trace1 and marked exit defect closing to T. Open: different faithful arithmetic Xi/index handoff; constructed subunit wall alone does not supply it. E: R:PluckerCovarianceSquareRootPurification; R:PluckerCovarianceObserverSubunitDefect.
- Unframed covector-to-vector residual promoter — Kill [L]: dimℝV≥2, τ equivariant under ALL GL(V) changes of frame ⇒ τ(α)=0 for EVERY nonzero covector α. Survivor [L]: positive-Hessian Legendre source chart promotes residual through H^−1 with exact reporter e^(−t) contraction, positive power and Bregman work law; metric/source chart and marked target are necessary data. Open: native arithmetic chart/coupling, not coordinate-free promotion. E: H:UnframedPromoterNoGo; H:LegendreResidualTransduction; P5:universal-law-field/formation-blowup-geometry/unframed-projective-kink-selection.
- RW raw EVEN polar-ground strip passage — Kill [L]: even entire order-one, cross-rooted F_n with F_n(i/2)=0 cannot have normalized local-uniform limit XiC on |Im z|<½. Forced pair causes singular negative imaginary log-derivative drop on zero-free compact imaginary segments; XiC has bounded nonzero imaginary-axis response. Survivor [L]: exact Hadamard drop law, polar-QUOTIENT strip-convergence receiver, unconditional real-rooted FULL-form grounds and RH iff nonnegative full form on all real-rooted tests. Generic raw cross-rooted implication remains true; no broader non-even no-go claimed. Open: corrected quotient/full-ground source convergence or source floor. E: R:CrossRootedPolarZeroXiStripObstruction; R:CCMRestrictedWeilFullFormRealRootedGround.
- Aperture-cone integer as scale-contrast selector — Kill [L]: positive compact injective T,infinite-dimensional H; EVERY scale exponential winds1, EVERY difference exponential null-homotopic. Any integer reader of its K1 class is blind to c=d versus c≠d. Survivor [L]: exact cone/ideal C* models and winding classification; norm contrast<1 and zero iff c=d; logarithmic scale acts by actual translation on C_0(ℝ). Open: arithmetic source coupling/contrast law beyond this class, not a scale-selective K1 integer. E: H:ApertureConeCalculus; H:ApertureOpenHistoryIdeal; H:ApertureConeWinding; H:ApertureLogTranslation; P1:spectral-aperture-cone-lean-programme.
- RW unconditional even-ground selection — Kill [L, CONDITIONAL]: finite off-line Xi copies with isolated top quartet t+iδ,t,δ>0 force cofinally large apertures where EVERY restricted ground is odd. Survivor [L]: exact even floor/odd smooth-test phase gap; eventual non-odd selection excludes this model. Infinite/clustering divisor, ground simplicity, corrected quotient convergence and Weil floor open. E: R:CCMParitySelectionNoGo; R:CCMParityQuartetEvenFloor; R:CCMParityQuartetOddTest; P3:11-rh-zero-divisor-geometry/ccm-parity-selection-fails-off-line-quartet.
- HF ordinary cyclic normal-regulator landing — Kill [L]: actual positive Steinberg normal K1 cycle is an explicit HC1 boundary; ordinary cyclic reader cannot retain m*log(3/2). Survivor [L]: I_St=I_+² STRICTLY below full augmentation square, negative sign sector retained; original cycle survives HH1 with nonzero augmentation–Kummer detector. Relative/negative cyclic realizations and analytic Xi compatibility open. E: R:DeningerPositiveSteinbergSquare; R:SquareZeroUnitCyclicBoundary; R:DeningerPositiveSteinbergCyclicComparison; P3:positive-steinberg-hochschild-cyclic-comparison.
- HF rapidly admitted integer-blind dual witness — Kill [L]: measurability + ∫|w|exp((π/2)|t|−K√|t|)<∞ + zero moments on a set with positive logarithmic reciprocal density ⇒ Fourier transform0; all integers included. Survivor [L]: exact Carlson density/admission boundary, prime-only polynomial-room theorem; nonzero null-potential annihilator has unbounded block mass in BOTH signs. Prime-only square-root-room and more singular dual classes not excluded. E: R:PrimeBlindCarlsonThreshold; R:WeilNullPotentialSignPartRigidity; P3:11-rh-zero-divisor-geometry/prime-blind-carlson-threshold.
- C2-P rational reflected-cosine repair — Kill [L]: for T(w)=cos(2π√((w+1/12)/27)), Φ(w)=(T(w),T(−w)), no nonconstant rational R has three distinct integer-contained fibres and reciprocal reflection R(Φ(−w))R(Φ(w))=1 where denominators are nonzero. Product repair has infinitely many genuine nonreal points in both nontrivial cube-root fibres. Survivor [L]: every irreducible non-coordinate algebraic curve has infinitely many off-integer Φ-preimages after finite exclusions; three integral fibres force R∈ℂ(X) or ℂ(Y); Φ Zariski dense. Arbitrary C2-P/Xi remains open. E: H:CosineProductNonrealFibers; H:CosineAlgebraicComponents; H:CosineRationalRepair; P3:leftovers/cosine-algebraic-fiber-rigidity.
- HF raw reciprocal bounded below pole — Kill [L]: literal reciprocal G of ANY full-positive λ unbounded on EVERY half-plane Re s>x,½<x<1. Survivor [L]: same G holomorphic,ordinary reciprocal series converges Re s>½,G(1)=0; all-twist reciprocal sums Oε(N^(½+ε)(2+|t|)^ε),square mass Oε(N^(1+ε)). ζ cancels source zero; bounded ζG remains open, not excluded by raw-G obstruction. E: R:WeilWorkSingularArithmeticReciprocalObstruction; R:WeilWorkSingularArithmeticSharpReciprocal; R:WeilWorkSingularArithmeticSquareMass; P1:weil-work-03-singular-arithmetic.
- HF separation-free narrow-packet coercivity — Kill [P]: arbitrary overlapping width-w polar bumps approximate a fixed broad nonzero source in H¹; mass→positive constant,actual archimedean energy→finite limit. Thus no common(log(1/w)−C)*mass lower bound. Survivor [L]: EVERY compact complex C² F has E_arch≥(b−C+¼)M−e^(4b)P/4 and optimized E_arch≥(¼log(M/P)−C)M,where M=∫|F̂|²,P=∫|F̂|²/(τ²+¼)². For F=G″−G/4,P=∫|Ĝ|²; disjoint packet inverse-mass law recovers logarithmic coercivity. Full matched-cone primitive payment/open source sign retained. E: R:WeilWorkExposingRayPacketCoercivity; R:WeilWorkExposingRayPrimitiveSharpness; docs/reports/weil-work/results/02-exposing-ray/OVERLAP-PROOF.md; P1:weil-work-02-exposing-ray.
- HF nontrivial boundary-regular ζ-multiplicative carrier — Kill [L]: λ=βΛ+1*m+v,Σ|m|/√n<∞,Σ|v|/√n<∞,v(0)=v(1)=0; full positivity forces β=1,M(1)=0,λ=Λ. Survivor [L]: exact pole-share balance and full multiplicative resonator; m,v need not vanish separately. General singular/non-summable carrier and positive producer open. E: R:WeilConeZetaCarrierBoundary; R:WeilConeZetaCarrierResonance.
- HF subcritical Gamma domination — Kill [L]: a*Gamma+b*Pole+C*L² with 0≤a<b is negative on some positive smooth integer-null mixture for EVERY C; mass-one null energy unbounded below. Survivor [L]: exact necessary coefficient boundary b≤a; actual modified positivity supplies signed-coefficient convergence, pole residue b and sharp leading Gamma budget a. Critical a=b=1 PBAP remains open. E: R:WeilWorkPBAPCriticalBoundary; R:WeilWorkPBAPCriticalCoefficients; R:WeilWorkPBAPCriticalResidue; P5:weil-pbap-subcritical-gamma-domination.
- HF unit-mass joint phase correction — Kill [L]: prime p≥5,all shifted phases logn−½logp,2≤n<p,require mass M>1; log-frequency cost diverges as M↓1. For ANY fixed smooth profile of width<log2 with TWO distinct real-active nodes,actual real-null full energy AND mass-normalized energy→+∞; no inactive-node equations assumed. Survivor [L]: exact positive smooth integer-null correction for EVERY M>1 above ANY frequency threshold; mass exactly2*baseMass*(1+M),both poles retained in energy bound. General/varying-profile critical PBAP open. E: R:WeilWorkPBAPJointPhase; R:WeilWorkPBAPJointNull; R:WeilWorkPBAPJointActive; R:WeilWorkPBAPJointEnergy; R:WeilWorkPBAPJointEnergyEscape; P1:weil-work-01-pbap.
- RW/HF tiny integer traces as cheap atomwise repair — Kill [L]: actual far-polar tests have E_arch≤−δ and sup_n|atomCoeff(n)|→0, yet weighted independent-atom budget Θ(Xe^X). Survivor [L]: exact coherent finite repairs cancel ALL integer traces at aperture X+17/50 with O(1) repair energy; divergent box budget is not a lower bound for arbitrary repairs. Universal matched-family lower bound open. E: R:WeilWorkExposingRayPolarLeakage; R:WeilWorkExposingRayCoherentCompletion.
- HF vanishing local-seed variance completion — Kill [L]: translated nonnegative mixtures of polar seeds supported in [−½log2,½log2], completed by their exact variance repairs, pay ≥π/(5log2)*|F̂(t)|² at EVERY real t. Literal Riemann source L≥2 and full finite exposing mixture retain a fixed positive cost; geometric Fejer floor survives step→0 at fixed positive total shift. Survivor [L]: exact signed-kernel variance identity, C² source admission and capacity law. Arbitrary non-variance repairs open. E: R:WeilWorkExposingRayCoherentGap; R:WeilWorkExposingRayCoherentCompletion; R:WeilWorkExposingRayLocalCapacity.
- HF spaced common-profile polar lattice null mixture — Kill [L]: Fejer-profile lattice spacing X≥4,one actual half-pole zero per test; every nonzero positive mixture has a strictly negative rounded integer sample. Survivor [L]: exact coefficient-mass/pole-defect identity; mass≤4Σ_d cosh(dX/2)*|sampled trace_d|. Arbitrary overlap/profiles/repairs outside class. E: R:WeilWorkExposingRayLatticeMass.
- HF strict saving from logarithmic Toeplitz ceilings alone — Kill [L]: unconditional nonnegative prime-supported system satisfies EVERY complex-vector ceiling with budget logN but normalized prime square mass approaches constant1 cofinally. Survivor [L]: global square mass≤log²N; two-prime square attains star budget√(a²+b²) iff composite entry=−2ab/√(a²+b²). These are relaxation models, not full Weil-positive systems; source-specific stronger saving/ζG detector open. E: R:WeilWorkSingularArithmeticToeplitzSharpness; R:WeilWorkSingularArithmeticDivisorCompletion.
- HF translated-radical arithmetic null repair — Kill [L]: nonnegative mixtures of arbitrary translates/truncations of Φ_L,L≥log2+1, have logValue(2)≥δ*spectral density; normalized arithmetic cost cannot vanish. Coherent finite mixtures on j*logb,b≥2, cancel ALL positive b-powers iff every coefficient=0. Survivor [L]: uniform density/atom coercivity and exact outer-autocorrelation invariant. Arbitrary short real shifts have dense complex Xi span and exponential weighted tails; all derivative orders have a common factorial repair budget and exact mixed divisor–Bessel correlations. Strong-norm shifted-Xi approximation is separately expensive; finite positive moment cancellation with paid cost remains open. E: R:WeilWorkDeficitRadicalTranslateObstruction; R:WeilWorkDeficitGeometricRadicalObstruction; R:WeilWorkDeficitRestrictedXiDensity; R:WeilWorkDeficitRadicalBudget; R:WeilWorkDeficitUniformDerivativeBudget; R:WeilWorkDeficitBesselCorrelation; P5:weil-work-06-restricted-radical-cancellation.
- HF fixed-interior phase settlement — Kill [L]: actual regularized phase has dyadic integral norm≤18Y/(η²logY),eventually Y,0<η≤1; fixed-width normalized mean→0. Survivor [L]: η=Y⁻⁸ recovers full canonical phase within C/Y in L¹; at fixed ordinate, every polynomial-length reciprocal-prefix remainder retains exact boundary atom order. No moving-height uniformity or phase-only truncation no-go. Boundary concentration remains open. E: R:WeilWorkSettledPhaseInteriorCancellation; R:WeilWorkSettledPhaseRegularization; R:WeilWorkSettledPhaseReciprocalTailOrder.
- HF positive matched-ray mass margin — Kill [L]: EVERY fixed ε>0 and tail slack c fail on actual exact nonnegative matched polar C² families at aperture≤½logN+C: E−ε*physicalMass<threshold−c*tail(N),eventually N. Survivor [L]: matched mass≥m₀*t; mass-normalized excess has exponentially small upper bound at every rate r<2πe⁻². No lower sign proved; vanishing negative mass-error producer remains open. E: R:WeilWorkExposingRayMassMargin.
- RW/HF independently tuned primitive surrogate — Kill [L]: on SAME exact matched families,Σα_i*((b_i−C)M_i−e^(4b_i)P_i/4)<threshold−c*tail(N) for EVERY independent row tuning b_i. Survivor [L]: E≥surrogate+M/4; optimized logarithmic mass-ratio bound survives. No no-go for sharpened estimate or arbitrary matched-cone method. E: R:WeilWorkExposingRayPrimitiveSharpness.
- HF subexponential-budget width<2 differential matching — Kill [L]: fixed finite derivative list,ANY complex synthesis/signed mixture,independent row centers and width<2 has atom/exposingWeight bounded by C*coefficientBudget*e^(−δn); matching forces exponential budget. Survivor [L]: actual odd width2 filter matches opposite tail with exponentially vanishing relative error; exact compact complementary energy identity retains shorter residual. Derivative-order growth,finite-head repair and full energy sign remain open. E: R:WeilWorkExposingRayDifferentialWidth; R:WeilWorkExposingRayCriticalOddSource; R:WeilWorkExposingRayCriticalOddTail.
- HF finite-observation spectral determination — Kill [L]: EVERY finite real observer,including full energy+complex correlations or bounded expectations,leaves closed topological cubes of EVERY finite dimension among actual normalized complex-null REAL-test symmetric representing laws. Survivor [L]: full rational covariance family determines law; budgeted compact completions have continuous inverse and finite approximate control of continuous observables. No finite exact determination or PBAP sign failure. E: R:WeilPaperTopologicalObservationCubes; R:WeilPaperPhaseCovarianceRecovery; R:WeilPaperFiniteCovarianceControl.
- HF cheap strong-norm shifted-Xi approximation — Kill [L]: packet of physical shifts in[−a,a],variationV,at ANY real Xi zero γ has L² error ε>0 approximating modulated Φ,with V+1≥exp(exp(|Xi(0)|²/(8ε²)−a)−K),universal K>1. Survivor [L]: if V≤e^N then |Xi(0)|²≤8(a+log(N+K))*ε²; zero mismatch and full theta-tail cutoff estimate exact. Finite-moment positive cancellation outside this strong-norm obstruction remains open. E: R:WeilWorkDeficitXiApproximationCost.
- HF nontrivial weighted periodic residual phase — Kill [L, full-positive λ]: exact bilateral harmonics2klogr,ANY real r>1,Σabs(p_k)r^abs(k)<∞ force λ=Λ,RH; signed rational and irrational bases included. Survivor [L]: period-one actual residue law,absolute inverse-dilation convolution,irrational radical elimination and rational subgroup reduction. Weighted multifrequency rigidity and source representation production open; no periodicity premise inferred. E: R:WeilWorkQuantizationPeriodicResidues; R:WeilWorkQuantizationFrequencyMass; R:WeilWorkQuantizationRadicalMass; R:WeilWorkQuantizationRealPeriodicRigidity.
- HF nontrivial cubic finite-deficit datum — Kill [L]: original complete degree3 correspondence with FINITELY many points ordE<ordξ forces λ=Λ,RH; no extra spatial/boundary premise. Survivor [L]: every nontrivial datum has infinitely many negative integer residues of E′/E−ξ′/ξ,negative part exactly(ordξ−ordE)₊; all multiplicities retained. Infinite-deficit density/rigidity open; endpoint c(1−1/x) remains outside interior finite-packet class. E: R:WeilWorkHigherDenominatorFiniteDeficit; R:WeilWorkHigherDenominatorLogResidue.
- HF frozen-pole modulus shortcut for GY — Kill [L, local model ONLY]: ∫exp(2πitx)/(δ−2πit)²dt=0 for δ>0,x≥0,not a positive Lorentzian Fourier size. Survivor [L]: for finite A(t)=Σb_j exp(−2πitv_j),exact integral=Σ_(v_j>x)b_j(v_j−x)exp(−δ(v_j−x)); complex signs retained. Full GY window bound/zero-driven obstruction both remain unproved; no GY route retirement. E: R:WeilWorkPBAPMollifierCausality; docs/reports/weil-work/results/01-pbap/GY-CAUSALITY-AUDIT.md.
- HF one-node cosine certificate beyond logarithmic boundary — Kill [L]: literal unit-bump family K=L/2+s−d logL,W=κK e^(−L/2),actual prime half-log/nearest-integer lag,s=log(1/abs(lag)); d<1 defeats EVERY real cosine coefficient. Negative seed/opposite-phase pair need not be all-integer-null. Survivor [L]: d>1 nonempty null sector for EVERY correction mass M>1,full E≥((d−1)logL/4)*physicalMass. d=1,many-node certificates and unrestricted PBAP open. E: R:WeilWorkPBAPJointBoundaryObstruction; R:WeilWorkPBAPJointBoundaryPrime; R:WeilWorkPBAPJointBoundaryNull.
- RW/HF bare finite Gamma-mode certificate — Kill [L]: exact near-threshold matched polar families defeat ALL row-dependent truncations K_i≤exp(rN),0<r<κ/2,κ=2πe⁻²; truncated energy<threshold−tail(N). Survivor [L]: omitted energy≥moment/(32K²),matched moment≥c*t; exact positive remainder retained. Not a real-frequency/Galerkin-cutoff no-go; remainder-corrected bounds and full matched-cone floor remain open. E: R:WeilWorkExposingRayGammaTruncation.
- HF weakly continuous full-energy transfer — Kill [L]: intrinsic native energy nowhere weakly continuous,even on real-test symmetric laws; no continuous extension to compact origin-representing probabilities. Exact nonnegative energy losses/divergence occur at EVERY native limit; energy graph nonclosed. Survivor [L]: full law determines energy; realification preserves it; attained fibres contractible. Explicit pole-compensated budgets give compact completion,lower-semicontinuous Gamma energy and exact finite covariance lower certificates; at positive tolerance dual attainment and complementary slackness [L]. No PBAP sign refutation or failure of budgeted one-sided transfer. E: R:WeilPaperNativeEnergyTopology; R:WeilPaperSymmetricEnergyLimits; R:WeilPaperEnergyFiberContractions; R:WeilPaperSpectralCompactness; R:WeilPaperAffineCovarianceCertificates; R:WeilPaperCovarianceDualAttainment; R:WeilPaperCovarianceComplementarity.
- HF unweighted mean-square resonance passage — Kill [L, full-positive λ]: finite almost-periodic polynomials have mean square→0 yet normalized height-one resonance response1. Survivor [L]: actual resonance row=a_n/√n,finite squared norm~KlogN,K>0; exact Gaussian coefficient recovery/finite Bessel lower bounds. Weighted/control-norm passage and actual source-phase approximation remain open. E: R:WeilWorkQuantizationResonanceEnergy; R:WeilWorkQuantizationResonanceMean; R:WeilWorkQuantizationGaussianBessel.
- HF canonical coprime endpoints imply zero variance — Kill [L, local polynomial MODELS]: literal periodic coefficient sequences have canonical ratios for EVERY modulus yet positive variance for nonconstant normalized local polynomial. Not a full-positive counterexample. Survivor [L]: exact finite-period/geometric-valuation variance; zero variance IFF constant polynomial. Actual full-source prime-deletion square deviations share one finite variance budget; endpoint independence/vanishing variance open. E: R:WeilWorkSettledPhaseLocalPolynomialPeriods; R:WeilWorkSettledPhaseLocalPolynomialInvisibility; R:WeilWorkSettledPhasePrimeDeletionSummability.
- HF first product-kernel comparison — Kill [L]: actual order1 derivative energy<productKernel(1,1),opposite to proposed uniform comparison. Survivor [L]: order0 integer correlations strictly positive,order1 strictly negative for EVERY integer n≥2; complete prime budget reduces to weighted absolute product-kernel mass. Simultaneous positive-mixture cancellation and deficit bound open. E: R:WeilWorkDeficitLowOrderSigns; R:WeilWorkDeficitPrimeKernelBudget.
- HF positive Mellin tail-annihilator preserving ordinary source — Kill [L]: symmetric compact probability filter≠δ₀ has bilateral Laplace multiplier→∞ on positive axis; cannot preserve an absolutely convergent ordinary Dirichlet series with nonzero first coefficient,even eventually. Survivor [L]: source-preserving filters classified EXACTLY by δ₀; positive moment gives linear multiplier lower bound. Signed/noncompact filters outside class; cubic infinite-deficit converse open. E: R:WeilWorkHigherDenominatorPositiveFilter.

- FU/MC fixed smoothing for growing prime packets — Kill [L]: literal k-prime packet becomes positive exactly at causal integration order r≥k−1; no fixed r works for all k. At threshold normalized mass1 escapes every fixed logarithmic window. Survivor [L]: sharp threshold, positive convolution, exact mass/tail laws. Moving/rescaled signed source outside this obstruction. E: R:MobiusRieszPrimePacketThreshold; R:MobiusRieszPrimePacketEscape.
- MC coefficient-independent square-kernel bound — Kill [L]: bare positive-entry kernel has negative 2×2 minor for N≥3; counterterm-renormalized (2,N) plane (N≥2) PSD iff N≤3; diagonal grows≥cN³, excluding universal coefficient O(N²). Survivor [L]: literal signed Möbius terminal row nonpositive and O(N logN); square-sample/short-bilinear RH receiver. Actual joint arithmetic bound open. E: R:MobiusSquareRenormalizedKernel; R:MobiusSquareBilinearTerminalRow; R:MobiusSquareResidueShortBilinear.
- FU/MC coarse Selberg inputs — Kill [L, abstract models]: positive-power models satisfy coarse Selberg/sublinear first-response bounds but violate critical square-sample O(N²). Survivor [L]: exact model threshold σ≤½ for square-sample O(N²). Not an arithmetic counterexample; complete signed source remains open. E: R:PMSelbergSquareSampleBoundary.
- HF countable log-panel positivity as full Weil positivity — Kill [L]: one finite deficit at2, summable deficit, every log panel positive, yet full Weil positivity fails; arbitrary tail-panel heights compatible with a preserved prefix. Survivor [L]: sharp preserved-prefix boundary; finite-block deficit forces visible excess≥max(δ/100−η/(4R₀),0). Full-test sign remains necessary. E: R:WeilLogShiftFiniteDeficitSeparation; R:WeilTailPanelSharpPrefix; R:WeilFiniteBlockExcessMass.
- HF totalized potential without convergence — Kill [L]: zero-excess minorant has partial potentials→−∞ while totalized tsum=0 satisfies formal inequalities. Survivor [L]: exact finite/local-excess convergence criteria; whole-line domain iff normalized deviation subexponential. Pure exponential weight e^(ρn) admitted exactly for ρ<2πe^(−abs(y)); equality diverges. E: R:WeilLogShiftConvergenceNoGo; R:WeilLogShiftSubexponentialDomain; R:WeilLogShiftCriticalEndpoint.
- HF bounded recovery histories as moment control — Kill [L]: bounded fine-mesh histories can have divergent signed, excess and deficit log2-moments. At any positive coordinatewise precision with any fixed exact prefix, dense residual bounded histories have unbounded moments and signed nonsummability at every real shift. Survivor [L]: coefficient/history homeomorphism and exact recovery; regular finite-dimensional histories admit common normalized C₀ receiver. No growth bound for arbitrary histories. E: R:WeilLogShiftBoundedRecoveryNoGo; R:WeilLogShiftRecoveryHomeomorphism; R:WeilLogShiftArbitraryPrecisionGenericity; R:WeilLogShiftC0RecoveryReceiver.
- HF polynomial-cost full-cutoff Gram certificates — Kill [L]: for support range n and fixed B₀>0, every normalized actual-test certificate eventually costs more than A·n^p for every fixed A,p. Survivor [L]: each nonempty d-support has an exact d+1-test certificate; erasing any test gives a basis and positive balance. Finite feasibility does not supply full-source sign or cutoff-uniform cost. E: R:WeilLogShiftSuperpolynomialGramCost; R:WeilLogShiftGramMinimalCardinality; R:WeilLogShiftGramSimplexBasis.
- LA/MSC Laguerre–Pólya inverse differential filters — Kill [L]: Xi has no LP preimage under any nonconstant real-rooted real polynomial differential symbol; every nonzero real-shift average has imaginary zeros. Survivor [L]: exact LP transfer and interlacing; direct theta-source sign and nondiagonal divisor-faithful transport remain outside this no-go. E: R:XiFirstOrderLaguerrePolyaMaximality; R:XiRealRootedPolynomialPreimage; R:XiDerivativeLaguerrePolyaPreimage; R:XiRealShiftAverageImaginaryZeros.
- HF/CTF regular exact-null certificates — Kill [L]: tests Ξ^kR, k≥1, with the stated holomorphic strip admission/decay, critical Γ-weighted logarithmic room and integer blindness have zero integral; no nonzero positive certificate in this class. Survivor [L]: exact order transfer; integer-blind Carlson threshold K≤π/2 forces vanishing, K>π/2 admits nonzero separators. More singular classes outside theorem. E: R:ExactNullCertificateOrderTransfer; R:IntegerBlindLogarithmicCarlsonCritical; R:IntegerBlindLogarithmicCarlsonSharpness.
- DR finite-quotient monodromy as full π₁ — Kill [L, free-group model]: proper nonnormal subgroup of F₂ reaches every finite quotient, has full integer winding and normally generates F₂; finite-packet conjugacy data do not force surjectivity. Survivor [L]: actual Xi profinite surjectivity/relative algebraic closure and analytic caps. Global dyadic-root continuation remains open. E: H:InfinitePacketObstruction; R:XiTiltRelativeClosure; R:XiCappedAnalyticAtlas.
- DR finite-critical-value entire left factors — Kill [L]: Xi cannot equal F∘g with entire F of positive lower order and finitely many critical values; stated logarithmic-tract subclass also excluded. Survivor [L]: nonzero Xi critical values accumulate at0; exact factor boundary. Infinite-critical-value factors outside theorem. E: R:XiCriticalValueAccumulation; R:XiFiniteCriticalFactorRigidity; R:XiLogarithmicTractFactorRigidity.
- W1C unitary Euler factors — Kill [L]: exact principal-minor Euler factorization of a unitary matrix forces diagonal modulus1 and zero off-diagonal entries; no modulus-p^(−½) diagonal factors. Survivor [L]: diagonal-unitary classification; changed arithmetic scattering/domain remains open. E: R:UnitaryEulerFactorRigidity.
- WBF strong completion preserves compact trace — Kill [L]: finite genealogy compressions cost0; completed nonzero-fibre compact-ideal trace cost∞. Operators, adjoints and Grams converge strongly, but norm gap≥1; compact repair cannot remove it. Survivor [L]: exact finite actions and compact-perturbation invariance. Depth-uniform arithmetic completion still missing. E: H:PaperGenealogyTraceCompletion.
- TT positive displacement coefficients — Kill [L]: third-minor/slope degrees16/17; slope leading displacement coefficient −48·512·12^18·v^9(3k+1)^4(3k+4)<0 for v>0,k>−⅓ at every center; divided-difference obstruction retained. Survivor [L]: exact leading term and degree. No actual-source sign counterexample; bounded-domain/interior sign remains open. E: R:ThetaCuspRatioKineticLeading/SlopeLeading.

## ULF obstructions

60 source/completion mechanisms; surviving mathematical targets in TG, HF, CDC.

- FAIL-28 Twisted Möbius–Witt fractional index — for `a>0`, the Abel/logarithmic boundary index is `1/ζ(1+a)∈(0,1)`, hence `W_a` has no meromorphic germ at `z=1`; `a=0` gives `W₀=e^(−z)`. No Xi-occurrence lift. [L] E: H:TwistedMobiusLambertWittSeries; F194–F196; CANNOT-106/107.
- FAIL-29 "Even and odd ⇒ zero" reflection-parity torsion — odd orientation and even escape live in different graded pieces (CANNOT-110).
- FAIL-37 Adjoint-differential closability — dense closable scalar reporters already extend boundedly; the replicated shell codiagonal is nonclosable.
- FAIL-38 Normal stationary correspondence on the shell GNS completion — normality governs bounded observables, not the singular Ward response (MUST-105).
- FAIL-39 Normal-crossing completion, ordered confluence, Shale/Fock sector separation, minimal dilation uniqueness — each exact, the conjunction still lacks the source weld (CANNOT-152).
- FAIL-40 Intervention tomography — ternary countermodel fixes observer and recovery kernel, implements FE, moves nonzero charge (MUST-106, CANNOT-153).
- FAIL-41 C*-envelope / Shilov boundary — classifies the quotient after the boundary ideal is supplied (CANNOT-154).
- FAIL-42 Central-support / distributive completion — restates formation homology and the completion boundary.
- FAIL-43 Tensor amplification, nuclear exactness, projective/metaplectic coherence — no fixed-target embedding, no stable images, gauge-trivial scalar FE data (F305, F306).
- FAIL-44 Baire automatic continuity — the executable core is a dense meagre `F_σ`; countable compact atlases miss a residual set (CANNOT-156/158).
- FAIL-45 Complete-metric / isometric dense landing — completion transports the singular horizon faithfully (CANNOT-157).
- FAIL-46 Information neutrality / trace-ideal shortcut — the lift preserves off-wall superselection (F319).
- FAIL-47 Scalar/projective determinant holonomy — reflection Cartier trivialization is unconditional (F320).
- FAIL-48 Unmarked external completion curvature — erases rapidity magnitude (F322–F324).
- FAIL-49 Non-descending cost mark + bounded Xi action — the boundedness clause is an existing RH endpoint (CANNOT-164).
- FAIL-50 Finite torsion fibres + identity theorem — cofinal cyclotomic completion collapses to 0 (F326, CANNOT-101).
- FAIL-51 Cyclotomic rotation / Lorentz boost intersection; locally-finite-to-positive quotient — the required intertwiner is the isolated producer (F327).
- FAIL-52 One trace degree higher — correct interaction reader, no source-to-physical descent (F330).
- FAIL-53 Finite-stage compactness / surjective profinite tower — the live comparison is relative and non-surjective (F332).
- FAIL-54 Grammar birth / no-metabolic-birth axiom — present, or names the conclusion (F334).
- FAIL-55 Odd exteriorization, curved DG/Clifford completion, matrix factorization — encode Gamma curvature, constrain no character (F335).
- FAIL-56 Anomaly replication folded into its rank-two boundary — canonical fold refuted (F337).
- FAIL-57 Ambidextrous categorical dimension — repackages the hyperbolic ledger (F340).
- FAIL-58 Generic source-natural proof-history / face descent — co-shift covariance forces both eigenprofiles (F344).
- FAIL-59 Phantom maps, `lim¹`, proof-history loss, S-complete/GIT quotients — parent theories, no vanishing.
- FAIL-60 Law-birth rank = Krein negative index — no source morphism identifies them (F351).
- FAIL-61 One interaction direction + one Krein direction — double counting of one reflection charge (F352).
- FAIL-62 One-dimensional holonomy, FE inversion, covariant Stokes closure — fixed-frame triviality is RH (F353).
- FAIL-63 Recovery uniqueness, minimality, information neutrality — recovery reconstructs any cocycle (F354).
- FAIL-64 Weyl–parabolic self-opposition — no source theorem swaps the axes; a ternary countermodel fixes observer and legs and acts by `−1` on nonzero charge.
- FAIL-65 Idempotent/dagger completion + accumulated one-port shear — bounded upper-shear splittings exist (F365, F366).
- FAIL-66 Proof identity, confluence, subsingleton completion — erase presentations only after vanishing (F368).
- FAIL-67 GL(2) automorphic positivity — see KR-AUT.
- FAIL-68 Faithful torsion module annihilated by the wall — faithfulness + wall annihilation is RH (F372).
- FAIL-69 `K₀`/Morita/Chern/Big-Witt rapidity — only integer scalar action (CANNOT-177).
- FAIL-70 Two literal rational-adelic endpoints — covariant flag, both vanish on the reduced source (F378).
- FAIL-71 FE involutivity / KL isometry as source reversibility — lifting discards and regenerates concealed history (CANNOT-183).
- FAIL-72 Ghost propagation, cyclotomic persistence, integer-index rigidity — normalized second ghost `−1/3` (CANNOT-185).
- FAIL-73 Modular theory alone — nonerasing descent forces `t=0` only as an RH receiver (CANNOT-186).
- FAIL-74 Bogoliubov/Shale–Stinespring/Fock implementability — classifies sectors (CANNOT-187).
- FAIL-75 Higher-rank prime dynamics, measure and cocycle rigidity — the grade survives as a homomorphism (CANNOT-189).
- FAIL-76 Gamma factor / FE / archimedean positivity alone — Gamma/FE cell carries a planted off-line zero (CANNOT-190).
- Γ_R^d functional equation plus finite coefficient prefix as uniqueness — Kill [L]: every d≥3 has infinitely many independent polynomial-growth Dirichlet solutions with entire completion with either FE sign and arbitrarily long zero coefficient prefix. Survivor [L]: exact Voronoi/chart sampling relations and theta→Mellin converse; positive arithmetic/Euler membership not supplied. No degree1/2 nonuniqueness or RH counterexample. E: R:GammaRCubeFunctionalEquationAbundance; R:GammaRPowFunctionalEquationAbundance; R:GammaRPowOddTwins; R:ThetaSymmetryMellinConverse; R:GammaRealPowerKernel.
- FAIL-77 Bounded completion of the Euler product on theta `L²` — `‖E_S‖=Π(1+p^{−½}) → ∞` (CANNOT-191/192).
- FAIL-78 Scalar completion / residual vanishing — orbital response and prime-square shell survive (CANNOT-193).
- FAIL-79 Subtracting the principal `[1/p]` class — exact trichotomy, the source counterterm has the wrong phase (CANNOT-194).
- FAIL-80 Bilateral tangent admission from the FE — FE swaps grades, proves no continuity (CANNOT-195).
- FAIL-81 Linear one-marginal Hellinger boundary, Beta/Jacobi diffusion, generic dilation (CANNOT-232).
- FAIL-82 Positive dephased `T` — reflection-even, discards the odd amplitude (CANNOT-235).
- FAIL-83 Fixed-scale isometry of prime and theta history records — cubic vs infinitely flat clocks (CANNOT-236).
- FAIL-84 Scalar outer (Szegő) completion — loses odd unsquared orientation (CANNOT-237).
- FAIL-85 Finite monitored unitary realization of the exit tail — exit mean `7/4` coarse (CANNOT-238).
- FAIL-86 Direct determinant / fixed theta hazard — residues miss finite-rank horizons (CANNOT-239).
- FAIL-89/90 Mellin creator, cofinite Gamma frames, Petz recovery, nonabelian holonomy, small trace self-commutator — information-neutral, preserve every grade, cannot kill index (F524–F529).
- FAIL-91 Gamma spectators / multiplicative transport of `T` (F530–F535).
- FAIL-92 Continuous multiplicative completion / generic Halmos–Naimark dilation (F536, CANNOT-242).
- FAIL-93 Choosing a member of the same-defect completion fibre (F542–F547, CANNOT-248).
- FAIL-71r–75r anchor-era failures: mean-value comparison of completions (KR-AUT), line-anchor positivity (→ LA), surveyed discrete invariants (KR-INT), half-divisor (KR-TWN), metaplectic Kramers (KR-TWN).
- RPGT chiral-corona closures (RPGT.12, .21, .23: weak `H^{1/2}` limit + `κ₋<1` / bounded seam cost) — anchored holomorphic passages cannot lose degree at finite energy; `κ₋=κ₊` (KR-R1).
- TSBC off-line zero as a Schubert bubble emitted by literal Gaussian formation — literal formation fails by diffuse divergence, never by finite-energy emission (KR-R1).

## Endpoint no-gos

From endpoints.md: FALSE = premise refuted (implication vacuous); EXCLUDED = producer class excluded; CIRCULAR = premise is RH re-encoded. Route affected in brackets.

FALSE (10):
- F0204 Weighted Suzuki curvature first-moment bound — premise ⇔ RH ∧ `ψ(x)−x=O(√x)`, the second false under RH [FU].
- F0026 First-clock apex superlevel majorization — prime power 4 is a positive atom at the negative apex [FU].
- F0030 `ψ(x)−x=O(√x)` — false under RH (Littlewood).
- F0198 Suzuki ordinary entire characteristic limit walls (v1, v2) — targets not entire; corrected walls live [SZ].
- F0155 Fixed finite passive/thermal/state-space realization [PA; KR-FPR].
- F0166 Central-normalized prime Ising tree → XiC [KR-ISG].
- F0211 UV-transparent Hawking KMS–FDT impedance limit — premise empty [HB].
- F0231 Wold residual half-endpoint variation + critical mesh energy [TT].
- F0209 Source-selected reciprocal-power / Cassini reciprocal-likelihood carriers [PA, TH].
- F0219 Coefficient-faithful signed cross-orbit incidence (XST) [TT].

EXCLUDED (20):
- F0055 Constrained Weil aperture window: attained top excess never yields RH [RW].
- F0053 Connected-symmetry protected defect — loop charge constant on preconnected families.
- F0177 Reflected bi-heat Markov normalization — no finite time balances.
- F0193 Shared-Ward Gamma ghost descent producers — each reduces to the shared Ward endpoint.
- F0183 Route-R intrinsic producers [R].
- F0112 Route-N Gamma-sewn Krein/Kadison receivers — positive defect; modular recovery loses `ℓ¹` [N].
- F0229 Wold–Jordan continuous / Hausdorff multifibre descent — nonlinearity adds nothing.
- F0012 Bounded vertical-clock approximants — certificate is RH itself.
- F0143 Möbius–Gamma–ξ scalar/linear/homogeneous debt controllers — non-erasing cancellation is exactly RH [MC].
- F0228 HC filtered Gamma-six diagonal landing [WD].
- F0171 Exponent-zero Euler gauges of the all-negative sheet.
- F0234 Compact-open scalar descent of Wold charge — bubbles keep charge [TT].
- F0146 Complete physical coface annihilator landing — kills the theta source.
- F0252 Positive cofinal regularization of trace-one reflection incidence — no endpoint gain.
- F0207 HB producer classes (clock gauges, nonlinear evolutions, QNM renormalizations, Jost normalization, neutralization, AIME cancellation, Peierls propagators) [HB].
- F0079 FZZ same-source divisor gradient flow [PM].
- F0132 Lee–Yang marginal carrier couplings [KR-ISG].
- F0218 Moving positive tail-completion gauges (ξ-Taylor) [TT].
- F0111 ξ-root conormal positive-damping marked landing — theta cokernel landing impossible.
- F0259 Atomwise positivity of shifted ξ trace forms — needs cross-orbit cancellation [TH].

CIRCULAR (24):
- F0017 Weil–Clifford scalar coefficient positivity [RW]. F0028 First-clock principal relative capacity [FU]. F0149 Theta prime-admission receivers. F0136 Dyadic `m`-free zeta rungs [DR]. F0003 Arakelov power-orbit stability / Big-Witt square pullback [KR-INT]. F0178 Reflected character norm equality. F0167 Prime-power centered-mark collision. F0162 Global barrelled BV–Wold producer. F0251 Reduced-conductor Roos regulator. F0046 Pre-divisor second-Cartier order law. F0060 Gaussian entropy prime-cycle holonomy. F0076 EWQ source-independent diagonal Krein completion. F0128 JAS closed-flat unit-residue certificate [JAS]. F0014 Burnol Cartier/divided-shift source laws [R]. F0249 Bare reciprocal Clifford polarization. F0126 Localized zero-free approximants — proximity hypothesis is the conclusion. F0185 Route-P differentiable unitary completions [RP]. F0093 Gamma-sewn Möbius passive deletion completion. F0102 HC bounded diagonal receiver [WD]. F0186 Route-P subquantum trace defect [RP]. F0169 Prime-square Wold scale domination. F0184 Route-E parity column-load defect = Littlewood signature criterion [MC]. F0078 FZZ argument-dilation Ward cancellation [PM]. F0148 Theta Green reflected-pair + fibre neutrality — pair neutrality unconditional, adds nothing.

## Scoped catalogue

477 indexed mechanism obstructions. Section titles identify affected live routes/candidates; numbers remain stable.

### CCM-FU: prime scheduling and current bounds (39) — constrains FU, RW

- no-go-473 CCM-FU nonnegative mixed curvature across growing cores. [L] E: R:MobiusDivisorUniformGrowingCoreNegativeCurvature
- no-go-466 CCM-FU/P normalized critical Abel eventual one-sided sign. [L] E: R:CriticalAbelRoutePAsymptoticBridge
- no-go-435 CCM fixed positive exponential-clock bounded source. [L] E: R:CCMGuinandWeilFixedExponentialClockNoGo, P1:ccm-fu-fixed-clock-pole-obstruction
- no-go-424 CCM-FU fixed or undersized old-core shell payment. [L] E: R:MobiusDivisorDyadicShellDebtGrowth, R:MobiusDivisorShellAnchorDebt, R:MobiusDivisorShellAnchorComplexity
- no-go-427 CCM-FU dense high-prime old-core shell payment. [L] E: R:MobiusDivisorShellHighCore
- no-go-428 CCM-FU upper-third mixed-curvature cancellation. [L] E: R:MobiusDivisorThirdSectorMixedSign, R:MobiusDivisorThirdSectorDefectBarrier
- no-go-294 CCM exterior constant-mode adaptive-mass repair. [L] E: R:CCMActualHeadExteriorCosineAdaptiveMassWall
- no-go-295 CCM phase-locked canonical exterior packet. [L] E: R:CCMActualHeadExteriorCosinePhaseLockedNoGo
- no-go-289 CCM-FU sublogarithmic two-sided critical signed transport. [L] E: R:CCMFUSuzukiCriticalBidirectionalTransportRangeNoGo
- no-go-075 CCM all-frequency positive/scalar Ward completion. E: REF
- no-go-069 CCM causal-depth regular operator assembly. E: REF
- no-go-068 CCM Littlewood/triangular/observer/Robin producer package. E: REF
- no-go-070 CCM unframed local chiral spectralization. E: REF
- no-go-007 CCM-FU adaptive stepwise prime contraction. E: REF
- no-go-015 CCM-FU fixed weighted or square-root terminal head. E: REF
- no-go-008 CCM-FU fixed-block prime schedules. E: REF
- no-go-011 CCM-FU geometric parity certificate or defect-free prefixes. E: REF
- no-go-016 CCM-FU head/coarea Lyapunov and positive normalization. E: REF
- no-go-009 CCM-FU increasing middle front plus scalar reserves. E: REF
- no-go-014 CCM-FU inherited-state contraction. E: REF
- no-go-004 CCM-FU monotone-weight diagonal smoothing. E: REF
- no-go-005 CCM-FU separate gcd-component sign. E: REF
- no-go-013 CCM-FU transferable pair reserve. E: REF
- no-go-012 CCM-FU uniform successor averaging. E: REF
- no-go-006 CCM-FU uniformly budgeted increasing-prime elimination. E: REF
- no-go-010 CCM-FU universal nonempty-energy contraction. E: REF
- no-go-311 CCM-FU scalar rectangular-Euler inversion. [L] E: R:CCMFUSuzukiRectangularEulerNoGo
- no-go-312 CCM matched adjacent-codiagonal scalarization. [L] E: R:CCMActualHeadMatchedQuantilePolarAdjacentCodiagonal, R:CCMActualHeadMatchedQuantilePolarParabolicTransport, R:CCMActualHeadMatchedQuantilePolarParabolicCompletedSourceBoundary
- no-go-325 CCM reflection-odd wall jet at a parity-pole first contact. [L] E: R:CCMActualHeadWallJetPoleParityNoGo, R:CCMActualHeadMatchedAdjacentCodiagonalSourceBridge
- no-go-344 CCM fixed local matched/quantile graph wall. [L] E: R:CCMActualHeadMatchedQuantileLorentzConeNoGo
- no-go-351 CCM-FU clock-delayed finite-packet budget. [L] E: R:MobiusDivisorInheritedPrimeInsertionProducer, P1:ccm-fu-clock-funding-own-research-facts
- no-go-352 CCM/O fixed affine and common-clock coercivity repairs. [L] E: R:CCMActualHeadMatchedQuantileTwoOffsetEndpointNoGo, R:CCMRestrictedWeilPoleParityCommonClockEnvelope
- no-go-363 CCM finite low-rank moment carriers. [L] E: R:CCMActualHeadMatchedWallLightThirdJetCoercivityNoGo, R:CCMActualHeadMatchedQuantilePolarParabolicCrossKernelRankFactorization
- no-go-364 CCM-FU copy-compatible positive processed-core metrics. [L] E: R:MobiusDivisorArityHeadProcessedCoreHomothety, R:MobiusDivisorOrientedPrimeDilationRigidity, P1:ccm-fu-clock-funding-own-research-facts
- no-go-376 CCM-FU arbitrary cutoff growth. [L] E: R:MobiusDivisorFiniteClockCutoffGrowth, P1:rh-finite-clock-growth-boundary
- no-go-377 CCM-FU bounded-quotient current-clock repayment. [L] E: R:MobiusDivisorCurrentClockDepth, P1:rh-current-clock-depth-facts
- no-go-389 CCM-FU scalar graph-energy coercion. [L] E: R:CCMFUSuzukiGraphEnergyScalarNoGo
- no-go-393 CCM-FU delayed short-clock-span payment. [L] E: R:MobiusDivisorDelayedClockSpanDebt, P5:rh-delayed-short-clock-span-payment, P1:rh-exhaustive-clock-continuation-facts
- no-go-400 CCM matched-quantile debt-only Cauchy wall. [L] E: R:CCMActualHeadMatchedQuantileLorentzDebtGeometry

### Arithmetic cancellation: E, EDQ, HCF, T1/T2, LI, Estermann (63) — constrains MC, TT, LI, HCF; KR-DEF

- no-go-467 E boundary singleton divergence at fixed receiver order. E: R:RouteELargestPrimeFibreParity, R:RouteEFixedOrderSelectedFibreBoundary, R:RouteEFixedOrderCofactorLinearization, R:RouteEFixedOrderPrimeBandMass, P1:route-e-largest-prime-fibre-parity
- no-go-455 E hard-core exclusion as an operator-wide negative order. E: P1:route-e-hardcore-pair-field, R:RouteEHardCoreWalshSpectrum, R:RouteEHardCorePrimitiveBridge
- no-go-449 E far-prime completed-cofactor sign as global debt. [L] E: P1:route-e-largest-prime-fibre-parity, R:RouteELargestPrimeFibreParity
- no-go-436 E coordinatewise primitive parent payment. [L] E: R:RouteEPrimitiveConeParentNoGo, R:RouteEAllQuotientPowerEdgeDominance
- no-go-437 LI global real-axis scalar-sign selector. [L] E: R:LiEvenCrossGlobalRealAxisSignNoGo, P5:li-global-real-axis-scalar-sign
- no-go-425 E prime-dilation-only boundary covariance sign. [L] E: R:MobiusFirstPrimeDilationCancellation, R:MobiusCoprimeHarmonicUniform
- no-go-429 E harmonic-prefix-only Gamma–Hankel ceiling. [L] E: R:MobiusGammaHankelHarmonicPrefixNoGo, R:MobiusGammaHankelMovingRowAbel
- no-go-430 Estermann single-modulus character/inverse-twist selector. [L] E: R:EstermannCharacterFactorization, R:EstermannKloostermanZetaContent, R:EstermannKloostermanSaving, P5:estermann-degeneracy-rigidity
- no-go-296 EDQ Möbius divisor-kernel positivity. [L] E: R:EulerDeletionCoprimeKernelDiagonalization
- no-go-297 EDQ uniform one-prime core insertion bound. [L] E: R:MobiusDivisorDilationMeanUniformCoreNoGo, R:DivisorCoreMellinResidueUniformMargin
- no-go-298 T1 fixed-width rapidity diagonal localization. [L] E: R:XiMassTwoRapidityCorrelationGeometry
- no-go-275 finite-abscissa Dirichlet scalar, shift and period selector. [L] E: R:ArithmeticFunctionScalarEvaluation, R:FiniteAbscissaArithmeticUnits, R:ArithmeticDirichletTwistedBoundary, R:DirichletTranslationPeriod
- no-go-022 E bounded-density binary singleton histories. E: REF
- no-go-046 E complete factor-two activation histogram. E: REF
- no-go-044 E complete-prime/integer-prefix identification. E: REF
- no-go-045 E diagonal Gamma–Hankel Möbius reconstruction. E: REF
- no-go-024 E finite source-faithful spectral centering. E: REF
- no-go-025 E fixed-arity Hall or source-disjoint `l1` centering. E: REF
- no-go-043 E generic hard-cutoff seam reconstruction. E: REF
- no-go-027 E generic short-interval/Menon producer. E: REF
- no-go-047 E negligible-discard integer cells and fixed-power conditioned richness. E: REF, P5:route-e-negligible-discard-integer-cells, P3:route-e-conditioned-slot-divisors
- no-go-023 E nested-residual sign telescope. E: REF
- no-go-028 E same-reservoir reversal or two-shift bulk reverse supply. E: REF
- no-go-026 E signed column-load or normalizer-flux producer. E: REF, R:RouteESignedNormalizerFluxCircularity, R:RouteESignCompletePhysicalDegree
- no-go-048 E two-sided additive-hybrid Kloosterman lift. E: REF
- no-go-049 E×Gamma complete-lcm Kloosterman weld. E: REF
- no-go-038 EDQ all-prime damping/majorant shortcut. E: REF
- no-go-030 EDQ arithmetic-minimum, projected-balance, cellwise sign, or finite holomorphic phase charts. E: REF
- no-go-032 EDQ blanket positivity of the completed arithmetic half. E: REF, P5:edq-completed-global-accretivity
- no-go-036 EDQ cofinal all-frequency divisor positivity. E: REF, P5:edq-positive-divisor-frequency-tail
- no-go-031 EDQ coprime-only or prime-support-only reconstruction. E: REF
- no-go-029 EDQ endpoint/full-energy/associative refinement shortcuts. E: REF
- no-go-033 EDQ exhaustive exact critical matching by finite cutoffs. E: REF, P5:edq-fixed-cutoff-exact-critical-matching
- no-go-035 EDQ fixed complex-neighborhood subpower bound. E: REF, P5:edq-fixed-complex-neighborhood-bound
- no-go-034 EDQ uniform period-average logarithmic ceiling. E: REF, P5:edq-period-average-growth-obstruction
- no-go-148 FCRJ shrinking, fixed-window bounds, or schedule selection. E: REF
- no-go-176 HCF continuous scalar diagonal minorant or adaptive spacing. E: REF
- no-go-174 HCF finite entire Euler-gauge cancellation. E: REF
- no-go-177 HCF fixed positive-shift mixture or positive dyadic telescope. E: REF
- no-go-175 HCF norm-square-only, unpaired low-center, or absolute Poisson-alias ceiling. E: REF
- no-go-255 LI eventual negativity, generic square-cone, ordinary boundary summation, finite/adaptive prefix, sublinear repair, absolute endpoint assembly, or uniform normalized tail. E: REF
- no-go-057 LI local Bernstein or global quotient complete monotonicity. E: REF
- no-go-178 T1 fixed finite-aperture/order/type prime extraction. E: REF
- no-go-147 T2 regular/compact-open semicontinuous scalar descent. E: REF
- no-go-313 EDQ inclusive all-gcd positive completion. [L] E: R:MobiusDivisorInclusiveGcdGramNoGo, R:MobiusDivisorInclusiveGcdGramAsymptotic
- no-go-340 factorized Dirichlet-polynomial large-value selection. [L] E: R:SelectionResonanceFactorizationMain, R:SelectionResonanceFactorizationGeneralMain, P1:density-hypothesis-large-values-frontier
- no-go-353 T1 regular stationary diagonal-germ localization. [L] E: R:XiMassTwoRapiditySaddlePolarity, R:XiMassTwoRapidityStationaryPhase, R:XiMassDiagonalGermStationaryNoGo
- no-go-354 T2 normal Möbius and Chebyshev-mirror second comparison. [L] E: R:XiHeatCassiniWoldJointDepthMobiusSourceTransport, R:XiHeatCassiniWoldChebyshevDivisorMirror
- no-go-355 EDQ uniform-period replacement of physical child energy. [L] E: R:EulerDeletionEnergyPeriodSeparation, R:EulerDeletionTerminalPrimeSupport, R:EulerDeletionUpperHalfPhysicalPrimeSupport
- no-go-365 EDQ strong-drift uniform integrability and fixed-tail compactness. [L] E: R:EulerDeletionResidueMartingaleL2Limit, R:EulerDeletionResidueMartingaleDriftNoGo
- no-go-366 E complete replica-cell coprime parity. [L] E: R:RouteEReplicaCoprimeCompleteCellNoGo
- no-go-367 E global Kloosterman collision orientation. [L] E: R:Sieve/KloostermanGlobalCollisionOrientation
- no-go-368 HCF horizontal multiplicity-pole projection. [L] E: R:HedenmalmCriticalFeatureSourceHorizontalPoleBlindness, R:HedenmalmCriticalFeaturePositiveShiftVerticalL2Criterion
- no-go-380 T1 exchange cancellation of finite covariance. [L] E: R:XiMassTwoRapidityHermitianExchange
- no-go-381 HC unlabelled exchange orientation. [L] E: R:XiHorizontalCollisionExchangeOrientationNoGo
- no-go-394 E fixed absolutely summable cross-prime recurrence kernel. [L] E: R:RouteEStaticAbsoluteKernelRecurrence, P1:routes-e-p-u-q-c1-d2-l-own-research-facts
- no-go-395 HCF positivity-only uniform-grid alias variance. [L] E: R:HedenmalmCriticalFeatureUniformGridAliasNoGo
- no-go-396 HC line-conjugation-stable scalarization of ordered-prime orientation. [L] E: R:XiHorizontalCollisionOrderedPrimeCrossCurvature
- no-go-397 T2 polynomial source graphs plus fixed Bohr datum. [L] E: R:XiHeatCassiniWoldPositiveTenthAllSourceGraphDirectedMeanNoGo, R:XiHeatCassiniWoldResidualNaturalSqrtOneSidedMeanSpectrum
- no-go-412 EDQ physical initial-segment LCM positivity. [L] E: R:EulerDeletionCenteredLcmCoprimeConservation, R:EulerDeletionCenteredLcmInitialCutoffSign, R:EulerDeletionCenteredLcmMertensPanelInversion
- no-go-413 E→EDQ coefficient-blind Gamma–Hankel domination. [L] E: R:EulerDeletionRouteEAdjacentDipoleNoGo
- no-go-419 E zero-row-only Kloosterman spectral cancellation. [L] E: R:Sieve/KloostermanZeroRowSpectralComparison, P1:root-assigned-routes-fact-log
- no-go-420 T1 pointwise cancellation of complete stationary prime cone. [L] E: R:XiMassStationaryPrimeConeNoncancellation, R:XiMassStationaryPrimeConeCovarianceGrowth

### Scattering and physical action: HB, FZZ, PW, PTR (101) — constrains PM, PTR; HB

- no-go-487 FZZ divisor-mode passivity from physical response. Kill [L]: canonical passivity ⇔ dyadic zero-clock boundedness; literal parity-source spurious modes have response 17/16>1. Survivor [L]: every finite right-strip packet of multiplicity M gives orthogonal −I_M,+I_M witness blocks; `ind₋(q)=total right-strip analytic multiplicity=rank(w(t/2)−w(t))` in ℕ∞. Correlation-jet kernel exactly bounded self-similar witnesses; continuous bounded profiles have zero logarithmic mean on [1/2,1]. q-neutral does not mean radical. Open: actual witness nonnegative half-mass/Haar approximation (MC), not index equality. E: R:FermiNymanMultiplicityIndex; R:FermiNymanDyadicDifferenceRank; R:FermiNymanCorrelationKernel; R:FermiNymanBoundedSpuriousClassification; R:FermiNymanBeurlingHaarTarget; P3:pm-dyadic-defect-rank; P3:pm-correlation-jet-kernel; P3:pm-bounded-spurious-classification.

- no-go-426 PW-B subcritical scalar full-square contact. [L] E: R:ThetaCuspHawkingBMPWCrossClockSubcriticalContactNoGo, R:ThetaCuspHawkingBMPWCrossClockTranslatedTests
- no-go-438 FZZ-P balanced compact-current transfer. [L] E: R:FZZCigarParityBalancedExternalCompactCurrentNoGo, P5:fzz-p-balanced-compact-current-transfer-no-go
- no-go-439 PW-B exact compatible full/native current contact. [L] E: R:ThetaCuspHawkingBMPWOperatorAnomalyLaw, R:ThetaCuspHawkingBMPWActualOperatorAnomaly
- no-go-474 PTR fixed linear commuting-target descent. [L] E: R:PhotonicPrimeNoLinearCommutingIntertwiner, P5:ptr-fixed-linear-commuting-intertwiner-no-go
- no-go-475 PTR unital order-blind multiplicative linear port. [L] E: R:PhotonicPrimeLinearPortOrderFusionNoGo, P5:ptr-fixed-linear-order-blind-euler-port-no-go
- no-go-456 PTR single-clock stroboscopic zeta return. [L] E: P5:ptr-single-clock-stroboscopic-return-no-go, R:PhotonicFixedClockReturnNoGo
- no-go-457 PTR uniformly finite-order prime-cluster return. [L] E: P5:ptr-finite-order-prime-cluster-return-no-go, R:PhotonicPrimeInteractionOrderNoGo
- no-go-458 PTR commutative occupation of literal prime cells. [L] E: P5:ptr-literal-prime-cell-commutative-occupation-no-go, R:PhotonicPrimeSourceFrameNoncommutativityNoGo
- no-go-459 PTR commutative quotient of literal prime-source algebra. [L] E: P5:ptr-literal-prime-source-abelianization-no-go, R:PhotonicPrimeSourceAlgebraAbelianizationNoGo
- no-go-460 PTR raw cyclic trace as order-insensitive Euler landing. [L] E: P5:ptr-raw-cyclic-trace-euler-landing-no-go, R:PhotonicPrimeTripleCyclicTraceNoGo
- no-go-444 PTR sharp cylinder cutoff on all tempered distributions. [L] E: R:PhotonicCylinderDistributionCutoffNoGo, P5:ptr-global-tempered-cutoff-no-go
- no-go-445 PTR uniform bilateral imaginary loss as a real causal response. E: R:PhotonicConductiveMultimodePumpIdentity, P5:ptr-uniform-bilateral-complex-loss-causal-no-go
- no-go-440 PTR passive angular and multimode loss-flux reductions. [L] E: R:PhotonicHelicalAngularDistributionalNoGo, R:PhotonicPassiveMultimodeFluxNoGo, R:PhotonicRotatingCylinderMaterialOverlap
- no-go-431 PW-B symmetric full/native current retaining full dual contact. [L] E: R:ThetaCuspHawkingBMPWFullNativeAdjointSymmetrizer, R:ThetaCuspHawkingBMPWLiteralKernelGreenContact
- no-go-299 FZZ cubic raw zero-collar cutoff. [L] E: R:FZZCigarCubicRawCutoffNoGo
- no-go-300 FZZ Fermi-characteristic/parity-Mellin amplitude identification. [L] E: R:FZZCigarFermiCharacteristicMellinAmplitudeNoGo
- no-go-301 FZZ shared-coupling direct affine phase matching. [L] E: R:FZZCigarFermiSharedCouplingDirectPhaseNoGo
- no-go-302 FZZ one-sided radial plus additive Hermitian chiral Ward cancellation. [L] E: R:FZZCigarOneSidedRadialHermitianChiralWardNoGo
- no-go-303 FZZ one-sided radial plus scalar-real renormalized-plane Ward cancellation. [L] E: R:FZZCigarOneSidedRenormalizedPlaneWardNoGo
- no-go-304 HB full canonical action through literal unit-source receiver. [L] E: R:ThetaCuspHawkingBMFullCanonicalMatchingNoGo
- no-go-305 HB full canonical action through arbitrary literal-carrier decoder. [L] E: R:ThetaCuspHawkingBMFullCanonicalSourceEncodingNoGo
- no-go-306 HB original retarded field through literal-carrier decoder. [L] E: R:ThetaCuspHawkingBMNativeFieldMatchingNoGo
- no-go-307 HB local radial source-transpose matching. [L] E: R:ThetaCuspHawkingBMLocalSourceTransposeRigidity
- no-go-290 FZZ all-depth factorized neutral Ward selector. [L] E: R:FZZCigarParityNeutralAllDepthFactorizedWardNoGo
- no-go-291 HB symmetry-only affine-collision exclusion. [L] E: R:XiAffineCollisionSymmetryModelNoGo
- no-go-283 FZZ one-sided radial plus real compact Hessian. [L] E: R:FZZCigarOneSidedRadialRealCompactWardNoGo
- no-go-284 FZZ one common compact response for a nonzero reflected pair. [L] E: R:FZZCigarOneSidedRadialCommonCompactPairNoGo
- no-go-285 FZZ momentum-fitted radial/compact Ward selector. [L] E: R:FZZCigarParityMomentumFittedRadialCompactWardNoGo
- no-go-286 FZZ depth-one full annular Hessian universal sign. [L] E: R:FZZCigarParityTwoMarkedFullAnnularHessianNoGo
- no-go-279 HB QNM-conserved reflected-pair response. [L] E: R:ThetaCuspHawkingBMQNMConservedReflectedPairResponseNoGo
- no-go-280 HB copywise unit-phase darkness repair. [L] E: R:ThetaCuspHawkingHBUniversalCopywiseUnitPhaseDarknessNoGo
- no-go-281 HB regular five-half trapped-collision producer. [L] E: R:XiFiveHalfTrappedCollisionIntervalNoGo
- no-go-276 HB reflected normalizable reader as original horizon mode. [L] E: R:ThetaCuspHawkingBMReflectedReaderBoundary
- no-go-216 channelwise third-order Hawking/AIME cancellation. E: REF
- no-go-215 diagonal or sector-local Hawking completion. E: REF
- no-go-221 finite-state FZZ/Schwarzschild closure. E: REF
- no-go-116 FZZ canonical joint natural radial/phase incidence. E: REF
- no-go-111 FZZ charge-balanced holonomy-only replica area. E: REF
- no-go-112 FZZ external-BRST pointwise, branch, spectator, and genus shortcuts. E: REF
- no-go-114 FZZ finite normalized logarithmic-density threshold. E: REF
- no-go-113 FZZ generic tempered scalar puncture occurrence. E: REF
- no-go-118 FZZ holomorphic real-slice or horizontally stratified generator. E: REF
- no-go-119 FZZ regular finite-exponential-type physical response. E: REF
- no-go-115 FZZ same-scale scalar Laurent fusion. E: REF
- no-go-117 FZZ same-source divisor gradient flow. E: REF
- no-go-110 FZZ unmarked torus averaging. E: REF
- no-go-268 HB amplitude-independent stationary skew-kernel sign. [L] E: R:ThetaCuspHawkingBMEvenSectorSkewSectorForm, R:ThetaCuspHawkingBMEvenSectorSkewChiralEdge, R:ThetaCuspHawkingBMEvenSectorSkewConstantSquare
- no-go-201 HB analytic or finite-rank two-leg compensation. E: REF
- no-go-209 HB analytic perturbative QNM clock. E: REF
- no-go-207 HB Birmingham–Mokhtari source-probe response. E: REF
- no-go-080 HB closed-dense unbounded or projectively normalized response. E: REF
- no-go-210 HB closed-discrete finite-jet positive-clock passport. E: REF
- no-go-208 HB completed spin-two/Jost/continuum/renormalization shortcuts. E: REF
- no-go-214 HB conservative Bogoliubov or regular/common-Fock/Riesz completion. E: REF
- no-go-204 HB diagonal/compact/bounded or abstract unbounded coefficient response. E: REF
- no-go-202 HB finite-energy Hilbert, bounded-Krein, or arbitrary two-leg graph compensation. E: REF
- no-go-205 HB finite-variation damped spectral cancellation. E: REF
- no-go-203 HB finite/local/Hermitian/passive completion. E: REF
- no-go-200 HB global propagator, fixed pairing, or meromorphic scalar cancellation. E: REF
- no-go-041 HB modular spectral, positive-height graph, characteristic-kernel, principal-causal, or local residual admission. E: REF
- no-go-211 HB nonzero FE-invariant scalar response correction. E: REF
- no-go-079 HB regular passive/equivariant, arbitrary or maximal unbounded dissipative, or self-adjoint exclusion. E: REF
- no-go-213 HB scalar angular reconstruction. E: REF
- no-go-212 HB scalar Poincare-radial descent. E: REF
- no-go-206 HB Schwarz-odd diagonal or Schwarz-exchanged global Peierls realization. E: REF
- no-go-271 HB unrenormalized split-reader continuity. [L] E: R:ThetaCuspHawkingBMXiReaderSplitResidue
- no-go-198 HB zero-cusp, unmodified scalar-RSZ, or pointwise specialization. E: REF
- no-go-217 inverse-character sideband audit as physical BM closure. E: REF
- no-go-218 local Birmingham–Mokhtari pole, scalar-projective, or monodromy-only shortcut. E: REF
- no-go-224 neutral FZZ/PW counterterm sewing. E: REF
- no-go-223 positive moment-admissible PW boundary regularization. E: REF
- no-go-082 PW-B convergent endpoint moment series. E: REF, P5:pw-b-convergent-endpoint-moment-series
- no-go-084 PW-B literal global weighted Mellin dual-mass bound. E: REF, P3:pw-b-gamma-mellin-dual-domain
- no-go-085 PW-B positive, conditionally ordered, uniformly energized, or closed-linear endpoint darkness. E: REF
- no-go-081 PW-B raw Gamma skew-source scalar occurrence. E: REF, P5:pw-b-raw-gamma-skew-occurrence
- no-go-120 PW-B singular connection index or canonical Hilbert density. E: REF
- no-go-083 PW-B unit-ground-corrected Gamma scalar occurrence. E: REF, P5:pw-b-corrected-gamma-scalar-occurrence
- no-go-219 raw Birmingham–Mokhtari causal decay or two-sided boundedness. E: REF
- no-go-225 RBH complementary/wall finite part, separated-sign linear production, or passive normalization. E: REF
- no-go-222 scalar-history, regular Borel, grade-diagonal, or rescaling-invariant Parikh–Wilczek balance. E: REF
- no-go-314 HB genuine Green-pole matching by the unit-source clock. [L] E: R:ThetaCuspHawkingBMOriginalGreenPoleMatchingNoGo
- no-go-315 HB finite scalar/packet realization of the original source clock. [L] E: R:ThetaCuspHawkingBMOriginalSourceClockRigidity
- no-go-316 HB literal on-shell same-frequency, holomorphic or native-L2 realization. [L] E: R:ThetaCuspHawkingBMLiteralSameFrequencyPeierlsNoGo, R:ThetaCuspHawkingBMLiteralOnShellSourcePole, P1:hb-source-pole-frequency-defect-cochain
- no-go-326 HB spectral-root or physical-chamber cutoff-face escape. [L] E: R:ThetaCuspHawkingBMPhysicalRateNonreal, R:ThetaCuspHawkingBMOriginalMetricCorner, P1:hb-source-pole-frequency-defect-cochain
- no-go-330 HB one-counterterm or compact raw-cap shortcut. [L] E: R:ThetaCuspHawkingBMEndpointCountertermUniqueness, R:ThetaCuspHawkingBMJointSourcePrincipalContinuation, R:ThetaCuspHawkingBMOriginalCapWeakWave, R:ThetaCuspHawkingBMFullSeedCapRadialMemory
- no-go-342 HB B2 coefficientwise square-reader cancellation. [L] E: R:HBSquareReaderChannelsOnLine, P1:hb-b2-literal-peierls-facts
- no-go-356 FZZ real-factorized, symmetric and local-branch cross-depth orientation. [L] E: R:FZZCigarParityCrossDepthOrderedSourceLaw, R:FZZCigarParityExternalBRSTNeutralSymmetrizationNoGo, R:FZZCigarHigherScreeningOrderedSourceNoGo, R:FZZCigarHigherScreeningAllDepthJointNoGo
- no-go-357 PTR global-clock, uniform-frame, scalar or positive-metric transfer. [L] E: R:PhotonicPrimeClockDeningerLatticeNoGo, R:DeningerPhotonicParabolicJetBridge, R:PhotonicScalarFloquetParabolicNoGo, R:PhotonicPrimeCyclicSlabParabolicRealization
- no-go-358 PTR finite closed Floquet truncation. [L] E: R:PhotonicPrimeCyclicSlabParabolicRealization, R:PhotonicTemporalMaxwellSlabRealization
- no-go-382 PW-B finite or summable positive atomic seams. [L] E: R:ThetaCuspHawkingParikhWilczekFinitePositiveAtomicSeamNoGo, R:ThetaCuspHawkingParikhWilczekCountablePositiveAtomicSeamNoGo
- no-go-383 PW-B scalar and one-endpoint seam transmutation. [L] E: R:ThetaCuspHawkingParikhWilczekSingleEndpointSeamNoGo, R:ThetaCuspHawkingParikhWilczekTwoEmissionCoherenceNoGo, R:ThetaCuspHawkingParikhWilczekForcedContactScalarTransmutationNoGo
- no-go-384 PTR finite three-port OAM ladder. [L] E: R:PhotonicFiniteOAMPortLadderNoGo
- no-go-385 PTR bare-harmonic conormal recovery. [L] E: R:PhotonicBareHarmonicConormalNoGo
- no-go-401 PW-B single cross-metric ordered CTP readout. [L] E: R:ThetaCuspHawkingBMLiteralCyclicPeierlsCrossMetricOrientationNoGo, P5:pwb-cross-metric-order-no-go
- no-go-402 PTR fixed-`k` geometric Maxwell sideband. [L] E: R:PhotonicFixedKGeometricFloquetNoGo, P5:ptr-fixed-k-geometric-maxwell-no-go
- no-go-403 PTR finite-energy bilateral conormal boundary. [L] E: R:PhotonicConormalFiniteEnergyNoGo, P1:ptr-conormal-finite-energy-no-go
- no-go-410 PW-B direct un-oriented optical/CTP incidence. [L] E: R:ThetaCuspHawkingBMPWOpticalCTPParity, P1:pwb-ordered-null-transport-own-facts
- no-go-415 PW-B unrenormalized all-fibre zero residual boundary. [L] E: R:ThetaCuspHawkingBMPWResidualBoundaryNoGo, R:ThetaCuspHawkingBMPWResidualCuspAsymptotic, P1:pwb-residual-dominant-radial-rigidity-own
- no-go-418 PW-B fixed-calibration two-amplitude off-line incidence. [L] E: R:ThetaCuspHawkingBMPWAmplitudeIncidenceNoGo, P1:pwb-amplitude-uniform-incidence-own
- no-go-421 PW-B integrable normalized off-line cusp forcing. [L] E: R:ThetaCuspHawkingBMPWCrossClockTranslatedTests, P1:pwb-cross-clock-source-mean-nonintegrability-own

### Theta, Schur, spectral and positivity mechanisms (70) — constrains TH, RN, TG, WL, RW, SZ, LA

- no-go-489 Strict full-theta outgoing Cauchy reserve. Kill [L]: for complete theta kernel `K`, every real tail and `c>0` admit a finite negative packet of `K−c·Φ(x)Φ(y)/(e^{2x}+e^{2y})`; no uniform-rank positive Cauchy margin. Survivor [L]: exact incoming diagonal law `K(−r,−r)/(r e^{-2r}Φ(−r)²)→1/(2π)` and sharp rank-one Cauchy projection. Sharp zero-reserve PSD remains open. E: R:ThetaTailCauchyCoercivityObstruction.
- no-go-490 Reflection-compatible full-theta Cauchy reserve. Kill [L]: with `q=e^{2x}+e^{-2x}`, every real tail and `c>0` admit a finite negative packet of `K−c·Φ(x)Φ(y)/(q(x)+q(y))`. Survivor [L]: charged-cusp `|Φ(z_N)|≥A N⁵`, `J(z_N,z_N)≤D N¹⁰`, analytic boundary admissibility; `J(z_N,z_N)/|Φ(z_N)|²→0` (also weighted horizontal `L²`) forces every valid comparison rate to diverge and every dominated analytic scalar feature `f` to satisfy `f(z_N)/Φ(z_N)→0`. Unsubtracted `K` sign open. E: R:ThetaTailReflectedCauchyObstruction; R:ThetaTailReflectedBoundaryObstruction; R:ThetaTailChargedEnergyCollapse.
- no-go-491 Uniform Hardy real-zero law across theta-power deformations. Kill [L]: `F_a=θ₃h^{a/4}` has only finitely many transform zeros in `|Im w|≤½` for `a>½` and infinitely many outside; exact modular inversion does not preserve infinitely many real zeros across all `a`. Survivor [L]: infinitely many real zeros for `0<a<½`; every transcendental `a∈(0,½)` has infinitely many off-line zeros; affected parameters form an open set whose complement in `(0,½)` is closed there, countable and algebraic. `a=½` gives completed `L(s,χ₈)` and `a=⅓` gives completed `L(s,χ₁₂)` up to nonzero factors; off-line zeros at `a=⅓` would imply ¬GRH(χ₁₂). Algebraic exceptions and Xi zero confinement open. E: R:ThetaPowerHardyZeros; R:ThetaPowerStripRigidity; R:ThetaPowerZerosOffCriticalStrip; R:ThetaPowerChiEightLFunction; R:ThetaPowerChiTwelveLFunction; R:ThetaPowerTranscendentalOffLineZero; R:ThetaPowerOffLineParameterSet; P1:theta-power-family-hardy-threshold; P3:theta-power-transcendental-offline-zeros.
- no-go-492 Fixed positive geometric reserve for complete theta kernel. Kill [L]: for every real tail and `ε>0`, some finite packet makes `K−εG` negative, `G(x,y)=∫₀∞√((x+s)(y+s))Φ(x+s)Φ(y+s)ds` on positive nodes; no fixed positive geometric reserve. Survivor [L]: exact logarithmic tangent finite part with coefficient `Φ(0)²/4`; negative dimensions of `K` on any real tail equal those of its double-Laplace Bezoutian on every `Re w=σ>0`. Sign of unsubtracted `K` open. E: R:ThetaTailGeometricCoercivityObstruction; R:ThetaTailLaplaceSignature.
- no-go-493 Theta-power zero-escape receiver. Kill [L]: unrenormalized `Λ_a` zeros in every compact `|Re w|≤U`, `|Im w|≤ρ<½` are real for sufficiently small `a>0`, without RH; `Λ_a` does not tend to Xi [P]. Renormalized fixed-box exclusion under locally uniform convergence is circular [P]. Survivor [L]: small-parameter local real-rootedness and cusp-constant/Gamma-pair split; zero simplicity/asymptotic lattice only [P]. Xi zero confinement open. E: R:ThetaPowerSmallParameterRealZeros; R:ThetaPowerCuspConstantSplit; P5:theta-power-zero-escape-receiver.
- no-go-494 Theta-power shared-input seam selector. Kill [L]: every transcendental `a∈(0,½)` has an upper-half-plane disc whose `Λ_a` phase has positive Hardy relative index and adjoint seam norm `≥1`; modularity, cusp behaviour and zero-free positive source shared with Xi do not force seam contraction. Survivor [L]: explicit off-line zero → positive disc index → seam failure; an Xi-specific Euler-product input is still required. E: R:ThetaPowerOffLineDiscSeamCountermodel; R:ThetaPowerTranscendentalOffLineZero.

- no-go-482 Literal theta global all-degree cold-aperture convexity. Kill [L]: `L_j⁴ S_j(−L_j) → (log Φ(√y))'''(u)` along `L_j=(j+½)/u`; at `u=9` limit `<0`, hence eventual negative curvature. Survivor: exact signed incoming-profile law; degree-zero and full Hankel gates open. E: R:ThetaColdDegreeCornerLimit.
- no-go-483 Fixed finite local Gram realization of complete theta cleared form. Kill [L, coefficient class]: anti-diagonal normalization excludes every fixed finite falling-factorial jet representation; first row fixes any weighted-multiplication moments [P]. Survivor: exact normalized anti-diagonal limit; nonlocal/unbounded-order source feature map remains open. E: R:ThetaLocalGramObstruction.
- no-go-484 Fixed-level, rank-uniform logarithmic-Cauchy correction. Kill [L]: alternating `2m`-vector has `Q=2m(L+1−2h_m)`, `2h_m∼log m`; fixed `L` or uniformly bounded coefficient-energy repair fails. Survivor: necessary `L≥2h_m−1`, sufficient `L≥2h_m`; literal fixed-node tail becomes positive definite after translation, while corrected squared-Cauchy model is PSD for `L+log c≥2`; growing-rank literal transfer open. E: R:LogarithmicCauchyRankBoundary; R:LogarithmicCauchyUniformRepair; R:ThetaTailCauchyAsymptotic.
- no-go-485 Positive independent-cosh expansion of literal theta potential. Kill [L]: leading `e^{2x}` coefficient forces edge mass `2π` at frequency 2, contradicting negative linear residual `−9x/2`. Survivor: exact spectral-edge mass and linear-charge laws; signed/interacting source construction open. E: R:ThetaPositiveCoshPotentialObstruction.
- no-go-486 Bare first-atom theta tail globally PSD. Kill [L]: squared-source invariant `∫e^{2x}f²=(75/(44π))∫f²` forces negative incoming diagonal; analytic section density transports a negative finite Gram direction to *every* real tail. Survivor: full finite negative-index profile invariant under restriction to any tail, also for complete theta; complete-source PSD remains open. E: R:ThetaFirstAtomTailCenterObstruction; R:ThetaFirstAtomTailLocalityObstruction; R:ThetaTailAnalyticLocality.

- no-go-478 Decreasing-density contraction `0 ≤ B ≤ D` of the cleared log-moment kernel (two-uniform mixture; `D−B` value `−119221/32256` at `(−13,17)`). [L] E: R:MonotoneSourceGramContraction, P5:monotone-source-gram-contraction
- no-go-479 Generic dyadic boundary winding rigidity (continuous nonvanishing zero-mean solutions with both theta endpoint anchors realize every winding `−(2k+1)`). [L] E: R:ThetaBoundaryDyadicClassification, P5:theta-dyadic-boundary-winding-rigidity
- no-go-480 Fixed theta-shell prefix as real-zero foundation (every nonempty prefix: infinitely many nonreal, finitely many real zeros) [L]. Survivor [L]: all fixed-order literal omitted-tail jets have an exact rational moving-cutoff limit. First-Laguerre transition [L]: at `t=λ(N+1)²`, `λ>4`, normalized limit `128π⁶(4π²−λ²)/(4π²+λ²)⁴`; eventual positive sign for every fixed `4<λ<2π`, negative for `λ>2π`, including `λ=5,8`. Leaf, axiom and umbrella-wiring audits complete; no universal priority claim. Full-source low-order sign and equality ray open. E: R:ThetaFiniteShellNonrealZeros; R:ThetaMovingShellTailJet; R:ThetaMovingPrefixLaguerre; P3:la-moving-theta-cutoff-laguerre-transition; P5:theta-fixed-prefix-nonreal-zeros.
- no-go-481 Whole-strip holomorphic logarithm of literal theta source. Kill [L]: arc charges `0`, `−θ(1)/4` force an interior imaginary-axis *source* zero; no whole-strip exponential. Survivor: exact signed arc-charge and odd-cusp flatness laws; no Xi zero-location conclusion. E: R:ThetaCuspImaginaryArcCharge; R:ThetaCuspImaginaryEndpoint.
- no-go-472 C1 prime-only Loewner Gram positivity. [L] E: R:PrimeEulerLoewnerLocalNoGo, R:PrimeEulerLoewnerGlobalFarRightNoGo
- no-go-476 Theta renewal real-rate/passive finite-index loop. Kill [L]: literal positive phase kernel is not completely monotone; continued renewal denominator has infinitely many nonreal poles; reflected feedback Pick kernel has infinite positive/negative index despite trace-class critical-zero sampling. Survivor: exact positive renewal/cosh phase representation; literal square-lattice phase law open. E: R:ThetaRenewalResonanceDivisor; R:ThetaRenewalFeedbackLoop; P3:theta/theta-renewal-complex-resonance-stieltjes-obstruction.
- no-go-468 Positive even prime-scale theta source as zero-confinement principle. [L] E: R:ThetaPrimeScalePositiveSourceOffLineNoGo
- no-go-469 Raw theta half-port, finite-order scalar gauge and narrow positive-packet repairs. Kill [L]: at simple critical Xi zeros, right-normal modulus imbalance derivative `−2b(γ)Ξ′(γ)` has both signs at lower zero-density `≥5/18`; exact symmetrization has no nontrivial zero-free entire scalar gauge of any finite order. Every real clock gauge leaves log-narrow (`o(L)`) positive packets with a strict strip-order defect; ordering forces `2δ>arccos(8/11)` eventually. Two-scale packets fail at one of heights `2,4,6`; balanced three-scale repair fails at height `8`. Survivor: signed first-source moment/two-jet classifier; non-narrow literal square-lattice or additive/singular correction open. E: R:ThetaHalfLinePortOrientation; R:ThetaHalfLinePortGauge; R:ThetaHalfLineFiniteOrderGauge; R:ThetaHalfLinePortCrossings; R:ThetaPrimePacketPorts; R:ThetaPacketHarmonicObstructions; P3:theta/theta-half-line-port-alternating-orientation; P3:theta/theta-causal-germ-translation-ideal-phase-selection-formalized.
- no-go-470 Prime–modular pointwise order as matrix positivity. Kill [L]: deletion–inversion commutator has strict scalar sign and positive two-scale Laplace pairing, but full kernel has infinite positive/negative index even on prime-log scales; `B̂(τ)=Ξ(2τ)/(τ²+1/16)` retains sign-changing spectral weight. Survivor: exact Xi-linked transform and scalar monotonicity, no matrix PSD. E: R:ThetaDeletionInversionCommutator; R:ThetaQuadratureDefectSpectralKernel; R:ThetaCommutatorKernelInertia; P3:theta/theta-prime-modular-commutator-crossing.
- no-go-471 Bounded regular chronological inversion. [L] Kill: σ>−3 unit dipoles TV2 but smoothed L¹→0; finite-measure polynomial/derivative readers cannot reproduce causal jumps; compact L¹ packet observers lose separation for 1+σ≥0. Survivor: finite-signed-measure convolution injective for σ≥0; literal arithmetic recovery σ>0,t>0; exact observer derivative cost ≥2c/log(p/(2q))−(1+σ)M. Moving noncompact/collective signed estimates not excluded. E: R:ThetaChronologicalCausalJumps; R:ThetaChronologicalSingularDeconvolution; R:ThetaChronologicalPacketResolution; P3:theta/theta-chronological-boundary-positive-transfer
- no-go-461 Bounded injective theta-inverse symmetrizer. Kill [L]: actual full/centered inverse has infinite zero-Jordan history, dense range/injective adjoint; no bounded injective symmetrizer. Survivor [L]: closed history restriction spectrum {0}; compact Hilbert quotient preserves every nonzero Xi eigenvalue/full algebraic multiplicity, with actual Riesz/Fourier adapters. Canonical theta-mass-normalized quotient mode nonzero and `‖mode(z)‖≤C_A/(1+‖z‖)^A` for every A∈ℕ, uniformly at XiC(z)=0, |Im z|≤1/2, |Re z|≥1. In L²(k^(−q)dx), real translate admitted iff q<2e^(−2|a|); admitted complex Gaussian-slack orbit/finite-alphabet words vanish in quotient. q=0 history dense; 0<q<2 proper. Euler deletion product P admitted iff q<2/P²; fixed-q exhaustion escapes. Bounded translation H_q→H_q′, q′>0, iff a=0,q′≤q or a≠0,q′<q e^(−2|a|); squared norm = density-ratio essential supremum, equality excluded for nonzero shift. Tempered Fourier–Laplace extension exists iff frequency real, even when matching only all-exponential-integrable Schwartz sources. Real finite-Dirac-jet Xi kernel has dimension m(t), exactly orders r<m(t); physical Fourier pullback gives independent annihilators of every ordinary unscaled theta derivative, with first excluded jet nonzero on source. Full original tempered all-derivative annihilator classified: physical Fourier transport to Xi kernel; unique real-zero signed jets r<m(t), finite compact-test reconstruction and one joint original-Schwartz seminorm bound iff unique global tempered extension. Point support/local/global converses closed. Schwartz-valued analytic translation and weighted arithmetic landing open. Weighted off-real Xi modes remain; rapid decay/quotient occurrence supplies no reality. Open: singular graded arithmetic landing retaining quotient divisor/orientation. E: R:HedenmalmThetaDerivativeJordan; R:HedenmalmThetaDerivativeHistoryQuotient; R:HedenmalmThetaDerivativeHistoryRiesz; R:HedenmalmThetaQuotientEigenmodeDecay; R:ThetaRealShiftHistory; R:ThetaWeightedTranslationDomain; R:ThetaGradedFiniteHistory; R:ThetaPrimeDeletionWeightedAdmission; R:ThetaUnweightedDerivativeHistory; R:ThetaWeightedHistoryProperness; R:ThetaInterWeightTranslation; R:ThetaTemperedEvaluationBoundary; R:ThetaTemperedMultiplicityJets; R:ThetaTemperedSourceJets; R:ThetaTemperedEndpointClassification; R:ThetaTemperedFourierKernel; R:ThetaTemperedGlobalJets; R:ThetaTemperedPointSupport; P3:theta/theta-compact-inverse-zero-jordan-history.
- no-go-462 Coercive finite-range theta Fourier metric. [L] Kill: bounded G, c>0 coercivity, finite absolute-frequency range W and entrywise GD=D*G impossible; no self-adjoint premise. Survivor: fixed-shift n(Φ_(n+a)−Φ_n)→0, zero row sums and bounded block quadratic forms against norm²2N. Stronger all-range no-go-461 distinct. E: R:ThetaCdfFiniteRangeSymmetrizerNoGo; R:ThetaCdfFixedShiftAction
- no-go-463 Critical theta-wall finite part as a scalar positive cube energy. [L] E: R:ThetaWallCriticalPrimeCubeFinitePartNoGo
- no-go-448 O/genus fixed-part count as free-orbit selector. [L] E: R:DivisorSliceFixedPart, R:DivisorSliceFreePart, P5:genus-programme-retired
- no-go-453 Global reflected Riccati/three scalar charges as zero selector. Kill [L]: positive analytic strongly log-concave source, order-one transform, global reflected Riccati positivity and exact literal mass/half-charges admit arbitrarily shallow off-real zeros. Survivor [L]: exact charge calibration, global quantitative Riccati margin and controlled order-one damping; literal theta/Euler membership absent. E: R:ThetaRiccatiGaussianCountermodel; R:ThetaRiccatiThreeChargeCountermodel; P3:theta/theta-global-riccati-order-one-offline-countermodel-formalized; P3:theta/theta-riccati-three-charge-offline-countermodel-formalized.
- no-go-447 Cofinal theta sieve with uniformly bounded signed cusp variation. [L] Both positive and negative cusp variations diverge while signed mass tends to zero. E: R:ThetaSieveBidirectionalCuspVariation; P3:theta/theta-sieve-bidirectional-cusp-variation
- no-go-441 O reflected lag Gram positivity. [L] E: R:LagReflectionKernelNoGo, R:ReflectionVersusTranslationPositivity
- no-go-432 K-RVM generic monotone/log-concave moment-gate positivity. [L] E: R:PrimeArchRadiusGaussianGateBoundary, R:PrimeArchHermiteMomentBoundary, P1:k-rvm-finite-sixth-moment-bracket
- no-go-433 Theta positivity, log-concavity, finite moments and exact real divisor as off-line exclusion. Kill [L]: `k+t k⁽⁴ᵐ⁾` has transform `Ξ(z)(1+t z^{4m})`, preserving every real zero and multiplicity while adding off-real zeros; source can be arbitrarily close in Schwartz and exponential-seminorm topologies. Compact-tail implant additionally preserves both literal tails and any finite moments, but not the whole real divisor. Survivor [L]: complete Xi divisor plus perturbation tail `O(exp(−a exp(b|x|)))`, `b>2`, forces zero perturbation; exponent `2` is sharp. Literal modular/Euler identity or global divisor orientation remains open. E: R:ThetaDerivativePacketSpectralBoundary; R:ThetaCompactTailImplant; R:ThetaTailDivisorCapacity; R:ThetaTailCapacitySharpness; P3:theta/theta-derivative-dark-divisor-packets.
- no-go-308 SQB current finite-deck word/full-block coercivity. [L] E: P1:selberg-density-quartic-facts, R:SelbergMaassGeneratorCostGrowth, R:SelbergMaassUnipotentPaths
- no-go-193 bounded-similarity/Keldysh/theta pseudospectral selection. E: REF
- no-go-261 central theta probability convolution-root producer. [L] E: REF
- no-go-109 CLG fixed-mass/first-moment curvature reserve. E: REF
- no-go-108 CLG positive Lorentz/Hankel faces zero through two. E: REF
- no-go-107 CLG stripped/master-reserved center velocity, source-independent Bregman cone, static localization, Riccati charge, scalar reserve compression, or Bose shifted cones. E: REF
- no-go-106 CLG/TTF all-order signed positivity of individual reflected theta fibres. E: REF, P3:clg-ttf-global-odd-compensation, P5:clg-ttf-native-sixth-rank-boundary
- no-go-248 de Branges transcendence selector. E: REF
- no-go-184 EGC raw horizontal-edge majorant. E: REF
- no-go-237 FD2/GTA polarization, cone approximation, admissible approximation, or full quadratic-defect decay. E: REF
- no-go-141 finite stationary theta carrier. E: REF
- no-go-272 literal theta-series full logarithmic turn. [L] E: R:ThetaCuspComplexClockSector
- no-go-149 O lag sign, strict-margin, Gram, lower-floor, or abstract single-base shortcut. E: REF
- no-go-190 OPUC / positive circle carrier. E: REF
- no-go-040 positive mean or positive residue as spectral-gap selector. E: REF
- no-go-051 positive Selberg zero ledger. E: REF
- no-go-192 rank-one theta-lattice sewing deformation. E: REF
- no-go-104 S6F/TCD C5–D1 slope corridor. E: REF
- no-go-105 S6F/TCD generic complete reflected-Hankel landing. E: REF
- no-go-064 S6F/TCD regular star-algebra contravariant carrier. E: REF
- no-go-103 S6F/TCD static chamber, D1–C5 weld, lower-jet, monotone Schrödinger potential, second-level concavity, whole-positive-chamber, generic positive-head, atomwise-PSD, or raw matrix-Bernstein closure. E: REF
- no-go-052 SQB scalar, polynomial/native-scattering, finite-word, deck-average, norm-only character, finite-packet, nonzero-mean resummation, phase-current, common-forcing-as-occurrence, pointwise-regulator, and path-resistance shortcuts. E: REF, R:SelbergMaassBoundaryPositivity, R:SelbergMaassDiagonalLoss, R:SelbergMaassExceptionalMeanZero
- no-go-086 theta-pair/product-fibre Wigner positivity. E: REF
- no-go-121 W2C positive-cone extension or common-translation propagation. E: REF
- no-go-317 SQB positive rational-trace averaging for compact-core coercivity. [L] E: R:SelbergMaassTraceAverageNoGo
- no-go-318 prime-labelled cubic theta scalar evaluation at an Xi zero. [L] E: R:PrimeLogThetaStripWronskianCubicJet
- no-go-332 SQB universal pointwise Möbius stress sign. [L] E: R:SelbergMaassMobiusMultiplierNoGo, R:SelbergMaassPhaseStressFourier
- no-go-337 SQB all-channel averaging, level raising, or mean-zero orientation. [L] E: R:SelbergMaassAllChannelLoss, R:SelbergMaassPhaseProductMean, R:SelbergMaassPhaseProductLossLimit, P1:selberg-density-quartic-facts
- no-go-343 approximate or smoothed prime-measure Weil positivity. [L] E: R:WeilPrimeMeasureRigidityCountable, R:WeilInsertionAnyWeight, R:WeilSinglePrimeDeletionUniform, R:WeilPrimeFreeCrossing
- no-go-349 SQB whole finite-deck L2 density. [L] E: R:MaassFiniteDeckDirichletCentral, R:MaassFiniteDeckDirichletDense
- no-go-350 SQB two-dimensional vertex-grid compactness. [L] E: H:WitnessLinePoincare, R:MaassFiniteDeckCuspidalRellich, R:MaassFiniteDeckCuspidalFriedrichs
- no-go-359 RG literal totalized carrier-density continuity at real nodes. [L] E: R:RiemannGaussian/RiemannXiSuzukiCarrierRealNodeDensityNoGo, R:RiemannGaussian/RiemannXiSuzukiCarrierGlobalRealNodePatch
- no-go-369 BSH Boolean contraction and ordinary closed completion. E: P1:bsh-own-research-facts
- no-go-370 K-RVM bounded-similarity recovery and scalar completion of cofinal tails. [L] E: R:PrimeIndexedRVMNonunitarySimilarityNoGo, R:PrimeIndexedRVMPontryaginBoundarySurvivor, H:HilbertSchmidtFourthJet
- no-go-375 SQB scalar modular cusp cutoff. [L] E: R:MaassFiniteDeckHorocycleCutoffRigidity
- no-go-387 RG compact phase-flip certificate without cutoff growth. [L] E: R:RiemannGaussian/GaussianCertificatePeakObstruction, R:RiemannGaussian/GaussianCertificatePhaseFlipDigammaBound, R:RiemannGaussian/GaussianCertificatePhaseFlipCutoffBudget
- no-go-388 singular theta metric as sole closed-graph coordinate. [L] E: R:HedenmalmThetaMetricPencil, R:HedenmalmThetaMetricClosedGraphBarrier, R:HedenmalmThetaSourceDifferentialGreen
- no-go-398 K-RVM paired quartic determinant identity. [L] E: R:PrimeIndexedRVMQuarticCubicTrace, R:PrimeIndexedRVMSignedReflectionCandidate, H:HilbertSchmidtBlockDouble
- no-go-399 SQB tensor-square unitarity as finite packet selector. [L] E: R:MaassTensorSquareMultiplicity, P1:selberg-density-quartic-facts
- no-go-422 CLG degree-twelve correction with nonnegative global derivative. [L] E: R:ThetaCuspPolynomialFluxMiddleReserve, R:ThetaCuspDegreeTwelveFluxBoundary, R:ThetaCuspActualOddHeadVariance

### Singular descent, formation and completion (29) — constrains CDC, JAS, RFHM, PCS, SC, MC, RN

- no-go-181 BW barrelled Wold certificate. E: REF
- no-go-166 controlled arithmetic Leibniz/formal-deformation producer. E: REF
- no-go-172 finite two-packet rational/differential prime formation. E: REF
- no-go-242 finite, differential, modulus/Newton, power-profield/Jensen, inertia, orbit, deformation, fixed-dimension passports, or squarefree-half regularization. E: REF, P5:dyadic-root-laplace-source-mass, R:SquarefreeConvolutionHalfLaplaceAllClocksNoGo, R:SquarefreeConvolutionHalfHeatMass, R:PoleFactorTwoThirdsLowerBound
- no-go-161 flat/split homological provenance. E: REF
- no-go-162 formation depth, passive recovery, finite Gaussian fusion, or abstract sublinear filling as coercive producer. E: REF
- no-go-065 HDL ordinary residue or continuous coface descent. E: REF
- no-go-228 JAS diagonal/flat/nilpotent/Haar synthesis. E: REF
- no-go-230 JAS multivalued square-zero quotient landing. E: REF
- no-go-229 JAS/RFHM all-prime reversible literal sewing. E: REF
- no-go-231 JAS/RFHM direct prime-torus action. E: REF
- no-go-183 KMSS order-independent scalar Koszul completion. E: REF
- no-go-037 L common integrable original prime-Green primitives. E: REF, P3:route-l-l1-original-circle-injectivity
- no-go-153 L fixed-reader singular relation. E: REF
- no-go-154 L Hausdorff operator/multifibre descent. E: REF
- no-go-155 L normalized cofinal exact-prime Green-source convergence in original Meyer topology. E: REF, P3:route-l-cofinal-green-source-limit
- no-go-250 NDS reduced-conductor regulator and nodal naturality. E: REF
- no-go-054 ordinary-limit or perfect-shadow annihilation of a derived class. E: REF
- no-go-157 PCS co-shift-natural selective boundary. E: REF
- no-go-160 Real-corona intrinsic local-index transgression. E: REF
- no-go-092 Route-R internal energy/diagonal multiplication, moving clock, or bounded cross-prime lift. E: REF
- no-go-169 SC finite-port Stokes landing. E: REF
- no-go-171 SC scalar unitization, unrestricted additive determinant, or skew-adjoint additive restriction. E: REF
- no-go-170 SC unmarked pointwise rigged-fibre geometry. E: REF, R:SourceHorizontalRiggedKreinWallSingularityNoGo
- no-go-165 split additive-exponential Hopf hidden-kernel mechanism. E: REF
- no-go-159 XST signed cross-orbit incidence. E: REF
- no-go-333 C1 positive nuclear-root transport of Route-N projective leakage. [L] E: R:GammaSewnPluckerRouteNProjectiveLeakageNoGo, R:DeningerPrimeGammaLowerCauchyFiniteGramApproximation
- no-go-360 RHist scalar positive darkness with finite continuous-observer price. [L] E: R:XiCanonicalRepairPairPositiveDarkHistoryNoGo, R:DeningerBigWittCrossPrimeRHistPriceEscape
- no-go-372 RHist square-root singular rescaling. [L] E: R:DeningerBigWittCrossPrimeRHistSingularRescalingNoGo

### Ward, Suzuki, prime–Gamma and operator landing (76) — constrains WD, SZ, RP, PA, RN, W1C, SEC, MSC, APF, HF

- no-go-488 Conformal Hodge positivity as faithful off-line carrier. Kill [L]: `p(V_cu)=e^{κc}p(u)` makes every nonzero character with `Re λ≠κ` unbounded; positive invariant form is faithful iff divisor real. Survivor: conformal critical-line completion; causal Hardy model retains right-half zeros [P], and source-derived faithful/nonconformal pairing remains open (CANNOT-462). E: R:ConformalHodgeBlindness; H:EntireMultiplierDefectUniversality; P1:hf-positive-hodge-attack/facts.

- no-go-464 Burnol–theta conjugacy-only holonomy under amplitude gauge. [L] E: R:PrimeBurnolThetaAmplitudeGaugeNoGo
- no-go-450 STC rank-two local defect as finite global negative index. Kill [L]: positive even smooth source with rank-two pinned boundary defect and HS inverse has infinitely many off-real inverse eigenvalues; no Pontryagin carrier of fixed finite negative index contains them all. Survivor: source-specific global sign/index, not local defect rank. E: R:STCUniversalBoundaryPontryaginCountermodel.
- no-go-451 STC one fixed closed normalized source-to-seam graph. [P] E: R:STCRiggedPrimeSeamBound
- no-go-452 STC bounded fixed rigged Xi-divisor reading. E: paper source unlocated
- no-go-446 STC uniformly bounded linear all-height source-to-seam landing. Kill [L]: normalized physical-ordinate squarefree sources become orthogonal as `σ↓1`; bounded maps to a separable seam retain nonzero limits at at most countably many heights. A norm-continuous nonzero all-height FE–Schwarz seam forces transport norms to diverge. Survivor: unbounded/domain-sensitive landing. E: R:PhysicalOrdinateTransportNoGo; R:STCPhysicalOrdinateSourceOrthogonality; P3:route stc/stc-physical-ordinate-transport-singularity.
- no-go-442 U finite-prime shifted-Xi Pick positivity. [L] E: R:XiShiftEulerFinitePrimePoleNoGo, P5:xi-shift-finite-prime-pick-positivity-no-go
- no-go-443 STC bounded flat-gap seam reader. Kill [L]: full prime feature seam reader is nonclosable; compact-band and Gaussian bounded spectral readers fail. Survivor: unbounded domain-sensitive transport current. E: H:HyperbolicGapFlatCompletion; R:STCFlatGapPrimeLogReaderNoGo; R:STCFlatGapMeasureReaderNoGo; P3:route stc/stc-flat-gap-exterior-spectral-reader.
- no-go-434 W1C bare Clifford discrete spectrum or compact-resolvent occurrence. [L] E: R:WeightOneCliffordSpectralNoGo, P5:w1c-bare-clifford-eigenvalue-occurrence
- no-go-309 G-CE real-reflection cancellation. [L] E: R:MobiusGammaXiRealReflectionCancellationNoGo
- no-go-292 Suzuki odd-phase diagonal quadratic readout. [L] E: R:SuzukiVolterraPhaseOddDiagonalNoGo
- no-go-282 Suzuki torque-only second-jet selector. [L] E: R:SuzukiTwoJetShiftedHankelGate, R:SuzukiTaV2ActualSecondDefectBound, R:SuzukiTaV2ActualSecondDefectJetCofinalLimit
- no-go-253 absolute or merely relative Gamma anomaly cancellation. E: REF
- no-go-185 APF source-null or positive winding. E: REF
- no-go-135 completed Riesz clock descent through marginal quotient. E: REF
- no-go-257 critical scalar/Jordan Suzuki curvature summation. E: REF
- no-go-021 D2 boundary-to-interior propagation. E: REF
- no-go-128 D2 order transport through physical two-edge squares. E: REF
- no-go-123 directed prime–archimedean KMS/passive completion. E: REF
- no-go-088 fixed actual-head matched CCM compensation of Suzuki transition core. E: REF
- no-go-072 fixed local Suzuki Cartan/Stokes germ. E: REF
- no-go-132 fixed-affine Suzuki signed compensation. E: REF
- no-go-143 fixed-interior Ward majorant. E: REF
- no-go-067 fixed-rank positive Suzuki/Ward resolution. E: REF
- no-go-071 G finite zero-mass width high-pass. E: REF
- no-go-158 G-CE finite local analytic annihilator or fixed ceiling. E: REF
- no-go-087 growing-rank positive Cartan fission as Suzuki/Ward producer. E: REF
- no-go-133 higher fixed Suzuki contact as RH endpoint. E: REF
- no-go-076 MSC ordinary/stable Hilbert and fixed-rigging transport. E: REF
- no-go-050 P ordinary physical scalar depth completion. E: REF
- no-go-258 positive same-phase shared-plane Suzuki fusion. E: REF
- no-go-245 Route-P direct determinant and scalar/Rees/cubic matching. E: REF, R:RoutePPrimitiveGammaJuliaPhysicalStokesPivotWallTransferNoGo
- no-go-074 Route-P matrix-complete subquantum repair. E: REF
- no-go-246 Route-P positive/passive/scalar landing. E: REF
- no-go-091 shared-Ward coherent quadratic mixing and Gamma-six untwisting/localization. E: REF
- no-go-077 shared-Ward finite-index/reflection carrier. E: REF
- no-go-131 square-root PNT envelope as Suzuki scale-order producer. E: REF
- no-go-130 Suzuki diagonal Jordan compactification. E: REF
- no-go-089 Suzuki divisor-blind cross-sewn holomorphic regularization. E: REF
- no-go-129 Suzuki fixed-scale dressed transition-core producer. E: REF
- no-go-078 Suzuki wall-light finite-linear compression. E: REF
- no-go-259 unrenormalized Suzuki Ward energy. E: REF
- no-go-319 cofinal Sonin-isometric Euler four-unit repair. [L] E: R:EulerPreScalarGammaCofinalSoninIsometryNoGo
- no-go-320 signed-Eulerian top-fibre Plücker carrier. [L] E: R:PrimeGammaSignedEulerianTopFiberNoGo
- no-go-321 Suzuki positive/affine completion of the atomic–continuous current. [L] E: R:SuzukiWardContinuousCoDivergence, R:SuzukiWardCompletedLightResidualNoGo, R:SuzukiCompletedOutgoingDilationBalance
- no-go-322 Suzuki Green-boundary orthogonal closure split. [L] E: R:SuzukiTaActualResolventHerglotzEnergy, H:DeficiencyResolventBoundaryQuotient
- no-go-323 reflection-compatible scalar shorting of the Xi conormal current. [L] E: R:XiWardCubicScalarShortingNoGo
- no-go-324 singleton-additive synchronized Gamma recovery. [L] E: R:GammaSewnSynchronizedRecoveryMixedCurvature
- no-go-327 Route-P ordinary source-Hilbert real-axis theta reporter. [L] E: R:PrimeLogThetaStripReporterBoundary, R:PrimeLogThetaFourLevelLowerClosedGraphLanding, R:PrimeLogThetaRealAxisAmbientHilbertObstruction, R:PrimeLogThetaRealAxisClosableReaderNoGo
- no-go-328 SP-E positive terminal-seam compensation. [L] E: R:SPEQuantileRieszSourceTransport
- no-go-329 D2 real-flux-only transfer to Q. [L] E: R:PrimeArchD2QObliqueFlux
- no-go-331 SP-E quantile/Suzuki independent-estimator combination. [L] E: R:SPEQuantileRieszRelativeCarrier, R:SPEQuantileRieszSuzukiEulerianBridge, R:CCMUnitRieszCausalLaplaceBridge
- no-go-334 Route-P bounded Big-Witt seam for the labelled Gamma profile. [L] E: R:GammaValuationSchurBigWittPrimeSeamNoGo, R:GammaValuationSchurLabelledProfile
- no-go-335 Route-P scalar physical signed-word carrier. [L] E: R:PrimeGammaPhysicalWordHyperoctahedralBlindness, R:PrimeGammaCauchyCubicSignedEulerianCurvature
- no-go-336 Suzuki unpaired zero-time divisor velocity. [L] E: R:SuzukiWeilZeroVelocityNoGo
- no-go-338 Suzuki reflected-history abelian prime-chain transport. [L] E: R:SuzukiReflectedHistoryPrimeChainBoundary
- no-go-345 Suzuki/P direct finite Hermitian pullback. [L] E: R:SuzukiBoundaryExcursionJuliaKreinHermitianNoGo, R:SuzukiBoundaryExcursionJuliaKreinLightLift
- no-go-346 Suzuki rooted endpoint contraction. [L] E: R:SuzukiRootAnchoredWeightedBoundaryExcursion, P1:routes-e-p-u-q-c1-d2-l-own-research-facts
- no-go-347 SP-E/P one-label diagonal clock transport. [L] E: R:SPEQuantileRieszRoutePClockDiagonalNoGo, R:SPEQuantileRieszRoutePPluckerCocycle
- no-go-348 P/CCM finite-cell anti-alignment. [L] E: R:FrankensteinRoutePCCMGammaSixFiniteAntiAlignmentClassification
- no-go-361 SP-E/P finite stationary history and stationary null translation. [L] E: R:SPEQuantileRieszCovarianceKernelAllHistoryGrowthNoGo, R:SPEQuantileRieszRoutePTerminalParabolicConnection, R:SPEQuantileRieszRoutePTerminalIrreducibility
- no-go-362 Suzuki finite-head recurrence and fractional transition-core correction. [L] E: R:SuzukiCausalDepthFrostmanRecurrenceNoGo, R:SuzukiCausalDepthFiniteHeadRecurrenceNoGo, R:SuzukiTransitionCoreAsymptoticSaturation
- no-go-373 SP-E/P common-centroid translation gauge. [L] E: R:SPEQuantileRieszPrimePowerHistoryTranslationGauge, R:SPEQuantileRieszRoutePTranslationGauge, R:SPEQuantileRieszRoutePCentroidGaugeFix
- no-go-374 D2 passive KMS completion and scalar cancellation. [L] E: R:MobiusIncidenceSourceCompletionSingularity, R:MobiusIncidencePassiveCompletionNoGo, R:MobiusKMSScalarCancellationCapstone
- no-go-379 MSC threshold-tracked real-power rigging. [L] E: R:HedenmalmGammaSewnSquarefreeFisherThresholdTrackedRigging
- no-go-386 P/SP-E finite Lorentz-graph coercivity. [L] E: R:SPEQuantileRieszRoutePLorentzGraphKernel, P1:p-sp-e-translation-gauge-own-research-facts
- no-go-390 D2 source-selected reciprocal-power moment tail. [L] E: R:ThetaCuspCalibratedPowerReciprocalEvenTailNoGo, P1:d2-all-order-source-own-research-facts
- no-go-391 EGC reflection-only shifted-pole correction. [L] E: R:XiMeromorphicCauchyPairReflectionCorrectionNoGo, R:XiMeromorphicCauchyPairAllCopyCenteredCorrection, R:XiCauchyPairShiftResidueSourceTrace
- no-go-392 G symmetric Schwarz-cap regularization. [L] E: R:XiWardSchwarzCapTauOddNoGo, P1:g-own-research-facts
- no-go-404 Ward baseline-cancelling nonnegative cross kernel. [L] E: R:WardAnnulusCrossKernelMassRigidity, R:WardAnnulusCrossKernelWindowMass, R:WardAnnulusCrossKernelBudgetCeiling, P1:zeta23-beyond-bandwidth-one-proportion
- no-go-405 P/SP-E transport-credit-only matched history. [L] E: R:SPEQuantileRieszRoutePWeightedCreditEscape, R:SPEQuantileRieszRoutePTransportHistoryEscape, R:SPEQuantileRieszRoutePUnitRieszRenewalBridge
- no-go-406 SV2 finite Schur anchor-jet identification. [L] E: R:SuzukiFiniteJetGlobalIdentificationNoGo
- no-go-407 P/SP-E globally holomorphic literal unit-Riesz source. [L] E: R:SPEQuantileRieszRoutePSourceSpectralPole, R:SPEQuantileRieszRoutePSourcePoleResidue, R:SPEQuantileRieszRoutePSourcePoleGaugeJet
- no-go-408 P/SP-E blanket normalized history passivity. [L] E: R:SPEQuantileRieszRoutePSourceFixedAmplitudeOscillation, R:SPEQuantileRieszRoutePLinearHistoryEscape, R:SPEQuantileRieszRoutePLinearLowerThreshold, R:SPEQuantileRieszRoutePLinearFloorCriterion
- no-go-414 P/SP-E positive-semidefinite active-head strict cross. [L] E: R:SPEQuantileRieszRoutePActiveHeadHistorySurvival, R:RoutePPrimitiveBurnolGramModularFaithfulness
- no-go-423 SEC asymptotic adjacent Calkin-small seam selection. Compact-ideal trace cost=0 iff endpoint charges equal, otherwise ∞; off-line cofinal edges remain infinitely costly despite essential norm→0. [L] E: R:XiPrimeSeamAdjacentEssentialNormNoGo; R:PaperPrimeSeamIdealTrace

### Analytic roots, multiplicity and regularization (12) — constrains DR; KR-TWN, KR-UCF

- no-go-454 Mass-only bounds for a unit-height off-line Poisson bump. [L] E: R:DisplacementMassBlindness, R:CriticalLinePoissonPotential
- no-go-260 compact Thorin/Markov/seam-log Hankel. E: REF
- no-go-063 convolution-inverse analytic twins. E: REF
- no-go-094 finite holomorphic/difference-form Yang–Baxter selector. E: REF
- no-go-061 fixed-domain same-fibre holomorphic Kramers family. E: REF
- no-go-039 lift multiplicity in Green/prime-port quotients. E: REF
- no-go-269 paired-eta analytic square-root detour. [L] E: R:PairedEtaRootContinuationBoundary
- no-go-270 positive convolution square as a causal-root growth bound. [L] E: H:PositiveConvolutionSquareGrowth, R:ZetaPoleHalfCellRemainder, R:ZetaPoleHalfArithmeticLaplace
- no-go-254 reciprocal-Xi Clifford split. E: REF
- no-go-060 symplectic doubling, universal even multiplicity, or quadratic-symbol orientation. E: REF
- no-go-339 one-point Cauchy marginal as horizontal-displacement detector. [L] E: R:PoissonSmoothedPicketFenceCauchyLaw, P1:cauchy-marginal-horizontal-displacement-blindness
- no-go-371 MPLF bounded forward raw-jet recovery. [L] E: R:MeixnerRootPrimeLaplaceForwardBridgeNoGo, R:MeixnerRootPrimeLaplaceCofinalGramClassification

### Other finite, scalar and source-blind selectors (87) — constrains class kills (route-class obstructions) and all routes

- no-go-477 Route T normalized growing-core Mellin residue domination. [L] E: R:DivisorCoreMellinInverseGeometricNoGo
- no-go-465 Uniform local contraction or mixed-cone SOS as free-orbit certificate. E: P1:uniform-certificate-program, R:ZeroInfluenceStochastic, R:ConePositivstellensatzFailure
- no-go-310 finite nilpotent determinant detector. [L] E: H:KammeyerDeterminantApproximationCore, H:KammeyerDeterminantApproximationApplications
- no-go-293 unchanged timelike-mass transport to Vaughan near-diagonal phase. [L] E: R:XiMassNearDiagonalStationaryNoGo, R:XiMassTwoRapidityCorrelationGeometry
- no-go-277 finite-cutoff compensating-infinity or QFI selector. [L] E: R:FiniteCutoffCompensatingInfinityNoGo, R:FiniteCutoffQFIHigherContactNoGo, R:FiniteMobiusLeftOverflowEscape, R:FiniteMobiusRelativePhaseQFIUniversalNoGo, R:CofinalQFICircleNoGo
- no-go-278 prime-face gauge or bounded-cutoff homology selector. [L] E: R:PrimeFaceBoundaryGauge, R:PrimeProductCutoffContraction
- no-go-167 all-prime Fermat-quotient carry selector. E: REF
- no-go-241 boundary-resolvent shortcut. E: REF
- no-go-252 bounded Marcinkiewicz/Yoneda descent. E: REF
- no-go-239 bounded strict-frontier gauge. E: REF
- no-go-138 C1 literal global-mean Pluecker moment landing. [L] E: REF
- no-go-265 C5 pointwise Jensen prime factorization. E: REF
- no-go-263 centered abelian zeta-gas socle limit. E: REF
- no-go-019 continuous Beurling regularity or thin-deletion asymptotics. E: REF
- no-go-002 CTF finite positivity, fixed-tail weight, or perturbative bounded repair. E: REF
- no-go-226 diagonal thermofield purification. E: REF
- no-go-095 differential-algebraic arithmetic heat carrier. E: REF
- no-go-262 direct prime Ising. E: REF
- no-go-191 DQPT. E: REF
- no-go-139 F2 compact Hausdorff synchronization. E: REF
- no-go-137 F2 literal regularized trace-moment weld. [L] E: REF
- no-go-059 faithful integral Arakelov/Frobenius characteristic-polynomial producer. E: REF
- no-go-266 finite ABHN/Bruhat landing. E: REF
- no-go-232 finite critical-observation cover as nonabelian selector. E: REF
- no-go-134 finite Feller tensor admission as selector. E: REF
- no-go-251 finite residue positivity. E: REF
- no-go-126 finite retained-prime/Dirichlet annihilator. E: REF
- no-go-227 finite-cylinder double realization. E: REF
- no-go-001 finite-prefix, relabelling, weighted-coefficient, or formal-inverse continuation. E: REF
- no-go-125 finite-prime D2/P tail. E: REF, R:PrimeArchFinitePrefixSubcriticalScheduleNoGo
- no-go-287 finite prime-correct co-moving Levinson depth packet. [L] E: R:XiMassLevinsonComovingDepthChargeNoGo
- no-go-220 finite/moving-horizon mass sign closure in HB. E: REF
- no-go-058 first-Laguerre line anchor from generic positive kernels. [L] E: REF
- no-go-122 five-point angle concavity promotion. E: REF
- no-go-003 fixed finite critical-locus splitting weights. Kill/survivor [L]: finite holomorphic decaying test family with invertible line-pair derivative matrix admits a distant off-line quadruple plus support slides preserving every test value. Exact local compensation law; regular-tuple hypothesis required, no actual-Xi deformation or RH counterexample. E: REF, R:CriticalLocusRegularTupleBlindness
- no-go-053 fixed pair-even or interior-convergence individuation. E: REF
- no-go-199 fixed-kernel, target-scaled, gauge, or cross-pair HB production. E: REF
- no-go-144 four-unit operator-norm transport. E: REF
- no-go-267 fractional-part extraction. E: REF
- no-go-238 full-sector or compact–cofinal repair. E: REF
- no-go-273 Ghaboussi saddle/de Rham shortcuts. [L] E: R:GhaboussiSaddleDeRhamAudit, H:UniversalDeRham
- no-go-234 GIT word-trace gluing. E: REF
- no-go-066 HC bounded diagonal landing. E: REF
- no-go-093 Hurwitz associated-tensor fixed-vector selector. E: REF
- no-go-194 independent-phase/Riemann–Siegel log mean. E: REF
- no-go-042 Levinson profile-slope improvement. E: REF, R:Sieve/DifferentiatedBarbanVehovQuadraticHorizonEnergy
- no-go-288 positive energy of the symmetric reciprocal Levinson pair. [L] E: R:XiMassLevinsonSymmetricReciprocalEnergyNoGo, R:XiMassLevinsonSymmetricReciprocalLanding
- no-go-179 literal Euler half-density bounded completion. E: REF
- no-go-195 mollified off-line first moment and Jensen-gap closure. E: REF
- no-go-017 Montgomery pair-form positivity as a horizontal selector. E: REF
- no-go-247 moving finite-prime escape cure. E: REF
- no-go-140 NB/BD canonical raw-Möbius approximation. E: REF
- no-go-062 non-diagonal twin-factorization freedom. E: REF
- no-go-233 paired irregular determinant purity. E: REF
- no-go-274 Painlevé III(D₆) polynomial-exponential Xi bridge. [L] E: R:XiPainleveTauGaugeNoGo, P3:painleve-iii-xi-differential-gauge-no-go
- no-go-099 PEP exponent-zero negative-sheet gauge. E: REF
- no-go-055 persistent cofinal cyclotomic-zero completion. E: REF
- no-go-243 physical dilation, BBM pullback, or finite autonomous spectrum. E: REF
- no-go-244 positive critical-prime Fock determinant. E: REF
- no-go-236 positive diagonal repair. E: REF
- no-go-173 positive or naive signed Euler–Wold budget descent. E: REF
- no-go-098 PPM centered-prime natural-power monodromy. E: REF
- no-go-182 prime-Poisson common recovery or internal sewing. E: REF
- no-go-124 prime-window phase supply as selector. E: REF
- no-go-188 printed Connes–Consani prime normalization. E: REF
- no-go-090 projected versus joint prime–Gamma naturality. E: REF
- no-go-056 proper derivation-stable Steinberg three-jet quotient. E: REF
- no-go-197 regular, tempered, finite-action, or sparse-local-jet FZZ selection. E: REF
- no-go-187 residue-scale fitting. E: REF
- no-go-096 Ritt/log-tower cyclic/unicritical/tree invariant differential. E: REF
- no-go-073 SCE strict-convex event sign principle. E: REF
- no-go-264 source-horizontal annealing. E: REF
- no-go-189 source-independent diagonal Euler–Wick Hilbert/Krein completion. E: REF
- no-go-196 Speiser critical-line sign. E: REF
- no-go-018 square-summable odd source promoted to uniformly bounded tensor powers. E: REF
- no-go-235 standard CGL packet. E: REF
- no-go-168 TD/C1 raw positive supercarrier. E: REF
- no-go-249 time-one Gamma-jet Fock boundedness. E: REF
- no-go-020 trace-one positive cofinal regularization. E: REF
- no-go-127 two-atom centered Euler truncation. E: REF
- no-go-240 U scalar source-capital inference. E: REF
- no-go-256 universal squared-Euler anti-Löwner positivity. E: REF
- no-go-378 CTF integrable/summably-Cauchy moving-tail `L¹` compactness and fixed finite-dimensional Lipschitz tail repair. Kill [L]: each fixed smooth tail space has a positive cofinal residual floor; at critical `ρ`, eventual residual upper bound `L` requires `dist(Kρ,W)≤L|ζ′(ρ)|`, so `ζ′(ρ)=0` forces unbounded residuals. Absolute Taylor-remainder majorant grows with jet order on the needed `[0,log N]` window; it does not close the moving-tail route. Survivor [L]: growing-jet Möbius-prefix rows, exact `8/log N` exterior bound and signed projection/Abel decomposition; joint small-time cancellation or all-grade orientation remains open. E: R:ChronologicalTailL1IntegrableNoGo; R:ChronologicalTailL1CauchyNoGo; R:ChronologicalFiniteTailObstruction; R:ChronologicalGrowingMomentSource; R:ChronologicalBoseCothLocalBounds; R:ChronologicalGrowingSignedProjection; P3:chronological-growing-moment-source.
- no-go-409 high-block uniform sharp-head energy. [L] E: R:HighBlockSharpEnergyRefutation, P1:high-block-sharp-energy-refuted
- no-go-411 grid modulus-only cell surplus. [L] E: H:GridDeviceModulusOnlyNoGo
- no-go-416 slope-only off-line-moment RH consumer. [L] E: R:MollifiedGateConstantFloor, P1:offline-moment-slope-obstruction
- no-go-417 mollified mean-square gate below its exponential floor. [L] E: R:MollifiedGateConstantFloor, P1:estermann-analytic-layer
