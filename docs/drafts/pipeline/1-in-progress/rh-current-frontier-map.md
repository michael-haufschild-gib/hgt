# RH research ledger

**No route proves or disproves RH.** This register separates **24 active routes**,
**37 named candidates**, and **388 closed mechanisms**. “Active” means a formal
route architecture with an independent mathematical problem still open, not a proof in hand.

[Active routes](#active-routes) · [Route candidates](#route-candidates) ·
[Killed routes and subroutes](#killed-routes-and-subroutes) ·
[Shared infrastructure](#shared-infrastructure-and-unlabelled-continuation-problems) ·
[Evidence and terminology](#evidence-and-terminology)

## How to use this ledger

- Find an active route or candidate below. Each entry gives **Closed**, **Open**, and **Evidence**.
- For an abandoned approach, use the [grouped no-go catalogue](rh-killed-routes.md):
  every entry retains the exact obstruction and its positive survivor / remaining problem.
- For current theorem statements, follow each updated entry's Lean-source links.
  Earlier hypotheses, alternate fronts and detailed references remain in the
  [preserved reference](rh-frontier-reference-2026-09-12.md); current entries supersede its old frontiers.
- Route labels are lookup keys, not claims of independence. A receiver ending in RH
  does not prove its source premise. A killed subroute does not kill its whole family.

**Source-audit cutoff: 2026-09-21, `801fdb77d99ae7989a85dd658e8943e7e5de8552`.**
Reconciled the 58-file formal-source delta since the prior cutoff
`e318fb81324a3a253982b526510bf8af9c856af0` (49 additions and 9 modifications).
No builds, Lean checks, tests, lint or index refresh were run for this ledger update.

## Active routes

### Find a route

| Family | Active routes | Route candidates |
|---|---|---|
| Current, Ward and prime–Gamma | [CCM-FU](#ccm-fu--completed-current-and-fixed-aperture-suzuki-checkpoint), [D2](#d2--continued-primearchimedean-free-sector-passivity), [G](#g--ward-orientation), [MSC](#msc--möbius--sonin-affine-critical-boundary-renormalization), [P](#p--paired-primegamma-signed-exterior-wall), [SP-E](#sp-e--signed-prime-dilation-versus-continuum) | [BSH](#candidate-bsh), [CTF](#candidate-ctf), [EGC](#candidate-egc), [PBM](#candidate-pbm), [SC](#candidate-sc), [SEC](#candidate-sec), [TK](#candidate-tk), [W1C](#candidate-w1c) |
| Arithmetic cancellation | [E](#e--squarefree-wold-transport), [T1](#t1--theta-tail-core-current), [T2](#t2--natural-abel-singular-wold-divisor), [HC](#hc--horizontal-collision-charge), [LI](#li--finite-paired-li-prime--gamma-order) | [EDQ](#candidate-edq), [EWJ](#candidate-ewj), [HCF](#candidate-hcf), [HJ](#candidate-hj) |
| Weil, theta and paired positivity | [C1](#c1--class-space-quotient-and-global-weil-positivity), [O](#o--restricted-weil-ground-and-genus-lag-order), [Q](#q--exterior-paired-value-passivity), [CLG/TTF](#clgttf--completed-theta-bezoutian-no-escape), [SV2](#sv2--suzuki-projective-limit-and-shifted-kernel-inertia) | [AKC](#candidate-akc), [FEL](#candidate-fel), [GTA](#candidate-gta), [PMP/LPC](#candidate-pmplpc), [S6F](#candidate-s6f), [SQB](#candidate-sqb), [TCD](#candidate-tcd), [UEB](#candidate-ueb) |
| Cofinal source comparison | [STC](#stc--exterior-sonin-seam-coherence), [CSB](#csb--cofinal-bernstein-sourcetarget-comparison), [U](#u--adaptive-shifted-xi-hankel-frontier-renewal), [RG](#rg--gaussian-arithmetic-and-suzuki-transport-positivity) | [BPC](#candidate-bpc), [K-RVM](#candidate-k-rvm), [MPLF](#candidate-mplf), [RG-ETA](#candidate-rg-eta), [RG-HF](#candidate-rg-hf), [RHist](#candidate-rhist) |
| Singular descent | [CDC](#cdc--constitutive-dagger-confluence), [L](#l--singular-greenbv-to-physical-descent) | [APF](#candidate-apf), [HDL](#candidate-hdl), [IRK](#candidate-irk), [JAS](#candidate-jas), [PCS](#candidate-pcs), [PSRC](#candidate-psrc), [RFHM](#candidate-rfhm), [TMD](#candidate-tmd), [WBF](#candidate-wbf), [WS2](#candidate-ws2) |
| Nonlinear scattering | [FZZ-P](#fzz-p--parity-delay-mellin-orientation), [PW-B](#pw-b--recoildeninger-ward-transmutation) | [PTR](#candidate-ptr) |

Routes are alphabetical below. Candidate placement follows each candidate's primary open
problem. The family index is a navigation aid, not an exhaustive dependency graph.

<a id="c1--class-space-quotient-and-global-weil-positivity"></a>

### C1 — class-space quotient and global Weil positivity

- **Closed:** Lower prime--Gamma Cauchy atoms are total in the regular Xi--Weil core, and any four target vectors now admit simultaneous finite literal-source approximants preserving all 16 mixed Gram entries. Positive prime-faithful nuclear-root incidence still cannot majorize nonneutral Route-N projective leakage, even when distributed injectively over all four retained labels.
- **Open:** Prove a source-faithful sign/coercivity law for the limiting four-channel Gram carrier, outside the excluded positive nuclear-root ideal. Finite-source reachability and mixed-term retention close occurrence, not reflected-diagonal positivity or the cofinal Weil inequality.
- **Evidence:** [Four-channel finite Gram approximation](../../../../formal/GaloisForLFunctions/RHTower/DeningerPrimeGammaLowerCauchyFiniteGramApproximation.lean), [projective-leakage no-go](../../../../formal/GaloisForLFunctions/RHTower/GammaSewnPluckerRouteNProjectiveLeakageNoGo.lean), [fact audit](p-c1-four-channel-cauchy-own-research-facts.md); [earlier architecture](rh-frontier-reference-2026-09-12.md#source-line-724).

<a id="ccm-fu--completed-current-and-fixed-aperture-suzuki-checkpoint"></a>

### CCM-FU — completed current and fixed-aperture Suzuki checkpoint

- **Closed:** Fresh-prime processing copies each old core coordinate by `sqrt(p)` and adds one `p`-free background; its post-processing square retains the exact signed cross term, so the source target is now coordinatewise explicit. The complete moving prime--polar action is one signed delayed-charge transform, every fixed-wall quantile increment is nonnegative, the physical polar bulk is monotone on `[7,H-3]`, and one marked prime has enough literal polar capacity inside radius `ceil(2 log p)`. On the divisor-clock side, every finite core admits prescribed sufficiently large prime extensions that pay an entire fixed multiplicative clock block with a positive `c log M` margin.
- **Open:** Globalize these local producers: choose an exhaustive prime/clock schedule that pays the least omitted/current debt before its threshold, controls overlapping prime--polar intervals and both boundary collars, and bounds the single signed delayed-charge transform. Arbitrary cutoff schedules have unbounded logarithmic first-cell cost, while bounded-quotient helper windows cannot repay inherited debt; a successful schedule must use deep child fields with uniform changing-core constants.
- **Evidence:** [Coordinate target](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorOrientedPrimeDilationRenormalization.lean), [delayed-charge transport](../../../../formal/GaloisForLFunctions/RHTower/CCMFUSuzukiCriticalDelayedChargeTransport.lean), [log-scale polar capacity](../../../../formal/GaloisForLFunctions/RHTower/CCMFUSuzukiCriticalLogScalePrimePolarCapacity.lean), [finite clock-block payment](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorPrescribedClockBlock.lean), [clock-growth boundary](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorFiniteClockCutoffGrowth.lean), [current-clock depth](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorCurrentClockDepth.lean), [schedule audit](rh-coupled-clock-schedule-facts.md).

<a id="cdc--constitutive-dagger-confluence"></a>

### CDC — constitutive dagger confluence

- **Closed:** Canonical pre-divisor potential, calibrated mate gain and exact wall-classifying confluence/proof-erasure receivers.
- **Open:** Derive semantic descent or three-slot proof erasure on every closed Xi-error fibre from the literal arithmetic source.
- **Evidence:** [Architecture, precise hypotheses and source references](rh-frontier-reference-2026-09-12.md#source-line-742).

<a id="clgttf--completed-theta-bezoutian-no-escape"></a>

### CLG/TTF — completed theta Bezoutian no-escape

- **Closed:** Theta Bezoutian/Krein incidence, separated-tail positivity, global native D1, low-rank center-mixed sections and uniform small-cluster results. For the even compact polynomial-ODE bridge, determinant coefficients are formal at degrees `0–7` and `12–20`; all seven degree-eight cofactor terms now have source proofs, removing the slice-seven cofactor boundary.
- **Open:** Assemble those seven terms into the degree-eight coefficient identity, close coefficients `9–11`, and prove final polynomial extensionality. Then prove compact inner/middle comparison and general-packet/all-order source orientation. Cofactor closure alone does not establish rank-seven or global positivity.
- **Evidence:** [Degree-eight term 0](../../../../formal/GaloisForLFunctions/HTGeometry/PolynomialODEEvenCompactGapCofactorTerm0Slice8.lean), [degree-eight term 6](../../../../formal/GaloisForLFunctions/HTGeometry/PolynomialODEEvenCompactGapCofactorTerm6Slice8.lean), [higher cofactor normalizer](../../../../formal/GaloisForLFunctions/HTGeometry/PolynomialODEEvenCompactGapCofactorHigherNormalizer.lean); [earlier architecture](rh-frontier-reference-2026-09-12.md#source-line-1417).

<a id="csb--cofinal-bernstein-sourcetarget-comparison"></a>

### CSB — cofinal Bernstein source/target comparison

- **Closed:** Finite Bernstein/moment machinery, source-certified rectangle and centered-order improvement; exact thin-collar RH receivers.
- **Open:** Produce cofinal degrees/apertures with a source-derived bounded or subexponential source/target discrepancy.
- **Evidence:** [Architecture, precise hypotheses and source references](rh-frontier-reference-2026-09-12.md#source-line-856).

<a id="d2--continued-primearchimedean-free-sector-passivity"></a>

### D2 — continued prime–archimedean free-sector passivity

- **Closed:** Hermitian finite KMS entropy-production stages have the completed source's odd/negative-conjugation parity and zero real response at `i/4`, but their normalized positive-imaginary slope is nonpositive. The unique correction from universal squarefree incidence to the completed prime--polar--Gamma source has a nonremovable centered-clock singularity and cannot be supplied by an independently passive finite KMS channel. If a scalar passive-minus-universal cancellation converges anyway, it is already an RH premise.
- **Open:** Prove D2's genuinely infinite source lower bound above the critical depth envelope using cancellation retained before scalar passive-response formation. Any Q handoff must also orient the oblique complex phase; parity compatibility and a real-part estimate are insufficient.
- **Evidence:** [Parity bridge](../../../../formal/GaloisForLFunctions/RHTower/PrimeArchEntropyProductionParityBridge.lean), [singular source completion](../../../../formal/GaloisForLFunctions/RHTower/MobiusIncidenceSourceCompletionSingularity.lean), [passive-completion no-go](../../../../formal/GaloisForLFunctions/RHTower/MobiusIncidencePassiveCompletionNoGo.lean), [scalar capstone](../../../../formal/GaloisForLFunctions/RHTower/MobiusKMSScalarCancellationCapstone.lean).

<a id="e--squarefree-wold-transport"></a>

### E — squarefree Wold transport

- **Closed:** Gamma--Hankel energy is now an exact nonnegative weighted square sum of literal Möbius renewal packets, so diagonalization is no longer missing. Every normalized sharp cofactor has a canonical centered norm-`≤1` source contraction. Two proposed global combinatorial shortcuts are closed: a complete opposite-parity replica cell is coprime-compatible only when at most one prime component varies, and every nonempty coprime Kloosterman collision fibre has exactly two same-oriented representatives, making the factor-two collision bound sharp.
- **Open:** Prove a cofinal bound for the aggregate moving packet-square mass in `1 < r ≤ 2`, or build a sparse coprime-compatible recurrence with its own load/seam bounds and the required twisted fourth-moment saving. The centered contraction still needs a source-faithful Fisher one-corner identification and recurrence transport; full-cell parity and collision multiplicity supply no cancellation.
- **Evidence:** [Packet energy identity](../../../../formal/GaloisForLFunctions/RHTower/MobiusRenewalPacketEnergy.lean), [centered cofactor contraction](../../../../formal/GaloisForLFunctions/RHTower/RouteECenteredCofactorContraction.lean), [complete-cell no-go](../../../../formal/GaloisForLFunctions/RHTower/RouteEReplicaCoprimeCompleteCellNoGo.lean), [collision orientation](../../../../formal/GaloisForLFunctions/RHTower/Sieve/KloostermanGlobalCollisionOrientation.lean).

<a id="fzz-p--parity-delay-mellin-orientation"></a>

### FZZ-P — parity-delay Mellin orientation

- **Closed:** Every finite ordered depth source decomposes exactly into anti-Hermitian kernel pairing plus exchange-order defect; on exchange-stable support, Hermitian kernels are blind. The completed higher-screening two-puncture source is real and reflection-symmetric, so finite exchange-stable integration and the joint all-depth natural screening sum have zero orientation. The two external-BRST neutral branch chambers carry opposite currents `±(2πip)⁻¹`; their unordered sum vanishes exactly. Branch incidence or neutral symmetrization therefore supplies no orientation.
- **Open:** Derive the full integrated mixed replica--momentum Ward identity on a physical non-exchange-stable ordered domain, or derive a genuinely anti-Hermitian source kernel, while fixing the still-separate phase frame, normalization, screening and counterterms. Ordered algebra alone does not identify the worldsheet producer.
- **Evidence:** [Ordered source law](../../../../formal/GaloisForLFunctions/RHTower/FZZCigarParityCrossDepthOrderedSourceLaw.lean), [neutral symmetrization no-go](../../../../formal/GaloisForLFunctions/RHTower/FZZCigarParityExternalBRSTNeutralSymmetrizationNoGo.lean), [higher-screening ordered no-go](../../../../formal/GaloisForLFunctions/RHTower/FZZCigarHigherScreeningOrderedSourceNoGo.lean), [all-depth joint no-go](../../../../formal/GaloisForLFunctions/RHTower/FZZCigarHigherScreeningAllDepthJointNoGo.lean), [source audit](fzz-p-rbh-pw-b-ptr-source-facts.md).

<a id="g--ward-orientation"></a>

### G — Ward orientation

- **Closed:** Walsh marking removes all inter-cell interference before realification. The two literal lower-half Cauchy rectangles are now proved to carry exactly one common finite strict-right Xi packet and its Schwarz mates, closing the finite packet-identification premise in the local annulus weld.
- **Open:** Construct a cofinal family of boundary-admissible moving rectangles and prove source integrability uniformly in that family, strong enough to orient and bound the literal narrow-line annulus energy. Finite packet equality and Walsh diagonalization do not supply this global estimate.
- **Evidence:** [Lower-half packet geometry](../../../../formal/GaloisForLFunctions/RHTower/XiWardLowerHalfSourcePacketGeometry.lean), [Walsh source producer](../../../../formal/GaloisForLFunctions/RHTower/XiWardWalshSourceProducer.lean), [fact audit](g-own-research-facts.md).

<a id="hc--horizontal-collision-charge"></a>

### HC — horizontal collision charge

- **Closed:** The thin Poincaré--Lelong source slice lands cutoff-independently on the exact horizontal collision charge, but as a nonnegative same-height multiplicity sum. On every finite swap-stable unlabelled pair carrier, the signed displacement sums to zero, while squared displacement survives and equals twice the strictly oriented half.
- **Open:** Construct a singular/unbounded source-to-Gauss--Hodge comparison retaining an external label, non-swap-stable domain or other genuine exchange-breaking datum before scalarization and the cofinal limit.
- **Evidence:** [Exchange-orientation no-go](../../../../formal/GaloisForLFunctions/RHTower/XiHorizontalCollisionExchangeOrientationNoGo.lean), [fact audit](routes-e-p-u-q-c1-d2-l-own-research-facts.md).

<a id="l--singular-greenbv-to-physical-descent"></a>

### L — singular Green/BV-to-physical descent

- **Closed:** Every native original-Green coordinate now has its forced twice-multiplicity normalization and a nonzero product-topology zero-damping limit retaining the literal prime source and both zeta jets. Fixed Gamma-six transport commutes with this coordinatewise completion, and its limiting reader coordinate vanishes exactly on the critical line.
- **Open:** Construct the actual zero-damping Green/BV source-domain object and a normed or otherwise source-faithful completion, then prove simultaneous all-coordinate reader vanishing. Product convergence removes scalar-normalization and reader-mismatch obstructions but supplies no global vanishing law.
- **Evidence:** [Coordinatewise original-Green completion](../../../../formal/GaloisForLFunctions/RHTower/DeningerOriginalGreenCoordinateCompletion.lean), [fact audit](l-original-green-coordinate-completion-own-research-facts.md); [earlier architecture](rh-frontier-reference-2026-09-12.md#source-line-890).

<a id="li--finite-paired-li-prime--gamma-order"></a>

### LI — finite paired-Li prime--Gamma order

- **Closed:** Finite paired-Li prime–Gamma identities, mode clocks, critical transfer and reciprocal-scale generating-law reduction.
- **Open:** Prove source-derived complex singularity-support/continuation orientation strong enough for coefficientwise zero-exclusion. Keep the complete complex pole/node structure.
- **Evidence:** [Architecture, precise hypotheses and source references](rh-frontier-reference-2026-09-12.md#source-line-2182).

<a id="msc--möbius--sonin-affine-critical-boundary-renormalization"></a>

### MSC — Möbius--Sonin affine critical-boundary renormalization

- **Closed:** The unique moving real power preserving source mass at safe base `sigma>1` is `r=sigma-Re rho`; it gives an exact norm-one `ell²` column but shifts the divisor to the zero-free point `sigma+i Im rho`. No real power can preserve both source mass and the original divisor target, closing the complete diagonal real-power rigging branch.
- **Open:** Carry safe-chamber order through a genuinely non-diagonal, non-power singular transport that retains the conormal residue and original divisor target.
- **Evidence:** [Threshold-tracked rigging](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmGammaSewnSquarefreeFisherThresholdTrackedRigging.lean), [fact audit](msc-threshold-tracked-own-research-facts.md).

<a id="o--restricted-weil-ground-and-genus-lag-order"></a>

### O — restricted-Weil ground and genus-lag order

- **Closed:** The canonical ground equation gives the exact numerical-range identity `Re ⟪D u,u⟫ = E‖Ju‖² − ‖u‖²` for the literal compressed scalar--polar--prime remainder. Thus the sharp wall `Re ⟪D u,u⟫ ≥ −‖u‖²` is exactly nonnegative restricted-Weil ground energy, and its cofinal finite-head epsilon relaxation is RH-equivalent. This replaces the unnecessarily strong norm-contraction target. Fixed affine/common-clock repairs remain closed, and finite matched wall-light third jets plus the complete parabolic cross kernel factor through only three/four source moments, so neither is coercive.
- **Open:** Prove the signed numerical-range lower wall directly from the von Mangoldt source, with arbitrarily small cofinal slack. Any successful carrier must escape the finite moment null spaces and control the already-admitted joint block rather than fit endpoint, common-clock or low-rank local jets.
- **Evidence:** [Canonical numerical range](../../../../formal/GaloisForLFunctions/RHTower/CCMRestrictedWeilCanonicalGroundRemainderNumericalRange.lean), [third-jet no-go](../../../../formal/GaloisForLFunctions/RHTower/CCMActualHeadMatchedWallLightThirdJetCoercivityNoGo.lean), [four-moment factorization](../../../../formal/GaloisForLFunctions/RHTower/CCMActualHeadMatchedQuantilePolarParabolicCrossKernelRankFactorization.lean), [route audit](route-o-whole-connes-closure-audit.md).

<a id="p--paired-primegamma-signed-exterior-wall"></a>

### P — paired prime–Gamma signed exterior wall

- **Closed:** Finite reporters, both ordered Julia legs and the separate flat terminal orbit are source-realized. Finite Lorentz graph dissipation has exactly one active radical: matched--quantile displacement constant on the head. That relative-offset shear is invisible to every centered strict-cross kernel but remains linearly visible to the terminal-facing Riesz readout as `-delta₂·mass·(sqrt(M)+centeredShift K)`.
- **Open:** Prove cofinal avoidance or controlled crossing of the terminal coefficient's zero set while intertwining the radical readout with the independent terminal connection on one unbounded graph domain. No bound or fixed sign for `sqrt(M)+centeredShift K` is available.
- **Evidence:** [Lorentz graph radical](../../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePLorentzGraphKernel.lean), [terminal parabolic connection](../../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePTerminalParabolicConnection.lean), [fact audit](p-sp-e-translation-gauge-own-research-facts.md).

<a id="pw-b--recoildeninger-ward-transmutation"></a>

### PW-B — recoil/Deninger Ward transmutation

- **Closed:** The literal Peierls rates realize both PW spectral edge labels at every natural grade. Full two-branch CTP completion is exactly reflection odd, and the even cross-branch coordinate determines every closed recoil holonomy. Finite or summable-countable positive atomic seams, a single singular endpoint scale, scalar two-emission coherence and common scalar contact transmutation are all excluded; none can supply the required relative coefficient.
- **Open:** Derive one field-valued cap/lift-defect law identifying normalized odd CTP magnitude with a nonzero positive multiple of fixed-grade PW imbalance, while retaining reciprocal support, finite-energy contacts and Xi occurrence. Spectral labels and parity are closed; magnitude transmutation remains open.
- **Evidence:** [Spectral bridge](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekLiteralPeierlsSpectralBridge.lean), [cross-branch holonomy](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekCrossBranchHolonomyBridge.lean), [positive atomic no-go](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekCountablePositiveAtomicSeamNoGo.lean), [scalar-contact no-go](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekForcedContactScalarTransmutationNoGo.lean), [source audit](fzz-p-rbh-pw-b-ptr-source-facts.md).

<a id="q--exterior-paired-value-passivity"></a>

### Q — exterior paired-value passivity

- **Closed:** The central line-conjugate algebra is now separated from a committed source barrier. Unconditional off-line ordinate separation plus the order-23 orientation corridor gives nonnegative response for every paired reciprocal-square atom, and absolute line-conjugate summation transfers this to the actual continued prime--Gamma trace throughout `0 < Re z ≤ 218/25`, `0 < Im z < 1/2`, away from a zeta zero/pole. Q remains an oblique complex-flux observable, so a D2 real-part bound alone still cannot imply passivity.
- **Open:** Extend the atomwise/source-trace barrier beyond `218/25` cofinally across the full pole-free upper strip, or produce a pole witness. The remaining source law must orient complex phase, not only real flux.
- **Evidence:** [Central algebra](../../../../formal/GaloisForLFunctions/RHTower/PrimeArchCentralPairedDiagonalAlgebra.lean), [source barrier](../../../../formal/GaloisForLFunctions/RHTower/PrimeArchCentralPairedDiagonalSourceBarrier.lean), [continued trace sign](../../../../formal/GaloisForLFunctions/RHTower/PrimeArchCentralPairedTrace.lean), [D2--Q oblique flux](../../../../formal/GaloisForLFunctions/RHTower/PrimeArchD2QObliqueFlux.lean).

<a id="rg--gaussian-arithmetic-and-suzuki-transport-positivity"></a>

### RG — Gaussian arithmetic and Suzuki transport positivity

- **Closed:** Real-node representative ambiguity and the finite eta-flux RH receiver remain closed. Every compact center-minimum Gaussian certificate reaching the phase flip `pi/epsilon` must now pay an explicit elementary peak through the bounded digamma channel plus retained prime slope mass; the latter is bounded by the deterministic budget `cutoff·log(cutoff)^2`, yielding an explicit necessary cutoff-growth law.
- **Open:** Produce certificates with that growing prime budget uniformly in center and width, or prove the finite eta flux tends to zero from an independent arithmetic anti-alignment estimate. The phase-flip law quantifies unavoidable cost; it does not construct good widths or signed seam control.
- **Evidence:** [Phase-flip peak](../../../../formal/GaloisForLFunctions/RHTower/RiemannGaussian/GaussianCertificatePeakObstruction.lean), [digamma bound](../../../../formal/GaloisForLFunctions/RHTower/RiemannGaussian/GaussianCertificatePhaseFlipDigammaBound.lean), [cutoff budget](../../../../formal/GaloisForLFunctions/RHTower/RiemannGaussian/GaussianCertificatePhaseFlipCutoffBudget.lean), [finite arithmetic flux criterion](../../../../formal/GaloisForLFunctions/RHTower/RiemannGaussian/RiemannXiSuzukiPositiveCriticalStripEtaFiniteArithmeticFluxCriterion.lean).

<a id="sp-e--signed-prime-dilation-versus-continuum"></a>

### SP-E — signed prime dilation versus continuum

- **Closed:** Prime-power history is exactly orientation ledger plus displacement debt and is invariant under common-centroid gauge. The finite Lorentz graph is positive definite modulo one relative-offset shear; on that radical every cross-kernel entry and centered charge vanish, while the Riesz terminal readout has the explicit nonzero-coefficient alternative recorded in Route P.
- **Open:** Prove a cofinal nonlocal prime--polar--Gamma estimate controlling graph resistance and the relative-offset readout together with the independent terminal orbit. Finite graph coercivity only controls the quotient and cannot bound the surviving shear coefficient.
- **Evidence:** [History ledger](../../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszPrimePowerHistoryLedger.lean), [Lorentz graph kernel](../../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePLorentzGraphKernel.lean), [fact audit](p-sp-e-translation-gauge-own-research-facts.md).

<a id="stc--exterior-sonin-seam-coherence"></a>

### STC — exterior Sonin seam coherence

- **Closed:** Exterior coherence endpoint and a target-free fixed-prime Gamma-six/Sonin lift with exact Calkin bounds.
- **Open:** Identify or construct the canonical all-prime seam from source, then prove its cofinal sub-root Calkin growth law.
- **Evidence:** [Architecture, precise hypotheses and source references](rh-frontier-reference-2026-09-12.md#source-line-846).

<a id="sv2--suzuki-projective-limit-and-shifted-kernel-inertia"></a>

### SV2 — Suzuki projective limit and shifted-kernel inertia

- **Closed:** Prime endpoint square-root scale cancels exactly into a fixed Laplace main term plus explicit Binet error, and the error aggregates against the literal von Mangoldt source. The completed wall has a single anchored signed-source normal form. Fixed pairs and every fixed finite causal-depth Frostman head recur arbitrarily close to the central cap, so no finite head gives an eventual coercive wall. Any correction making the transition-core Ward defect semibounded must asymptotically cancel all of its linear positive core; fixed fractional under-compensation is impossible.
- **Open:** Control the signed residual after near-total atomic--continuous cancellation for the moving infinite head. This requires cofinal normalized shell/drift/metric control or another source-derived infinite-prime law; endpoint asymptotics, finite-head enlargement and a merely linear correction cannot orient it.
- **Evidence:** [Endpoint cancellation](../../../../formal/GaloisForLFunctions/RHTower/SuzukiEndpointPrimeRegularCancellation.lean), [anchored source normal form](../../../../formal/GaloisForLFunctions/RHTower/SuzukiGammaCompletedWallAnchoredSourceNormalForm.lean), [finite-head recurrence](../../../../formal/GaloisForLFunctions/RHTower/SuzukiCausalDepthFiniteHeadRecurrenceNoGo.lean), [asymptotic saturation](../../../../formal/GaloisForLFunctions/RHTower/SuzukiTransitionCoreAsymptoticSaturation.lean).

<a id="t1--theta-tail-core-current"></a>

### T1 — theta-tail core current

- **Closed:** Stationary-phase polarity and the persistence of the anti-ordered saddle remain exact. Swapping the two frequency--rapidity legs now gives `star C(t,s)=C(s,t)`: the finite covariance is Hermitian, not alternating, so exchange produces a real part rather than an identity-level cancellation.
- **Open:** Prove signed nonlocal prime-frequency cancellation for that remaining real covariance, or derive source order support excluding anti-ordered saddles. Exchange symmetry, local stationary phase and diagonal localization cannot do it.
- **Evidence:** [Hermitian exchange](../../../../formal/GaloisForLFunctions/RHTower/XiMassTwoRapidityHermitianExchange.lean), [saddle polarity](../../../../formal/GaloisForLFunctions/RHTower/XiMassTwoRapiditySaddlePolarity.lean), [fact audit](routes-e-p-u-q-c1-d2-l-own-research-facts.md).

<a id="t2--natural-abel-singular-wold-divisor"></a>

### T2 — natural-Abel singular Wold divisor

- **Closed:** The Wold current is exactly a cubic four-shift of a joint-depth Möbius source. All non-head dilates and the `r≥2` tail are holomorphic; Möbius--valuation duality identifies the tail as negative higher valuation. But the normal source transport is exactly the known prime-log/Wold divisor carrier and retains every strict-right residue. Chebyshev mirroring is the same full divisor current, not a second comparison; a strict-right zero also forces a nonzero noncompact cofinal compensator.
- **Open:** Derive an independent source law excluding that compensator, or a genuinely different singular comparison. Normal Möbius reorganization and Chebyshev divisor mirroring cannot provide it. The finite Hamilton--Jacobi seam noncancellation composition remains paper-only.
- **Evidence:** [Joint-depth Möbius transport](../../../../formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldJointDepthMöbiusSourceTransport.lean), [Chebyshev divisor mirror](../../../../formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldChebyshevDivisorMirror.lean), [fact audit](route-t-saddle-polarity-facts.md).

<a id="u--adaptive-shifted-xi-hankel-frontier-renewal"></a>

### U — adaptive shifted-Xi Hankel frontier renewal

- **Closed:** Adaptive terminal frontiers, contact/residue pricing, parabolic confinement and fixed-degree positivity remain exact. Literal completed arithmetic sources now pay every finite consecutive history of adjacent admission costs, including the positive cross-degree reserve that remains when logarithmic velocity vanishes.
- **Open:** Prove a source-history lower bound or non-summability/rate law strong enough to forbid sparse quadratic frontier escape. The finite budget is an upper accounting identity, not degree-uniform coercivity.
- **Evidence:** [Adjacent-history budget](../../../../formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionAdjacentHistoryBudget.lean); [earlier architecture](rh-frontier-reference-2026-09-12.md#source-line-2156).

## Route candidates

These have a source fragment, receiver or proposed interface, but lack the handoff,
exhaustion or independent source theorem needed for a complete live architecture.
Some are alternative presentations of an active route's existing open problem.

### Find a candidate

[AKC](#candidate-akc) · [APF](#candidate-apf) · [BPC](#candidate-bpc) · [BSH](#candidate-bsh) · [CTF](#candidate-ctf) · [EDQ](#candidate-edq) · [EGC](#candidate-egc) · [EWJ](#candidate-ewj) · [FEL](#candidate-fel) · [GTA](#candidate-gta) · [HCF](#candidate-hcf) · [HDL](#candidate-hdl) · [HJ](#candidate-hj) · [IRK](#candidate-irk) · [JAS](#candidate-jas) · [K-RVM](#candidate-k-rvm) · [MPLF](#candidate-mplf) · [PBM](#candidate-pbm) · [PCS](#candidate-pcs) · [PMP/LPC](#candidate-pmplpc) · [PSRC](#candidate-psrc) · [PTR](#candidate-ptr) · [RFHM](#candidate-rfhm) · [RG-ETA](#candidate-rg-eta) · [RG-HF](#candidate-rg-hf) · [RHist](#candidate-rhist) · [S6F](#candidate-s6f) · [SC](#candidate-sc) · [SEC](#candidate-sec) · [SQB](#candidate-sqb) · [TCD](#candidate-tcd) · [TK](#candidate-tk) · [TMD](#candidate-tmd) · [UEB](#candidate-ueb) · [W1C](#candidate-w1c) · [WBF](#candidate-wbf) · [WS2](#candidate-ws2)

<a id="candidate-akc"></a>

### AKC

- **Closed / available:** Arakelov/Jacobi/Siegel reduction, finite-cusp and short-vector geometry; faithful finite integral Frobenius carriers excluded.
- **Open:** Construct an admissible changed source action/lattice and centered determinant control without reintroducing integral conjugate packets.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-akc).

<a id="candidate-apf"></a>

### APF

- **Closed / available:** Arithmetic paired Fredholm index, source winding/trace and completed-K1 finite-ancestor classification.
- **Open:** Annihilate every source trace Fourier coefficient and prove zero-independent divisor exhaustion; completion cannot create missing charge.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-apf).

<a id="candidate-bpc"></a>

### BPC

- **Closed / available:** Bernstein–Pringsheim collar-susceptibility interface.
- **Open:** Continue the source susceptibility analytically through the critical collar.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-bpc).

<a id="candidate-bsh"></a>

### BSH

- **Closed / available:** Mate curvature is exactly character curvature times `‖y(j+1)‖²` plus a boundary-ideal multiple, so boundary-multiplier vanishing would force unitary character norm. But explicit reciprocal contraction sections are off-unitary: Boolean full-history contraction, its energy law and either one-sided Sonin contraction cannot prove the mate identity. Ordinary norm/seminorm-closed finite-cut completions also retain the cofinal Gamma defect and cannot manufacture the needed pre-closure factorization.
- **Open:** Construct the literal prime--Gamma section with a source-level mate identity before closure, or use a stronger nonordinary completion retaining the missing factorization.
- **Evidence:** [BSH fact audit](bsh-own-research-facts.md), [earlier mechanism](rh-frontier-reference-2026-09-12.md#candidate-bsh).

<a id="candidate-ctf"></a>

### CTF

- **Closed / available:** Sparse cubic Gamma--zeta occurrence, harmonic-charge removal and critical-scale source floors. Bose response is continuous under bounded tail-`L¹` convergence, so no uniformly bounded moving tail can converge in tail `L¹` while repairing the critical response on `[1,2]`.
- **Open:** Construct a genuinely noncompact moving array outside fixed bounded-tail `L¹` compactness, or prove an all-grade source orientation law.
- **Evidence:** [Tail-`L¹` no-go](../../../../formal/GaloisForLFunctions/RHTower/ChronologicalTailL1StabilityNoGo.lean), [fact audit](ctf-l1-stability-own-research-facts.md).

<a id="candidate-edq"></a>

### EDQ

- **Closed / available:** Residue innovations converge strongly, while predictable drift cannot converge strongly or be exponent-two uniformly integrable. Terminal beta transport is sign-preserving and residual-period geometry collapses to one coefficient. New support theorems sharpen the live upper-half carrier exactly to ordinary primes `p in [l+2,N]`: non-prime terminal successors, old-prime composites and the singleton residual vanish. Literal child energy samples only one clock span, shorter than each surviving prime's full phase cycle, so complete-period averaging is unavailable.
- **Open:** Bound the resulting incomplete prime-orbit reduced-residue covariance cofinally and sum the quotient tail by a genuinely non-uniformly-integrable signed argument. Prime support removes composite noise but supplies no prime-pair cancellation.
- **Evidence:** [Terminal prime support](../../../../formal/GaloisForLFunctions/RHTower/EulerDeletionTerminalPrimeSupport.lean), [future-prime support](../../../../formal/GaloisForLFunctions/RHTower/EulerDeletionReverseTailFuturePrimeSupport.lean), [upper-half physical collapse](../../../../formal/GaloisForLFunctions/RHTower/EulerDeletionUpperHalfPhysicalPrimeSupport.lean), [fact audit](routes-e-p-u-q-c1-d2-l-own-research-facts.md).

<a id="candidate-egc"></a>

### EGC

- **Closed / available:** When both prescribed Cauchy poles lie outside an admissible inner rectangle, the normalized continued prime--archimedean contour is exactly the finite Xi multiplicity-copy Cauchy row. The complementary crossing regime's three-pole residue signs are fixed.
- **Open:** Add the outer shifted-pole corrections and prove normalized covariance vanishes along a nested pole-safe cofinal contour family.
- **Evidence:** [Pole-safe inner landing](../../../../formal/GaloisForLFunctions/RHTower/XiMeromorphicCauchyPairSourceLanding.lean), [fact audit](egc-cauchy-inner-landing-own-research-facts.md).

<a id="candidate-ewj"></a>

### EWJ

- **Closed / available:** Prime/depth-faithful Euler/Wold third jets, independent grade transport and feasible residual energy budgets.
- **Open:** Derive zero-independent physical admission/order and divisor exhaustion before selecting an Xi copy.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-ewj).

<a id="candidate-fel"></a>

### FEL

- **Closed / available:** Actual theta probability/Xi occurrence and explicit likelihood-contrast, recovery and reflection-gap laws.
- **Open:** Derive zero-to-contrast balance from source dynamics. Shares one family with PMP/LPC.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-fel).

<a id="candidate-gta"></a>

### GTA

- **Closed / available:** Actual-stage Schur charge receiver, persistent nonnormality and a one-hyperbolic-plane limiting source component.
- **Open:** Control transverse spectral energy relative to that component or justify source-relative subtraction. Full-defect decay is impossible.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-gta).

<a id="candidate-hcf"></a>

### HCF

- **Closed / available:** Horizontal scanning is blind, while transverse scanning sees residue `m/pi` and gives the exact vertical `L²` RH receiver. The archimedean height-two increment is now `O(1/|t|)`, and the literal safe-line completed source increment `Delta₂J(t)` is uniformly bounded; its square has `O(T)` window cost. This closes the Gamma tail and supplies a concrete finite positive four-leg input.
- **Open:** Continue a positive interval family of those squares to the transverse divisor while preventing equal-multiplicity pole cancellation. One fixed height-two difference can cancel separated equal poles and is not a producer.
- **Evidence:** [Vertical Gamma tail](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmCriticalFeatureVerticalGammaTail.lean), [bounded source increment](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmCriticalFeatureVerticalSourceIncrement.lean), [fact audit](routes-e-p-u-q-c1-d2-l-own-research-facts.md).

<a id="candidate-hdl"></a>

### HDL

- **Closed / available:** Prime-normal half-density, double-log residue and adaptive Green codiagonal are welded exactly to directed source-horizontal KL chirality and equality of frozen Hodge versus adaptive Jeffreys source work. All-copy source-work equality is equivalent to RH, so the four apparent endpoints are one receiver.
- **Open:** Derive either source equality before divisor specialization through a singular/noncontinuous or quotient differential retaining provenance. The weld adds no annihilation producer.
- **Evidence:** [Adaptive source-chirality weld](../../../../formal/GaloisForLFunctions/RHTower/MobiusThetaAdaptiveGreenSourceChiralityWeld.lean).

<a id="candidate-hj"></a>

### HJ

- **Closed / available:** Hurwitz anchor-jet reflection interface. A normalized finite rational-Hurwitz fibre recovers every scale `n^s`; at modulus two its reflected value equality is exactly the first-prime seam condition and, on all Xi fibres, exactly RH.
- **Open:** Derive that finite reflected-value equality from an arithmetic source law. The finite-value chain is an exact receiver, not a producer.
- **Evidence:** [Finite rational-fibre seam and RH equivalence](../../../../formal/GaloisForLFunctions/RHTower/XiHurwitzRationalFiberSeam.lean); [earlier HJ architecture](rh-frontier-reference-2026-09-12.md#candidate-hj).

<a id="candidate-irk"></a>

### IRK

- **Closed / available:** Irrational-rotation projective module/K-zero interface.
- **Open:** Produce an arithmetic trace/Chern landing in the completed Xi endpoint.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-irk).

<a id="candidate-jas"></a>

### JAS

- **Closed / available:** Singular ancestry carrier, theta value landing, all-grade chain and source creators.
- **Open:** Change inverse covariance or literal creation before quotient landing while preserving the connecting class; multivaluedness alone cannot repair the no-go.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-jas).

<a id="candidate-k-rvm"></a>

### K-RVM

- **Closed / available:** Nonzero cubic trace excludes sign reversal not only by unitaries but by every bounded invertible similarity. Determinant-only exclusion of indefinite boundary completion is false: an explicit nonzero Pontryagin two-channel completion is metric-self-adjoint, cubic nilpotent and has determinant one at every finite scale.
- **Open:** Derive a source-faithful non-similarity boundary assembly whose global carrier is non-nilpotent, nonvanishing and has the Xi divisor. Bounded isospectral transport and scalar tail completion are closed; the hyperbolic finite survivor proves only feasibility.
- **Evidence:** [Bounded-similarity no-go](../../../../formal/GaloisForLFunctions/RHTower/PrimeIndexedRVMNonunitarySimilarityNoGo.lean), [Pontryagin survivor](../../../../formal/GaloisForLFunctions/RHTower/PrimeIndexedRVMPontryaginBoundarySurvivor.lean).

<a id="candidate-mplf"></a>

### MPLF

- **Closed / available:** Along every positive root-time sequence tending to zero, packet-uniform finite prime-Laplace Gram bounds exist exactly on the critical line. Thus the cofinal Gram statement is a sharp RH receiver. A bounded primewise or arbitrary bounded columnwise operator cannot undo positive forward raw-jet transport into shrinking Meixner root half-densities; the required gain diverges whenever `theta < 2a`.
- **Open:** Derive the cofinal Gram bounds directly from an arithmetic source without bounded forward recovery, or construct a source normalization/indefinite transport that survives the shrinking root scale.
- **Evidence:** [Cofinal Gram classification](../../../../formal/GaloisForLFunctions/RHTower/MeixnerRootPrimeLaplaceCofinalGramClassification.lean), [forward-bridge no-go](../../../../formal/GaloisForLFunctions/RHTower/MeixnerRootPrimeLaplaceForwardBridgeNoGo.lean).

<a id="candidate-pbm"></a>

### PBM

- **Closed / available:** Prime-boundary monodromy interface.
- **Open:** Derive source cancellation or absence of quantized monodromy at infinity.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-pbm).

<a id="candidate-pcs"></a>

### PCS

- **Closed / available:** Explicit singular co-shift complex and exact wall-classifying ground obstruction.
- **Open:** Annihilate the class from source without erasing the forward mode; break co-shift covariance or change the incidence.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-pcs).

<a id="candidate-pmplpc"></a>

### PMP/LPC

- **Closed / available:** Explicit theta contrast/visibility, product fusion and tail-versus-vertical information decomposition.
- **Open:** Construct a source-predeclared cofinal Xi observation history and a balance law forcing contrast to vanish. Same likelihood family as FEL.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-pmplpc).

<a id="candidate-psrc"></a>

### PSRC

- **Closed / available:** Prime-shift singular residue-graph interface.
- **Open:** Prove source closability; bounded split descent is blind.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-psrc).

<a id="candidate-ptr"></a>

### PTR

- **Closed / available:** Prime clocks, parabolic two-slab Maxwell transfer, helical/OAM selection and three-port flow are exact. Four distinct locked OAM labels already occur at grades `0..3`, so no three-port readout is faithful. No spectral-label-blind function of the bare constitutive harmonic can reproduce the full conormal family: it would have to be both moderate on the critical line and non-moderate at `s=0`.
- **Open:** Derive an infinite OAM/sideband boundary map or a physical mode-folding law, retaining spectral-time data beyond bare helicity, then prove independent defect confinement. Finite ports and bare harmonic closure are terminal.
- **Evidence:** [Finite OAM-port no-go](../../../../formal/GaloisForLFunctions/RHTower/PhotonicFiniteOAMPortLadderNoGo.lean), [bare-harmonic no-go](../../../../formal/GaloisForLFunctions/RHTower/PhotonicBareHarmonicConormalNoGo.lean), [source audit](fzz-p-rbh-pw-b-ptr-source-facts.md).

<a id="candidate-rfhm"></a>

### RFHM

- **Closed / available:** Support/grade carrier and closed literal creators; reversible/source-linear sewing no-gos.
- **Open:** Break inverse covariance or replace literal creation while retaining phase, depth, compounds and a nonzero Xi connecting class.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-rfhm).

<a id="candidate-rg-eta"></a>

### RG-ETA

- **Closed / available:** Actual finite paired-eta arithmetic fluxes converge diagonally to the complete upper-spectral heat detector. Vanishing of this one explicit finite sequence is equivalent to RH; an off-axis zero forces eventual strict positivity. This closes the finite-to-complete interface and identifies the exact arithmetic target.
- **Open:** Prove that finite flux tends to zero by anti-alignment of the retained coupled prefix at square-root scale. Finite truncation or the criterion itself supplies no such source estimate. Subordinate to RG.
- **Evidence:** [Finite arithmetic flux criterion](../../../../formal/GaloisForLFunctions/RHTower/RiemannGaussian/RiemannXiSuzukiPositiveCriticalStripEtaFiniteArithmeticFluxCriterion.lean).

<a id="candidate-rg-hf"></a>

### RG-HF

- **Closed / available:** Finite Hardy approximants and exact reflection-resultant/phase-dispersion alternatives.
- **Open:** Prove source-pinned finite-to-entire rigidity excluding both alternatives. Subordinate to RG.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-rg-hf).

<a id="candidate-rhist"></a>

### RHist

- **Closed / available:** Source-history completion and affine Xi-residue landing remain exact. The normalized Big-Witt row is ambient-norm-dark while continuous positive observation forces price escape. Square-root rescaling does not repair this: the rows still tend to zero in the ambient carrier while their algebraic one-leg trace grows without bound, explicitly exhibiting the singular discontinuity required to see them.
- **Open:** Construct a divisor-independent vector-polarized history with a mathematically controlled singular/noncontinuous observation law and nonescaping reciprocal price, then exhaust Xi copies. Scalar positive repair, continuous finite-price observation and naive singular rescaling are closed.
- **Evidence:** [Big-Witt price escape](../../../../formal/GaloisForLFunctions/RHTower/DeningerBigWittCrossPrimeRHistPriceEscape.lean), [singular-rescaling no-go](../../../../formal/GaloisForLFunctions/RHTower/DeningerBigWittCrossPrimeRHistSingularRescalingNoGo.lean).

<a id="candidate-s6f"></a>

### S6F

- **Closed / available:** Literal sixth-jet source, strict D1/center mixture, order-eight connectors and small-cluster positivity. Generated ninth-order rational quadrature on the `1/64` mesh proves all five first-atom bounds required by the centered-order-24 sixth-trace closure; the resulting order-23 normalized prime--archimedean moment is now closed by a direct source theorem. The sixth reciprocal trace is also exactly one signed triple-product-kernel inequality, equivalently the third logarithmic coefficient of the normalized Xi square-coordinate jet.
- **Open:** Extend the source argument to every order or general-packet/cofinal incidence; a finite order-24 closure does not control the full jet hierarchy. Uniform signed product-kernel/log-coefficient inequalities are one concrete all-order target. The separate completed C5 slope remains open.
- **Evidence:** [Direct order-23 moment closure](../../../../formal/GaloisForLFunctions/RHTower/PrimeArchMomentTwentyThreeClosure.lean), [high-order source quadrature](../../../../formal/GaloisForLFunctions/RHTower/PrimeArchThetaFirstAtomHighOrderQuadrature.lean), [order-24 reduction](../../../../formal/GaloisForLFunctions/RHTower/XiCenteredOrderTwentyFourSixthTraceClosure.lean), [product-kernel/log-coefficient identity](../../../../formal/GaloisForLFunctions/RHTower/PrimeArchThetaThirdCumulantProductKernel.lean); [earlier architecture](rh-frontier-reference-2026-09-12.md#candidate-s6f).

<a id="candidate-sc"></a>

### SC

- **Closed / available:** Stokes/Witt descent and all-prime polarized Krein carrier; pointwise unmarked fibres are indistinguishable.
- **Open:** Find a source-fixed signed/indefinite restriction or cross-fibre invariant that preserves Xi landing without universal target fitting.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-sc).

<a id="candidate-sec"></a>

### SEC

- **Closed / available:** One-ended adjacent-prime seam interface.
- **Open:** Prove eventual source compactness of seam coboundaries.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-sec).

<a id="candidate-sqb"></a>

### SQB

- **Closed / available:** Reciprocal product grids now approximate the entire completed cuspidal form unit ball through one finite-dimensional cell-constant space. Bounded-core grid error and uniform cusp-tail contraction are spliced into total boundedness, giving compact inclusion of the completed cuspidal form domain. Its closed `L²` carrier and canonical self-adjoint Friedrichs operator are constructed, with compact resolvent at zero. Scalar height cutoffs preserving modular inversion are constant, so a nonzero compact modular cutoff must use non-scalar zero-mode transport or a boundary compensator.
- **Open:** Identify the canonical Friedrichs operator with the literal finite-deck Maass Laplacian on a dense smooth core, then prove spectral selection, Satake factorization and symmetric-power lifts. Rellich compactness and abstract compact resolvent are no longer open.
- **Evidence:** [Cuspidal Rellich](../../../../formal/GaloisForLFunctions/RHTower/MaassFiniteDeckCuspidalRellich.lean), [Friedrichs operator](../../../../formal/GaloisForLFunctions/RHTower/MaassFiniteDeckCuspidalFriedrichs.lean), [source identification target](../../../../formal/GaloisForLFunctions/RHTower/MaassFiniteDeckCuspidalFriedrichsSource.lean), [scalar-cutoff rigidity](../../../../formal/GaloisForLFunctions/RHTower/MaassFiniteDeckHorocycleCutoffRigidity.lean).

<a id="candidate-tcd"></a>

### TCD

- **Closed / available:** Literal theta convolution/full-jet connectors, global native D1 and small five-point cluster positivity.
- **Open:** Prove general-packet/cofinal source-to-divisor landing; D1 does not settle completed C5 orientation.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-tcd).

<a id="candidate-tk"></a>

### TK

- **Closed / available:** Thermodynamic/cooling limits reduce to D2's scalar defect.
- **Open:** Prove D2's prime-flux lower bound; changing ensembles supplies no independent gate.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-tk).

<a id="candidate-tmd"></a>

### TMD

- **Closed / available:** Integral formation-index, negative-tail primitive and compact-descent equivalences.
- **Open:** Derive source properness/continuity before Xi specialization. Global primitive existence is the RH endpoint, not the producer.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-tmd).

<a id="candidate-ueb"></a>

### UEB

- **Closed / available:** Translated Xi Bezoutian and all-depth source tangent of negative type.
- **Open:** Prove coefficient-faithful source-tangent landing with the required sign before divisor polarization.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-ueb).

<a id="candidate-w1c"></a>

### W1C

- **Closed / available:** Closed positive-ray weight-one Clifford operator.
- **Open:** Prove its arithmetic determinant/scattering occurrence identity.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-w1c).

<a id="candidate-wbf"></a>

### WBF

- **Closed / available:** Source-normal jet, prime-Poisson fracture and finite Hodge/energy laws.
- **Open:** Prove depth-uniform source-normal completion that annihilates the anomaly and lands in Xi.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-wbf).

<a id="candidate-ws2"></a>

### WS2

- **Closed / available:** Depth-two signed operator, sharp trace-class relocation and summable determinant anomaly.
- **Open:** Derive exact source spectral/determinant occurrence; trace-class proximity does not identify zeros.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-ws2).

## Killed routes and subroutes

A retirement concerns the specified producer and its hypotheses. Its surviving theorem may
still support another route. “Equivalent to RH” and “nonselective” mean the proposed shortcut
does not independently solve the problem; they do not mean its premise is false.

### Retired route labels

| Label | Why the original producer is closed | Surviving direction |
|---|---|---|
| A | Source-faithful phase transport is rigid; universal feasibility restates RH. | Phase/trace/resolvent and moment classifiers. |
| B | Required common unitary transport is incompatible with scaling/prolate parameters. | Relative graphs and boundary deformation. |
| C2/I | Finite width saturates its coordinate. | Cauchy/Hurwitz interfaces in Q. |
| D1 | Finite/local positivity does not orient the completed all-degree source. | D2 tail and Q exterior kernel. |
| F | Bounded/sublinear compact completion has wrong order or loses source/floor. | Principal, relative or singular assemblies. |
| G2 | Required relative-Volterra germ is RH-equivalent. | G's marked Ward boundary. |
| H | Even Taylor factorization erases orientation. | Relation-valued indefinite primitives. |
| HB | Group-independent scattering cannot constrain second-sheet poles, while the full PSL₂(ℤ) Hecke/Maass--Selberg producer loop yields only receivers or RH-equivalent premises. | Exact Eisenstein, resonant-state, pulse-layer and Peierls receiver infrastructure; see [HB retirement](rh-killed-routes.md#no-go-341). |
| J | Uniform unrenormalized energy budget fails. | A changed principal-relative source current; residual/bilinear laws survive. |
| K | Quadratic mechanism loses the marked source. | Changed infinite operator candidates K-RVM and WS2. |
| M | Required fixed cyclic reader is excluded; cofinal flatness restates RH. | Singular-reader and receiver geometry. |
| N | Response/contractivity/work conditions restate the endpoint. | Shared L/P/G receiver. |
| R | Intrinsic completion mechanisms do not produce vanishing of the formation index. | External source-marked completion problems in JAS/WBF/CDC/TMD. |
| IW | Global internal-model existence is the desired divisibility/RH premise. | Exact clock–shift divisibility classification. |
| AP | Stated completed-Xi pullback fails; surviving selectors restate RH. | Witt/sheaf/Galois geometry. |
| AF | Fixed convergent copywise certificates restate RH; nonneutral mass escapes. | Singular cusp or genuinely global charged source law. |
| SNR | Aperture can fit target height independently of source. | A source-native aperture invariant. |
| FD2 | Trace-faithful polarization cannot supply missing divisor orientation; full-defect decay fails. | Exact Xi occurrence, persistent nonnormality, and arithmetic Gauss staging without Xi landing. |
| RBH | Complementary/wall finite parts and separated-sign or passive production are blind or RH receivers. | A changed nonseparated, nonlinear or singular datum. |

[Exact results and survivors for original labels](rh-killed-routes.md#retired-labels) ·
[FD2 full verdict](rh-frontier-reference-2026-09-12.md#source-line-2869) ·
[RBH full verdict](rh-frontier-reference-2026-09-12.md#source-line-2311)

### Closed subroutes inside otherwise live families

The complete catalogue contains **all 388 named entries**, not a selected list. Each family
opens a name index followed by one structured result/survivor card per mechanism.
The 17 original-label records above are included in that total; FD2 and RBH also have
their longer architecture verdicts in the reference.

| Browse closed mechanisms | Entries |
|---|---:|
| [Retired original route labels](rh-killed-routes.md#retired-labels) | 17 |
| [CCM-FU: prime scheduling and current bounds](rh-killed-routes.md#ccm) | 30 |
| [E, EDQ, HCF, T1/T2 and LI: arithmetic cancellation](rh-killed-routes.md#arithmetic) | 47 |
| [HB, FZZ and PW: scattering and physical action](rh-killed-routes.md#scattering) | 79 |
| [Theta, Schur, spectral and positivity mechanisms](rh-killed-routes.md#theta) | 37 |
| [Singular descent, formation and completion](rh-killed-routes.md#completion) | 29 |
| [Ward, Suzuki, prime–Gamma and operator landing](rh-killed-routes.md#ward) | 57 |
| [Analytic roots, multiplicity and regularization](rh-killed-routes.md#roots) | 11 |
| [Other finite, scalar and source-blind selectors](rh-killed-routes.md#other) | 81 |

## Shared infrastructure and unlabelled continuation problems

These are not additional active-route labels. Their value is the exact problem they
remove—or expose—inside the named routes.

### Singular theta metric and differential-pencil interface

- **Closed:** The injective, non-bounded-below theta metric preserves the literal source-pencil kernel and hence the completed-Xi divisor. A rank-one monopole correction yields a closed unbounded differential pencil with the same kernels, and its Green defect is exactly one incoming minus one outgoing scalar port.
- **Killed shortcut:** The metric range is not closed, so the metric coordinate alone cannot provide the closed-graph topology required by an index-one dilation.
- **Still open:** Construct a genuinely new closed-graph coordinate and a source-derived index/capacity law for the two-port relation. Exact divisor retention and Green balance remain receiver infrastructure.
- **Evidence:** [Metric pencil](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmThetaMetricPencil.lean), [closed-graph barrier](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmThetaMetricClosedGraphBarrier.lean), [differential pencil](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmThetaSourceDifferentialPencil.lean), [two-port Green law](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmThetaSourceDifferentialGreen.lean).

<a id="hb--theta-cusp-hawking-causal-scattering"></a>

### HB receiver stack after route retirement

- **Closed:** The B2 bulk is now source-explicit: complementary causal branches have total clock `−6`; their product obeys a forced stream equation, its coexact covector is smooth/divergence-free, and every linearized Einstein component is explicit. Full cusp-subtracted forcing and weak response obey literal source reflection. The full Einstein current, master contact and contact-completed angular current are exactly CTP-skew, matching the ordered causal pairing; finite full-kernel Goursat transposition and advanced-source differentiation are also available. Off-line copies retain a nonzero lower-Weyl mixed cusp coefficient, so any boundary transport must remove a literal growing channel.
- **Killed producer:** Group-independent scattering cannot constrain second-sheet poles; the PSL₂(ℤ) arithmetic loop through Hecke positivity, Hecke--Maass--Selberg, Rankin--Selberg, Kuznetsov, Ward stationarity and Hardy/inner--outer formulations yields receivers or RH-equivalent premises. Coefficientwise B2 cancellation is false at Hardy's on-line zeros. HB is therefore retired as an RH route.
- **Still open, receiver-side only:** Prove the complete noncompact ordered two-event functional equals the complementary incoming Einstein current while retaining the explicit full-minus-native lift defect and Weyl finite part. Then identify cap/contact transport at the noncompact boundary. These may complete the physical model but do not restore an independent arithmetic producer.
- **Evidence:** [Ordered physical current](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMLiteralCyclicPeierlsOrderedCurrent.lean), [cross-branch bidegree](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMLiteralCyclicPeierlsCrossBranchBidegree.lean), [source reflection](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFullAngularSourceReflection.lean), [self-mixed cusp flux](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMLiteralCyclicPeierlsSelfMixedCuspFlux.lean), [source audit](fzz-p-rbh-pw-b-ptr-source-facts.md).

### Off-line first moment and large-value selection

- **Closed:** The product approximate-functional-equation chain proves the multiplicity-weighted horizontal displacement is `O(T)`. The committed Lamzouri layer now formalizes finite multiplicity/collision inequalities, simple-or-selected counts, affine pair-correlation minorants, finite Xi/Dirichlet/Satake/window count transports, and the unconditional Montgomery--Taylor `67.25%` simple-critical and `83.62%` distinct-zero lower densities in the native Xi census. Factorized large-value resonance still excludes unrestricted square-root cancellation on selected large-value sets.
- **Open:** Improve `O(T)` to `o(T)` or obtain a new source estimate below the mollified mean-square floor. Finite-support multiplicity and positive-density results do not exclude the remaining off-line multiplicity mass or orient a global Xi source. Large-value selectors must also control zero-side fluctuation and exclude short multiplicative factors.
- **Evidence:** [Finite multiplicity inequalities](../../../../formal/GaloisForLFunctions/HilbertMetric/LamzouriFiniteMultiplicity.lean), [Montgomery--Taylor Xi densities](../../../../formal/GaloisForLFunctions/RHTower/LamzouriMontgomeryTaylorXiDensity.lean), [pair-correlation minorants](../../../../formal/GaloisForLFunctions/RHTower/LamzouriPairCorrelationMinorants.lean), [unconditional first-moment card](../3-formalized/zeta-off-line-first-moment-linear-unconditional.md), [factorized resonance](../../../../formal/GaloisForLFunctions/RHTower/SelectionResonanceFactorizationMain.lean).

### Reflected-AFE and prime-phase recurrence

- **Closed:** Literal reflected-AFE positive-energy event, covariance identities and stable
  power minors. Product-ordered, separated terminal prime–cofactor blocks supply `C N^J`
  distinct coloured transversals; a common determinant floor `δ` yields the corresponding
  Gram determinant lower bound by summing their squared minors. Smooth-AFE negative-edge
  values now agree for every negative edge; the former `c≤1` restriction was artificial.
- **Open:** Prove that robust determinant floor for the literal reflected-AFE coefficients
  at the required scales, then uniform conditional covariance, simultaneous local target
  probability and deterministic vertical prime-flow recurrence. Counting alone supplies
  no minor floor; retain smooth background, complement and pole.
- **Evidence:** [Coloured Gram-minor inequality](../../../../formal/GaloisForLFunctions/HTGeometry/ComplexGramColoredMinors.lean), [actual terminal blocks and conditional Gram bound](../../../../formal/GaloisForLFunctions/RHTower/SteinhausTerminalColoredMinors.lean), [arbitrary negative edge](../../../../formal/GaloisForLFunctions/RHTower/SmoothAFEZetaArbitraryNegativeEdge.lean); [earlier AFE details](rh-frontier-reference-2026-09-12.md#source-line-2720).

### Barban–Vehov and Levinson energy diagnostics

- **Closed:** Absolute Barban–Vehov coefficient mass is linear in the mollifier length. At the exact quadratic horizon `L=M²`, reciprocal tuning has full detector energy `1/6`, split asymptotically into included mass `1/48` and omitted mass `7/48`. The fixed-ratio tuned regime also has an exact included/omitted asymptotic decomposition.
- **Open:** These fixed-horizon asymptotics do not prove `SharpEnergyInput C`, which requires one uniform bound over every large block base, displacement and sharp head length. The detector-specific displaced dyadic law, census constant and sparse off-line-zero exclusion remain open.
- **Evidence:** [Linear absolute mass](../../../../formal/GaloisForLFunctions/RHTower/Sieve/BarbanVehovLinearL1.lean), [full quadratic-horizon energy](../../../../formal/GaloisForLFunctions/RHTower/Sieve/DifferentiatedBarbanVehovQuadraticHorizonEnergy.lean), [included energy](../../../../formal/GaloisForLFunctions/RHTower/Sieve/DifferentiatedBarbanVehovIncludedQuadraticHorizonEnergy.lean), [omitted energy](../../../../formal/GaloisForLFunctions/RHTower/Sieve/DifferentiatedBarbanVehovOmittedQuadraticHorizonEnergy.lean), [fixed-ratio split](../../../../formal/GaloisForLFunctions/RHTower/Sieve/DifferentiatedBarbanVehovOmittedTunedEnergy.lean).

### Dyadic Xi roots and continuation

- **Closed:** Arithmetic convolution-root towers; every dyadic Xi-root level now extends
  from the Euler chamber to one common symmetric **Littlewood zero-free cusp**, with
  width proportional to `log log |t| / log |t|` at large height. The central theta
  probability still has no probability convolution square root and is not infinitely divisible.
- **Killed producers:** [Every positive cofinal squarefree-half Laplace heat clock](rh-killed-routes.md#no-go-242), including arbitrarily sparse clocks: source mass diverges at `s=2/3` while the pole factor stays bounded away from zero. [The paired-eta square-root detour](rh-killed-routes.md#no-go-269) has an actual simple auxiliary zero in `rightHalf`.
- **Open:** Global analytic continuation through the remaining strict right critical
  half-plane with the required monodromy/order control. Restricted-cusp extension does
  not construct that global root, and the all-level theorem does not separately package
  a coherent analytic tower. A replacement heat construction needs genuine source-mass
  compensation, not a different schedule; removing the eta correction needs a controlled
  limiting root, not just locally uniform convergence of its square.
- **Evidence:** [Wider cusp, all levels](../../../../formal/GaloisForLFunctions/RHTower/XiSymmetricLittlewoodZeroFreeCuspDyadicRoots.lean), [all-clock obstruction](../../../../formal/GaloisForLFunctions/RHTower/SquarefreeConvolutionHalfLaplaceAllClocksNoGo.lean), [eta factorization and dilation limit](../../../../formal/GaloisForLFunctions/RHTower/PairedEtaRootContinuationBoundary.lean); [earlier cusp roots](rh-frontier-reference-2026-09-12.md#dyadic-cusp-roots) and [probability obstruction](rh-frontier-reference-2026-09-12.md#theta-probability-roots).

### Pole-cleared zeta-half causal source

- **Closed:** Exact causal Gamma-half kernel and actual arithmetic translate sum. For
  `Re s≥0`, the damped source's Laplace transform squares to
  `ζ(s+3) (s+2)/(s+3)²`. On logarithmic integer cells, the old-atom endpoint baseline
  is isolated and the remaining weighted cell mass is summable for every `σ>1/2`.
- **Open:** Control the accumulated old-atom baseline and the full source's growth to
  obtain continuation beyond the absolute-convergence region. Absolute atomwise
  interchange requires `Re(s+3)>1`, so it cannot reach the target point `s+3=2/3`.
  A positive, decaying convolution square alone [does not control its causal root's growth](rh-killed-routes.md#no-go-270).
- **Evidence:** [Actual arithmetic Laplace identity and interchange boundary](../../../../formal/GaloisForLFunctions/RHTower/ZetaPoleHalfArithmeticLaplace.lean), [cell remainder and baseline](../../../../formal/GaloisForLFunctions/RHTower/ZetaPoleHalfCellRemainder.lean), [literal causal source](../../../../formal/GaloisForLFunctions/RHTower/ZetaPoleHalfCausalSource.lean).

### Positive zeta-half Tauberian inversion

- **Closed:** Gamma-half scaling, sharp harmonic-window un-tilting, matched local
  square-root boundary germs and localized Fourier decay.
- **Open:** Complete Tauberian inversion/unsmoothing to the ordinary coefficient
  asymptotic and the existing `ZetaBinomialHalfKatoInversion` input.
- **Evidence:** [Tauberian progress](rh-frontier-reference-2026-09-12.md#zeta-half-tauberian) and [boundary/inversion statement](rh-frontier-reference-2026-09-12.md#zeta-half-boundary).

### Prime-counting and signed normal-equation infrastructure

- **Closed:** An unconditional de la Vallée Poussin power-log prime number theorem is now
  available for both Chebyshev `ψ` and its Perron interface. Compact-frequency Abel tails
  and the exact positive logarithmic remainder-tail mass are formal, so those tails are not
  CCM's missing cancellation. Separately, the abstract
  half-log trace theorem now permits a bounded signed profile and weighted signed trace;
  positivity and a one-sided numerator hypothesis are no longer required.
- **Open:** Supply the source-specific exact normal equation, bounded signed profile,
  weighted-trace control and average needed by a named route. The unconditional PNT error
  does not imply CCM-FU's RH-equivalent dyadic subpower window law.
- **Evidence:** [Chebyshev power-log PNT](../../../../formal/GaloisForLFunctions/RHTower/ChebyshevPsiPowerLogPNT.lean), [compact-frequency prime tail](../../../../formal/GaloisForLFunctions/RHTower/PrimeZetaUniformCompactFrequencyTail.lean), [exact oscillatory log tail](../../../../formal/GaloisForLFunctions/RHTower/OscillatoryLogTailExact.lean), [signed half-log trace](../../../../formal/GaloisForLFunctions/HTGeometry/LogNormalEquationSignedTrace.lean).

### Finite determinant visibility

- **Closed:** Every finite nilpotent matrix, linear endomorphism and continuous endomorphism is
  invisible to `det(1-zN)`, whose value is identically one; nilpotent exponentials also have
  determinant one. This has been instantiated across the corpus's Jordan, BRST, Fock, Lax,
  Wronskian, completion-detector and principal-symbol nilpotent blocks. Integral `I-2T` also has
  odd, hence nonzero, determinant.
- **Open:** Any determinant route using these directions must add nonnilpotent/infinite-dimensional
  spectral data and prove source occurrence. Finite determinant-one identities classify blindness;
  they do not establish an approximation limit or transfer Kammeyer's analytic counterexample to
  unrelated models.
- **Evidence:** [Determinant mechanisms](../../../../formal/GaloisForLFunctions/HTGeometry/KammeyerDeterminantApproximationCore.lean), [corpus applications](../../../../formal/GaloisForLFunctions/HTGeometry/KammeyerDeterminantApproximationApplications.lean).

### Source-construction and selector checks

These results strengthen reusable infrastructure or close a specific proposed mechanism;
none supplies a new independent RH route.

| Family | Closed | Remaining boundary |
|---|---|---|
| Vector balancing | Open Banaszczyk transforms, finite sign recovery **conditional on nonempty iterated transform**, exact one-dimensional model; normalized cosine/rational product densities, moments and Gaussian–chi-square mixture/Jensen bound with factor `sqrt(2/π)`. | Prove the required multidimensional transform stability/nonemptiness and connect it to a literal RH source. Finite recovery and distribution identities do not supply either. |
| Multiple elliptic gamma | Nome-group rank modulo torsion equals augmented rational period rank minus one. For at least two upper-half-plane periods, the differentially algebraic locus is null/meagre and its complement is full-measure/comeagre. | Generic hypertranscendence is not a source-to-Xi orientation theorem; the prime-completion collapse result is unchanged. |
| Causal finite assemblies | Exact retarded interaction-shell pruning; real-frequency delay phases preserve power Gram and coherent-return modulus, including concrete BM responses. | The analytic scattering sum-rule hypotheses and full nonlinear action are not established by these finite identities. A [full logarithmic turn within the literal theta series' summability domain](rh-killed-routes.md#no-go-272) is impossible; logarithmic scale is not thereby physical Hawking time. |
| Finite Dirichlet algebra | Units in the finite-abscissa source algebra are exactly the series with nonzero first coefficient, and inversion remains in that algebra. Every scalar algebra map, and every invariant linear readout of a fixed nontrivial Dirichlet twist, is coefficient-one evaluation. Zeta has no literal nonzero translation period. | Higher homology or changed source modules remain open, but scalar evaluation, fixed twisted quotients and unchanged-coordinate periodicity are [closed shortcuts](rh-killed-routes.md#no-go-275). Balanced fixed eta rounds converge in the strip; unbalanced rounds diverge, and endpoint subtraction recovers eta without selecting zeros. |
| Finite cutoff and QFI | Finite continuation is an exact sum of two oppositely normalized escaping terms. At strict-left zeros the Möbius overflow has a zero-specific compensated limit. | Leading relative-phase QFI tends to the same value at every strict-left point, while inverse QFI coordinates merely reconstruct finite zeta; the [QFI/compensating-infinity selector is closed](rh-killed-routes.md#no-go-277). Subleading source-sensitive structure remains open. |
| Prime-face topology | Dirichlet weights gauge the admitted prime-face boundary graph to a parameter-independent graph; every cutoff cycle through `N` explicitly bounds through `2N`, also with Dirichlet weights. | Bare finite homology is [nonselective](rh-killed-routes.md#no-go-278). Filling norms, cofinal quantitative torsion, distinguished source classes and analytic completion remain open. |
| Differential/cohomological selectors | [Painlevé III(D₆) polynomial-gauge bridge excluded](rh-killed-routes.md#no-go-274) from its actual local sigma equation, not an assumed differential-algebraicity premise. [Saddle/de Rham shortcuts fail](rh-killed-routes.md#no-go-273), while exact Mellin, Hodge and arithmetic-contraction identities survive. | A different carrier/source law must escape the stated obstruction. Neither local stationarity, closedness nor a critical-line norm receiver locates the Xi divisor. |

Evidence: [finite sign-recovery interface](../../../../formal/GaloisForLFunctions/HTGeometry/BanaszczykSignRecovery.lean), [mixture identity](../../../../formal/GaloisForLFunctions/RHTower/BanaszczykGammaMixtureBridge.lean), [product Jensen bound](../../../../formal/GaloisForLFunctions/RHTower/BanaszczykChiSquareJensen.lean), [nome rank and genericity](../../../../formal/GaloisForLFunctions/HTGeometry/MultipleEllipticGammaNomeRankGenericity.lean), [finite causal applications](../../../../formal/GaloisForLFunctions/RHTower/ArxivCausalityCorpusApplications.lean), [delay-algebra scope](../../../../formal/GaloisForLFunctions/HTGeometry/Arxiv2608CausalitySumRules.lean), [eta round convergence](../../../../formal/GaloisForLFunctions/RHTower/EtaArithmeticRoundConvergence.lean), [visible-coprime summability](../../../../formal/GaloisForLFunctions/RHTower/VisibleCoprimeMellinSummability.lean).

### Other shared bridges

The reference index below preserves every existing bridge/pre-route section, including
results whose only surviving use is a receiver or no-go. Their presence does not promote
them to active routes.

<details>
<summary>Browse all shared bridge and pre-route sections</summary>

- [Mellin/Perron continuation infrastructure](rh-frontier-reference-2026-09-12.md#source-line-2339)
- [Montgomery explicit formula and pair form](rh-frontier-reference-2026-09-12.md#source-line-2343)
- [W2C — two-channel Weil bridge](rh-frontier-reference-2026-09-12.md#source-line-2351)
- [Screw square-energy receiver](rh-frontier-reference-2026-09-12.md#source-line-2361)
- [Horizontal-charge package](rh-frontier-reference-2026-09-12.md#source-line-2365)
- [Response-work polarization](rh-frontier-reference-2026-09-12.md#source-line-2371)
- [Cofinal formation capital](rh-frontier-reference-2026-09-12.md#source-line-2387)
- [Higher-arity serial-observer homology](rh-frontier-reference-2026-09-12.md#source-line-2405)
- [Derived and factor-framed selection geometry](rh-frontier-reference-2026-09-12.md#source-line-2415)
- [Cassidy differential-Galois dichotomy](rh-frontier-reference-2026-09-12.md#source-line-2437)
- [Bounded differential syntax and finite-jet blindness](rh-frontier-reference-2026-09-12.md#source-line-2445)
- [Finite holomorphic scattering gauges](rh-frontier-reference-2026-09-12.md#source-line-2487)
- [Rectangular Gram-fibre rigidity](rh-frontier-reference-2026-09-12.md#source-line-2493)
- [Matrix-valued free-Fock spectral law](rh-frontier-reference-2026-09-12.md#source-line-2499)
- [Infinite projective erosion and finite capacity geometry](rh-frontier-reference-2026-09-12.md#source-line-2507)
- [Common-profile Möbius--Poisson join](rh-frontier-reference-2026-09-12.md#source-line-2515)
- [Unconditional critical-line census](rh-frontier-reference-2026-09-12.md#source-line-2521)
- [Arithmetic source-moment Torelli](rh-frontier-reference-2026-09-12.md#source-line-2557)
- [Central theta source: proved first minor and all-rank boundary](rh-frontier-reference-2026-09-12.md#source-line-2565)
- [Relative-completion stability transgression](rh-frontier-reference-2026-09-12.md#source-line-2587)
- [Finite path-cochain reduction](rh-frontier-reference-2026-09-12.md#source-line-2593)
- [Faithful prime formation and noncompact boundary interception](rh-frontier-reference-2026-09-12.md#source-line-2597)
- [Projective reciprocal squarefree Ward seam](rh-frontier-reference-2026-09-12.md#source-line-2604)
- [Arithmetic Fredholm orientation and recurrence](rh-frontier-reference-2026-09-12.md#source-line-2608)
- [Physical-algebra and Rajchman phase bridges](rh-frontier-reference-2026-09-12.md#source-line-2628)
- [Oscillatory window capacity and its selector boundary](rh-frontier-reference-2026-09-12.md#source-line-2638)
- [Prime-tail diagonal escape](rh-frontier-reference-2026-09-12.md#source-line-2644)
- [Arithmetic second-order return receiver](rh-frontier-reference-2026-09-12.md#source-line-2652)
- [Bellman--Shoreline finite control geometry](rh-frontier-reference-2026-09-12.md#source-line-2658)
- [Chronological capacity and collective nonuniformity](rh-frontier-reference-2026-09-12.md#source-line-2662)
- [Quotient lifts and ensemble spectral edges](rh-frontier-reference-2026-09-12.md#source-line-2670)
- [Modal and pseudospectral transport](rh-frontier-reference-2026-09-12.md#source-line-2712)
- [Smooth AFE and Levinson window](rh-frontier-reference-2026-09-12.md#source-line-2720)
- [Matomäki--Teräväinen short-interval sieve infrastructure](rh-frontier-reference-2026-09-12.md#source-line-2774)
- [Visible-coprime orientation](rh-frontier-reference-2026-09-12.md#source-line-2784)
- [Finite generalized-Schur inertia](rh-frontier-reference-2026-09-12.md#source-line-2792)
- [Wold thermofield infrastructure](rh-frontier-reference-2026-09-12.md#source-line-2802)
- [Irregular Stokes sheaf foundation](rh-frontier-reference-2026-09-12.md#source-line-2806)
- [Finite Hasse and Weyl classifiers](rh-frontier-reference-2026-09-12.md#source-line-2812)
- [Restricted-history completion and priced darkness](rh-frontier-reference-2026-09-12.md#source-line-2832)
- [Other pre-routes](rh-frontier-reference-2026-09-12.md#source-line-2836)

</details>

## Evidence and terminology

### Evidence boundary

The register reconciles committed Lean source through the cutoff above. The latest 72-file
formal-source delta contains 61 additions and 11 modifications across existing routes, candidates
and shared infrastructure. All changed source files and route fact logs were classified. Twelve
new grouped no-go records were added; no active or candidate label was created.

Major closures are P/SP-E's all-path five-channel ordered carrier and exact history ledger; Q's
paired-diagonal band through `1047/100`; PTR's literal temporal-Maxwell cyclic transfer; SQB's
modular energy, witness-line and finite-grid core; O's homogeneous wall/common-clock law; SV2's
finite-head recurrence and asymptotic-saturation obstruction; T1/T2's stationary/Möbius source
classifications; FZZ-P's factorized/symmetric depth no-gos; EDQ's child-fibre contrast; and HB's
eventual principal-growth lower bound. Open route-level burdens are now sharper: global changing-
core cancellation, graph-closed P/SP-E variance control, full-strip Q positivity, exact-prime Weil
coercivity, infinite-ladder PTR confinement, SQB bounded-core total boundedness, and RH itself.

This is a source-statement audit, not a fresh kernel/dependency validation. No build or generated
check was run. It does not broaden theorem hypotheses or promote paper-only arguments. Current source links
support the changed frontiers; historical qualifications remain in the unchanged
[reference snapshot](rh-frontier-reference-2026-09-12.md).
That snapshot also preserves the former executive updates and normalized verdicts;
they are no longer parallel current-status lists.

### Status language

| Term | Meaning |
|---|---|
| Closed / proved | The scoped intermediate theorem is recorded in Lean source. It is not necessarily an RH-producing theorem. |
| Open | The missing source estimate, construction, comparison or global passage. |
| Receiver / endpoint | A proved implication or equivalence whose premise still has to be produced. |
| Candidate | An interface/source fragment without the required complete source handoff or exhaustion. |
| Killed / terminal | The named mechanism is impossible, nonselective, or merely repackages the RH premise. Consult its exact no-go. |
| Survivor | The strongest retained positive result or changed problem after an obstruction. It is not automatically a new route. |

### Common open problems

| Gate | Mathematical burden |
|---|---|
| ORD | Signed source order, cancellation, passivity or a quantitative current budget. |
| COF | One source-selected family controlling all required scales, apertures, degrees and escape directions. |
| LAND | Coefficient-, multiplicity- and orientation-faithful source-to-target passage. |
| ORIENT | Reflection-sensitive or off-diagonal information lost by scalar/diagonal receivers. |
| COMP | Faithful infinite completion or descent from finite source data. |
| DYN | A selective law of the complete nonlinear physical source. |

The shared hard problem is source production plus faithful global propagation.
More exact receivers do not supply either automatically.

[Detailed shared receiver relationships](rh-frontier-reference-2026-09-12.md#source-line-292) ·
[Cross-route conclusions and boundary-modulus obstruction](rh-frontier-reference-2026-09-12.md#source-line-3157)
