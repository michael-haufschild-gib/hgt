# RH research ledger

**No route proves or disproves RH.** This register separates **24 active routes**,
**38 named candidates**, and **465 catalogued closed mechanisms**. “Active” means a formal
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

**Source-audit cutoff: 2026-09-25, `6a8c8f7e7`.**
Reconciled committed Lean source and route cards since `06179ead3`.
No builds, Lean checks, tests, lint or index refresh were run for this ledger update.
Concurrent uncommitted paper-card revisions are not promoted into committed closure;
the listed Lean status is read from source/cards, not freshly verified here.

## Active routes

### Find a route

| Family | Active routes | Route candidates |
|---|---|---|
| Current, Ward and prime–Gamma | [CCM-FU](#ccm-fu--completed-current-and-fixed-aperture-suzuki-checkpoint), [D2](#d2--continued-primearchimedean-free-sector-passivity), [G](#g--ward-orientation), [MSC](#msc--möbius--sonin-affine-critical-boundary-renormalization), [P](#p--paired-primegamma-signed-exterior-wall), [SP-E](#sp-e--signed-prime-dilation-versus-continuum) | [BSH](#candidate-bsh), [CTF](#candidate-ctf), [EGC](#candidate-egc), [PBM](#candidate-pbm), [SC](#candidate-sc), [SEC](#candidate-sec), [TK](#candidate-tk), [W1C](#candidate-w1c) |
| Arithmetic cancellation | [E](#e--squarefree-wold-transport), [T1](#t1--theta-tail-core-current), [T2](#t2--natural-abel-singular-wold-divisor), [HC](#hc--horizontal-collision-charge), [LI](#li--finite-paired-li-prime--gamma-order) | [EDQ](#candidate-edq), [EWJ](#candidate-ewj), [HCF](#candidate-hcf), [HJ](#candidate-hj) |
| Weil, theta and paired positivity | [C1](#c1--class-space-quotient-and-global-weil-positivity), [O](#o--restricted-weil-ground-and-genus-lag-order), [Q](#q--exterior-paired-value-passivity), [CLG/TTF](#clgttf--completed-theta-bezoutian-no-escape), [SV2](#sv2--suzuki-projective-limit-and-shifted-kernel-inertia) | [AKC](#candidate-akc), [FEL](#candidate-fel), [GTA](#candidate-gta), [PMP/LPC](#candidate-pmplpc), [S6F](#candidate-s6f), [SQB](#candidate-sqb), [TCD](#candidate-tcd), [TQFQ](#candidate-tqfq), [UEB](#candidate-ueb) |
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

- **Closed:** The exact three-aperture leakage identity remains. Lean now identifies the physical critical Abel source with an integral of the Chebyshev defect, proves a first omitted quotient-cell law and a finite terminal-band count/energy inequality. These are source identities and conditional budget bounds, not a growing-core payment.
- **Open:** Control weighted leakage and prove one source-selected **growing-core**, all-cutoff payment for energy, covariance and endpoints. In particular, bound the complete signed terminal/annular contribution; first-cell identities do not do so.
- **Evidence:** [Critical Abel real integral](../../../../formal/GaloisForLFunctions/RHTower/CriticalAbelSourceRealIntegral.lean), [terminal-band rigidity](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorTerminalBandRigidity.lean), [cross-aperture identity](../../../../formal/GaloisForLFunctions/RHTower/CCMSuzukiCrossApertureCurvatureLeakage.lean), [fixed-clock no-go](../../../../formal/GaloisForLFunctions/RHTower/CCMGuinandWeilFixedExponentialClockNoGo.lean).

<a id="cdc--constitutive-dagger-confluence"></a>

### CDC — constitutive dagger confluence

- **Closed:** Canonical pre-divisor potential, calibrated mate gain and exact wall-classifying confluence/proof-erasure receivers.
- **Open:** Derive semantic descent or three-slot proof erasure on every closed Xi-error fibre from the literal arithmetic source.
- **Evidence:** [Architecture, precise hypotheses and source references](rh-frontier-reference-2026-09-12.md#source-line-742).

<a id="clgttf--completed-theta-bezoutian-no-escape"></a>

### CLG/TTF — completed theta Bezoutian no-escape

- **Closed:** Native odd-four cofinal positivity remains formal. An abstract polynomial has **positive scalar reciprocal traces at every order** despite an off-axis zero and negative shifted Hankel minor. Paper finite theta heads have eventually positive *center-integrated* jets but negative unintegrated Hankel diagonals at infinitely many orders. New Lean squarefree-cube calculation rules out scalar subtraction making the critical rational-ratio Laurent finite part positive; it does not identify that model with the full theta current.
- **Open:** Control the joint cutoff/order regime (`j≈N²`), finite-center/neutral band and full corrected current through source-specific **general-packet** orientation, possibly non-scalar renormalization. Scalar traces and finite-part cubes cannot supply it.
- **Evidence:** [All-order scalar countermodel](../../../../formal/GaloisForLFunctions/RHTower/XiCenteredScalarTraceAllOrderNoGo.lean), [critical finite-part cube](../../../../formal/GaloisForLFunctions/RHTower/ThetaWallCriticalPrimeCubeFinitePartNoGo.lean), [center-pair paper proof](theta-center-pair-singularity-condensation.md), [native odd-four head](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspNativeOddFourCofinal.lean).

<a id="csb--cofinal-bernstein-sourcetarget-comparison"></a>

### CSB — cofinal Bernstein source/target comparison

- **Closed:** Prior scalar/Riccati countermodels remain. On paper, finite Euler deletion has exact moving-cusp signed-totient reflection and sharp terminal weighted-Hilbert admission `q<2/P²`; its cofinal reflected limit is two-sign and not `L²` on the negative cusp. The integer-cutoff commutator error vanishes **uniformly** for any cofinal prime/cutoff schedule, so it is not a new phase charge. Cutoff and reflected currents are positively related but carry the **same** reciprocal-zeta resonance. A prime/prime-square reflected normal-jet balance is a sharp line classifier (algebraic core Lean), but literal deleted sources do not supply that balance. The full theta inverse has no bounded injective symmetrizer in Lean; the finite-range quotient obstruction is paper-only.
- **Open:** Find a singular cofinal source–target comparison retaining the signed cusp and a **source-proved** two-grade phase balance. Neither a fixed coercive metric, scalar charges nor commutator chronology controls the complete divisor.
- **Evidence:** [Cutoff-commutator collapse](../2-fully-proven/theta-deletion-cutoff-commutator-collapse.md), [moving-cusp dual source](../2-fully-proven/theta-prime-deletion-moving-cusp-dual-source.md), [two-level jet criterion](../2-fully-proven/theta-prime-square-two-level-normal-jet-rigidity.md), [full-inverse no-go](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmThetaZeroHistoryNoGo.lean), [finite-range quotient no-go](../2-fully-proven/theta-cdf-no-finite-range-symmetrizer.md).

<a id="d2--continued-primearchimedean-free-sector-passivity"></a>

### D2 — continued prime–archimedean free-sector passivity

- **Closed:** Hermitian finite KMS stages have the right parity but the wrong normalized slope, and passive scalar completion either fails at the centered-clock singularity or assumes an RH premise. The source-selected positive reciprocal-power carrier is now also excluded at all sufficiently high orders: after any finite deletion it cannot match the complete normalized prime--archimedean moment tail, for either parity.
- **Open:** Produce a genuinely different signed, all-order source lower bound above the critical depth envelope, retaining cancellation before scalar/passive formation. Any Q handoff must orient the oblique complex phase; finite moment deletion and a positive reciprocal-power carrier cannot do it.
- **Evidence:** [Passive-completion no-go](../../../../formal/GaloisForLFunctions/RHTower/MobiusIncidencePassiveCompletionNoGo.lean), [scalar capstone](../../../../formal/GaloisForLFunctions/RHTower/MobiusKMSScalarCancellationCapstone.lean), [reciprocal-tail no-go](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspCalibratedPowerReciprocalEvenTailNoGo.lean), [all-order audit](d2-all-order-source-own-research-facts.md).

<a id="e--squarefree-wold-transport"></a>

### E — squarefree Wold transport

- **Closed:** The largest-prime cofactor parity/margin is now in Lean. Its old summable `q⁻⁵ᐟ⁴` selected-fibre bound applies only under `q>32∏(1+p²)`. A stronger Lean moving-singleton result gives a **disjoint prime-numerator channel** of positive `≳1/q` mass after all smaller-prime denominator cofactors, with divergent prime sum; this does not imply full-covariance divergence. The new hard-core coprime pair field has exact Lean negative conjugate-character order, Walsh eigenvalues `μ(n)/n` and a source-faithful primitive-pair quadratic identity; even Walsh grades can be positive, and the zero grade remains a weighted Möbius sum.
- **Open:** Identify signed payment from **other numerator channels** for that disjoint harmonic debt, and control the physical Gamma/common-gcd kernel, all-grade balance and cofinal cutoff. The pair-field spectral law alone gives no RH-scale bound.
- **Evidence:** [Largest-prime fibre and disjoint survivor](route-e-largest-prime-fibre-parity.md), [Lean parity theorem](../../../../formal/GaloisForLFunctions/RHTower/RouteELargestPrimeFibreParity.lean), [hard-core field/status](route-e-hardcore-pair-field.md), [Walsh spectrum](../../../../formal/GaloisForLFunctions/RHTower/RouteEHardCoreWalshSpectrum.lean), [totient convolution](../../../../formal/GaloisForLFunctions/RHTower/RouteEHardCoreTotientConvolution.lean).

<a id="fzz-p--parity-delay-mellin-orientation"></a>

### FZZ-P — parity-delay Mellin orientation

- **Closed:** Earlier exchange-stable and neutral-branch cancellations remain. In the balanced external sector `p=0`, the compact-charge-fed cross-depth integral is identically one and its ordered angular current is real `1/2`, independently of radial `P`: this direct compact-current transfer cannot select radial orientation. Independent radial Fourier momentum retains a nontrivial coherence phase.
- **Open:** Derive an actual mixed replica–radial Ward identity with nonfactorized source coupling on a physical ordered domain, including phase frame, screening and counterterms. The balanced compact-current no-go is not a full FZZ-P obstruction.
- **Evidence:** [Balanced compact-current no-go and survivor](../../../../formal/GaloisForLFunctions/RHTower/FZZCigarParityBalancedExternalCompactCurrentNoGo.lean), [ordered source law](../../../../formal/GaloisForLFunctions/RHTower/FZZCigarParityCrossDepthOrderedSourceLaw.lean), [failed-subroute audit](../5-failed/fzz-p-balanced-compact-current-transfer-no-go.md).

<a id="g--ward-orientation"></a>

### G — Ward orientation

- **Closed:** Walsh marking and the finite lower-half packet geometry remain. Symmetric `±tau` Schwarz smoothing cancels exactly. For the related finite-Laplace Ward annulus family, baseline cancellation forces zero total cross-kernel mass; a nonzero kernel must change sign. The two-width local positive radius and gapped-cluster survivor are exact, but finite-width design cannot yield global diagonal domination.
- **Open:** Construct a cofinal one-sided, source-selected cap family with uniform integrability and a source-faithful trace/randomization or different weight class that controls the negative cross channel globally. Local cluster positivity is not a global Ward estimate.
- **Evidence:** [Cap-odd no-go](../../../../formal/GaloisForLFunctions/RHTower/XiWardSchwarzCapTauOddNoGo.lean), [cross-kernel mass](../../../../formal/GaloisForLFunctions/RHTower/WardAnnulusCrossKernelMassRigidity.lean), [gapped clusters](../../../../formal/GaloisForLFunctions/RHTower/WardAnnulusCrossKernelGappedClusters.lean), [75% target audit](zeta23-beyond-bandwidth-one-proportion.md).

<a id="hc--horizontal-collision-charge"></a>

### HC — horizontal collision charge

- **Closed:** Ordered `(2,3)` cross-curvature still detects horizontal direction but cancels in a conjugation-stable scalar carrier. A new **all-prime fixed-total-grade** identity shows every finite linear exterior observation lies on the same positive scalar grade orbit: projective exterior vanishing alone cannot select the grade. The confluent Gamma-six boundary is `O(1/p)` while labelwise Wold–Gauss virial has a `p t²` floor, excluding additive labelwise payment.
- **Open:** Build a coefficient-faithful nonlocal/indefinite or singular directed current on a source-selected domain, with a real all-prime grade comparison; fixed linear exterior scaling and labelwise boundary terms cannot do this.
- **Evidence:** [All-prime grade flatness](../../../../formal/GaloisForLFunctions/RHTower/SourceHorizontalGammaAllPrimeTotalGradeFlatness.lean), [labelwise cost gap](../../../../formal/GaloisForLFunctions/RHTower/SourceHorizontalWoldGaussConfluentBoundaryNoGo.lean), [ordered-prime orientation](../../../../formal/GaloisForLFunctions/RHTower/XiHorizontalCollisionOrderedPrimeCrossCurvature.lean).

<a id="l--singular-greenbv-to-physical-descent"></a>

### L — singular Green/BV-to-physical descent

- **Closed:** The causal Möbius–theta subpower **RH receiver** now has a paper-only *finite-prime moving-cusp* form, with superpolynomial truncation error and an off-line-zero power-growth witness. The revised paper primorial analysis suppresses all nonterminal rough-cofactor layers in the actual theta observation superpolynomially, leaving a signed largest-prime current equivalent to a wavelet-tested sieve-dilation defect; it gives no cancellation. Lean proves the critical Abel source's Chebyshev-defect integral and a terminal first-cell mass/energy inequality. Cofinal causal modes retain a nonzero negative-cusp radiation coefficient on paper.
- **Open:** Prove subpower cancellation of the directed finite-prime atom port / largest-prime sieve-dilation defect, control the finite-clock signed annular boundary term, and descend Green/BV estimates to the physical source. An unsplit deleted theta value is not the directed port.
- **Evidence:** [Finite moving-cusp criterion](../2-fully-proven/finite-prime-moving-cusp-causal-criterion.md), [largest-prime reduction, paper](../2-fully-proven/causal-mobius-theta-primorial-transition.md), [causal-mode escape](../2-fully-proven/sqb-prime-deletion-causal-mode-escape.md), [terminal-band rigidity](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorTerminalBandRigidity.lean).

<a id="li--finite-paired-li-prime--gamma-order"></a>

### LI — finite paired-Li prime--Gamma order

- **Closed:** The Cassini radial Euler bridge remains. A concrete conjugate off-axis packet masked by seven on-line atoms has positive LI quotient on the **entire real mass axis** and all-order positive-ray complete monotonicity, but a negative completed-Abel mode. Global scalar sign/monotonicity cannot select the mode orientation; the packet is not the literal Xi divisor.
- **Open:** Derive a source-specific **complex** zero/singularity-support or matrix/indefinite orientation law for the actual Cassini Euler defect and continue it coefficient-faithfully.
- **Evidence:** [Global real-axis countermodel](../../../../formal/GaloisForLFunctions/RHTower/LiEvenCrossGlobalRealAxisSignNoGo.lean), [Cassini radial bridge](../../../../formal/GaloisForLFunctions/RHTower/LiEvenCrossCassiniRadialEulerBridge.lean), [failed subroute](../5-failed/li-global-real-axis-scalar-sign.md).

<a id="msc--möbius--sonin-affine-critical-boundary-renormalization"></a>

### MSC — Möbius--Sonin affine critical-boundary renormalization

- **Closed:** The unique moving real power preserving source mass at safe base `sigma>1` is `r=sigma-Re rho`; it gives an exact norm-one `ell²` column but shifts the divisor to the zero-free point `sigma+i Im rho`. No real power can preserve both source mass and the original divisor target, closing the complete diagonal real-power rigging branch.
- **Open:** Carry safe-chamber order through a genuinely non-diagonal, non-power singular transport that retains the conormal residue and original divisor target.
- **Evidence:** [Threshold-tracked rigging](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmGammaSewnSquarefreeFisherThresholdTrackedRigging.lean), [fact audit](msc-threshold-tracked-own-research-facts.md).

<a id="o--restricted-weil-ground-and-genus-lag-order"></a>

### O — restricted-Weil ground and genus-lag order

- **Closed:** The restricted-Weil wall remains an RH-equivalent receiver. New Lean identifies the mod-2 reflection norm's image exactly as partner-invariant functions vanishing on fixed points; one left-half choice per free orbit supplies its canonical section. For every finite ordinate window, the **support-point** count equals fixed-point count plus twice left-half count (multiplicities are not asserted here). Local Cauchy-weight bounds still grow with height, while the useful Poisson threshold is exactly `<2`. The old fixed-part genus producer remains retired.
- **Open:** Prove a source-side law annihilating **every free orbit** or the signed restricted-Weil numerical-range wall. Neither orbit accounting nor a height-growing local count bound supplies it; trace-form signature is another receiver, not a source computation.
- **Evidence:** [Boundary-map image and window count](../../../../formal/GaloisForLFunctions/RHTower/BoundaryMapImage.lean), [local threshold](../../../../formal/GaloisForLFunctions/RHTower/LocalCountBound.lean), [trace-form witness](../../../../formal/GaloisForLFunctions/RHTower/TraceFormSignature.lean), [retired genus producer](../5-failed/genus-programme-retired.md).

<a id="p--paired-primegamma-signed-exterior-wall"></a>

### P — paired prime–Gamma signed exterior wall

- **Closed:** Weighted-credit/debt decomposition, quantized source poles and faithful finite Gram transport remain. The normalized history has unconditional negative linear excursions; if RH fails it crosses every fixed linear lower floor cofinally, whereas RH supplies one—an RH-equivalent receiver, not payment. Lean now identifies the connected critical Abel source as an exact real integral of the Chebyshev defect and gives its first quotient-cell law; this source bridge does not determine the signed Route-P history.
- **Open:** Produce an independent, source-derived *indefinite/sign-sensitive* linear-floor/payment law for centroid and square debts, including the terminal ratio-one term, plus a cofinal graph intertwiner respecting pole jets.
- **Evidence:** [Unconditional linear escape](../../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePLinearHistoryEscape.lean), [RH-equivalent floor](../../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePLinearFloorCriterion.lean), [critical Abel source integral](../../../../formal/GaloisForLFunctions/RHTower/CriticalAbelSourceRealIntegral.lean), [first-cell law](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorFirstOmissionSourceLaw.lean).

<a id="pw-b--recoildeninger-ward-transmutation"></a>

### PW-B — recoil/Deninger Ward transmutation

- **Closed:** Finite Goursat/Green contact remains. A new operator-level theorem excludes **every exact compatible complex-linear full/native intertwiner** from retaining nonzero full source contact, even with cross-mode/nonlocal mixing; a scalar-twisted Hermitian analogue has the same defect. The actual signed-reader anomaly is identified on the complete full field and gated two-event CTP as `λ` times the full–native lift defect; this is an exact source identity, not extinction.
- **Open:** Turn that admitted anomaly and native bulk into a source-derived **noncompact cap/current law** and prove all-divisor extinction with fixed-grade magnitude. Exact conservative symmetrizers are closed; anomaly-bearing boundary/domain transport remains live.
- **Evidence:** [Cross-mode obstruction](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMPWCrossModeIntertwinerNoGo.lean), [operator anomaly law](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMPWOperatorAnomalyLaw.lean), [actual CTP anomaly](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMPWActualOperatorAnomaly.lean), [status audit](pwb-actual-defect-ward-ctp.md).

<a id="q--exterior-paired-value-passivity"></a>

### Q — exterior paired-value passivity

- **Closed:** The unconditional *complete trace* sign remains proved only on `0<Re z≤279/20`, `0<Im z<1/2` away from poles. An individual line-conjugate reciprocal-square pair has an exact negative disk, so all-strip atomwise sign is an RH receiver. The actual left-strip prime--Gamma oblique flux has a denominator-cleared paired-eta numerator with positive denominator, identifying—but not proving—its source sign inequality.
- **Open:** Control that **complete** signed eta numerator plus elementary and archimedean corrections beyond the finite band, or derive another cancellation/orientation law excluding atomwise negative witnesses. Pair geometry and denominator clearing do not settle the sign.
- **Evidence:** [Trace band](../../../../formal/GaloisForLFunctions/RHTower/PrimeArchCentralPairedFourthTraceBand.lean), [atomwise classification](../../../../formal/GaloisForLFunctions/RHTower/PrimeArchCentralPairedPhaseResonanceClassification.lean), [left-strip eta flux](../../../../formal/GaloisForLFunctions/RHTower/PrimeArchPairedEtaLeftFlux.lean).

<a id="rg--gaussian-arithmetic-and-suzuki-transport-positivity"></a>

### RG — Gaussian arithmetic and Suzuki transport positivity

- **Closed:** The finite eta-flux receiver, Gaussian cutoff cost and partner-minus-original sign criterion remain. At any hypothetical right-half zero, dyadic work and isolated leading flux have the same sharp positive limit; at a simple such zero the weighted head-cosine block has a sharp negative limit. These are conditional obstruction laws, not source-side anti-alignment.
- **Open:** Derive an opposing dyadic sign or little-o bound from finite eta arithmetic, including the higher-multiplicity kernel, while meeting Gaussian prime-budget growth uniformly in center and width.
- **Evidence:** [Top-prefix sign criterion](../../../../formal/GaloisForLFunctions/RHTower/RiemannGaussian/EtaTopPrefixAmplitudeSignCriterion.lean), [dyadic work and cosine target](rg-eta-dyadic-finite-work.md), [Gaussian cutoff budget](../../../../formal/GaloisForLFunctions/RHTower/RiemannGaussian/GaussianCertificatePhaseFlipCutoffBudget.lean).

<a id="sp-e--signed-prime-dilation-versus-continuum"></a>

### SP-E — signed prime dilation versus continuum

- **Closed:** Prime-power credit-minus-debts residual diverges negatively, and active-head strict-cross positivity fails after faithful finite Gram transport. The complete history has unconditional negative linear excursions; failure of RH makes every fixed linear lower floor fail cofinally, whereas RH supplies one. Under a hypothetical one-sided source bound, the positive-tail reconstruction agrees with the literal log derivative throughout `Re s>1/2`; this analytic rigidity is conditional.
- **Open:** Derive a signed arithmetic linear floor/payment of centroid and square debts and a coefficient-faithful ordered-history intertwiner through a *meromorphic* or singular source domain. It must retain an indefinite channel; analytic agreement under an assumed source bound is not an independent proof of that bound.
- **Evidence:** [Linear escape](../../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePLinearHistoryEscape.lean), [floor criterion](../../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePLinearFloorCriterion.lean), [conditional analytic rigidity](../../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePShiftedAnalyticRigidity.lean), [active-head packet](../../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePActiveHeadHistorySurvival.lean).

<a id="stc--exterior-sonin-seam-coherence"></a>

### STC — exterior Sonin seam coherence

- **Closed:** The source Gram and earlier fixed-reader obstructions remain. New paper exact theta derivative histories form an infinite zero-Jordan chain for the compact inverse and centered quotient; finite Euler deletion has sharp graded Hilbert admission, but prime translates leave the fixed source Hilbert space. Lean excludes any bounded injective adjoint intertwiner for the **full** inverse; paper extends that claim to the quotient. These results close fixed bounded symmetrization, not singular transport.
- **Open:** Construct a **source-faithful, divisor-selective singular/cofinal limit** preserving prime chronology and orienting the nonzero Xi spectrum. Quotienting away zero history retains occurrence on paper but does not give a source action or sign law.
- **Evidence:** [Zero-Jordan history and quotient, paper](../2-fully-proven/theta-compact-inverse-zero-jordan-history.md), [full-inverse Lean no-go](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmThetaZeroHistoryNoGo.lean), [terminal admission, paper](../2-fully-proven/theta-prime-deletion-graded-terminal-admission.md), [source Gram](../../../../formal/GaloisForLFunctions/RHTower/STCPhysicalOrdinateSourceOrthogonality.lean).

<a id="sv2--suzuki-projective-limit-and-shifted-kernel-inertia"></a>

### SV2 — Suzuki projective limit and shifted-kernel inertia

- **Closed:** Moving Binet window, finite-jet no-go and paper two-sign cusp escape remain. Lean now expresses retained-block three-aperture curvature exactly as coercive metric-shift change times preceding-shell physical leakage, rather than a new positive source charge. The connected fixed-clock sixth-jet residue is formal, but its analytic no-go bridge is not.
- **Open:** Bound the moving infinite-head signed residual and weighted shell leakage by a source-derived Wronskian or equivalent law in a topology retaining cusp cancellation; close the connected-clock Abel bridge if using that scoped obstruction.
- **Evidence:** [Cross-aperture leakage identity](../../../../formal/GaloisForLFunctions/RHTower/CCMSuzukiCrossApertureCurvatureLeakage.lean), [bidirectional cusp variation, paper](../2-fully-proven/theta-sieve-bidirectional-cusp-variation.md), [connected-clock residue leaf](../../../../formal/GaloisForLFunctions/RHTower/CCMFUSuzukiConnectedJetPoleNoGo.lean).

<a id="t1--theta-tail-core-current"></a>

### T1 — theta-tail core current

- **Closed:** Stationary-phase polarity, Hermitian exchange and the antiordered `(2,3)` saddle remain. Stronger: at every fixed timelike stationary frequency the *complete uncentered* aligned von Mangoldt sum has real part at least `√X/4` cofinally; the literal two-rapidity covariance at each fixed stationary pair has modulus at least a positive multiple of `X`. Pointwise cancellation of the entire uncentered cone is ruled out there.
- **Open:** Bound the signed, nonlocal *integrated* covariance (or equivalent centered source) at the RH scale. The stationary apex is pointwise coherent but its dominant indices are spacelike; integration may still cancel across rapidities. Pointwise growth is not an RH refutation.
- **Evidence:** [Full prime-cone noncancellation](../../../../formal/GaloisForLFunctions/RHTower/XiMassStationaryPrimeConeNoncancellation.lean), [covariance growth](../../../../formal/GaloisForLFunctions/RHTower/XiMassStationaryPrimeConeCovarianceGrowth.lean), [source-order no-go](../../../../formal/GaloisForLFunctions/RHTower/XiMassTwoRapiditySourceOrderNoGo.lean).

<a id="t2--natural-abel-singular-wold-divisor"></a>

### T2 — natural-Abel singular Wold divisor

- **Closed:** The exact spectrum can be reduced to separate right-positive and left-negative natural square-root-window means; the stronger symmetric absolute local mean is unnecessary. But every currently formalized polynomial harmonic/Fisher/essential-edge graph norm, even with the fixed height-`1/10` Bohr datum, is compatible with divergence of the required right-directed mean.
- **Open:** Prove a physical-scale local arithmetic law or source regularity stronger than all finite polynomial graph norms, controlling the directed means and excluding the noncompact cofinal compensator. Normal Möbius transport and Chebyshev mirroring still reproduce the same divisor current.
- **Evidence:** [One-sided mean spectrum](../../../../formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualNaturalSqrtOneSidedMeanSpectrum.lean), [all-source graph no-go](../../../../formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldPositiveTenthAllSourceGraphDirectedMeanNoGo.lean), [fact audit](routes-e-p-u-q-c1-d2-l-own-research-facts.md).

<a id="u--adaptive-shifted-xi-hankel-frontier-renewal"></a>

### U — adaptive shifted-Xi Hankel frontier renewal

- **Closed:** Finite-stage Pick positivity still fails. Paper theta source-transport results now give exact graded prime deletion, zero-Jordan history and a finite-range symmetrizer no-go; the positive cutoff/reflected-current transfer preserves the same reciprocal-zeta resonance rather than a new phase selector.
- **Open:** Derive an all-prime, renormalized **nonlocal** source comparison and degree-uniform history lower bound. It must preserve singular cusp/zero-history data and distinguish finite archimedean poles from the completed divisor.
- **Evidence:** [Finite-prime Pick no-go](../../../../formal/GaloisForLFunctions/RHTower/XiShiftEulerFinitePrimePoleNoGo.lean), [graded admission](../2-fully-proven/theta-prime-deletion-graded-terminal-admission.md), [zero history](../2-fully-proven/theta-compact-inverse-zero-jordan-history.md), [finite-range no-go](../2-fully-proven/theta-cdf-no-finite-range-symmetrizer.md).

## Route candidates

These have a source fragment, receiver or proposed interface, but lack the handoff,
exhaustion or independent source theorem needed for a complete live architecture.
Some are alternative presentations of an active route's existing open problem.

### Find a candidate

[AKC](#candidate-akc) · [APF](#candidate-apf) · [BPC](#candidate-bpc) · [BSH](#candidate-bsh) · [CTF](#candidate-ctf) · [EDQ](#candidate-edq) · [EGC](#candidate-egc) · [EWJ](#candidate-ewj) · [FEL](#candidate-fel) · [GTA](#candidate-gta) · [HCF](#candidate-hcf) · [HDL](#candidate-hdl) · [HJ](#candidate-hj) · [IRK](#candidate-irk) · [JAS](#candidate-jas) · [K-RVM](#candidate-k-rvm) · [MPLF](#candidate-mplf) · [PBM](#candidate-pbm) · [PCS](#candidate-pcs) · [PMP/LPC](#candidate-pmplpc) · [PSRC](#candidate-psrc) · [PTR](#candidate-ptr) · [RFHM](#candidate-rfhm) · [RG-ETA](#candidate-rg-eta) · [RG-HF](#candidate-rg-hf) · [RHist](#candidate-rhist) · [S6F](#candidate-s6f) · [SC](#candidate-sc) · [SEC](#candidate-sec) · [SQB](#candidate-sqb) · [TCD](#candidate-tcd) · [TK](#candidate-tk) · [TMD](#candidate-tmd) · [TQFQ](#candidate-tqfq) · [UEB](#candidate-ueb) · [W1C](#candidate-w1c) · [WBF](#candidate-wbf) · [WS2](#candidate-ws2)

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

- **Closed / available:** Bernstein–Pringsheim collar interface remains. Paper moving-cusp reflection gives a signed-totient boundary source. Lean shows independent prime-depth amplitude rescalings conjugate the Burnol–theta holonomy while changing literal Gram coefficients, so conjugacy-only finite readouts lose source normalization.
- **Open:** Continue the source susceptibility through the critical collar using a coefficient-faithful, potentially singular boundary that retains amplitude gauge and signed cusp phase.
- **Evidence:** [Moving-cusp source, paper](../2-fully-proven/theta-prime-deletion-moving-cusp-dual-source.md), [amplitude-gauge no-go](../../../../formal/GaloisForLFunctions/RHTower/PrimeBurnolThetaAmplitudeGaugeNoGo.lean).

<a id="candidate-bsh"></a>

### BSH

- **Closed / available:** Mate curvature is exactly character curvature times `‖y(j+1)‖²` plus a boundary-ideal multiple, so boundary-multiplier vanishing would force unitary character norm. But explicit reciprocal contraction sections are off-unitary: Boolean full-history contraction, its energy law and either one-sided Sonin contraction cannot prove the mate identity. Ordinary norm/seminorm-closed finite-cut completions also retain the cofinal Gamma defect and cannot manufacture the needed pre-closure factorization.
- **Open:** Construct the literal prime--Gamma section with a source-level mate identity before closure, or use a stronger nonordinary completion retaining the missing factorization.
- **Evidence:** [BSH fact audit](bsh-own-research-facts.md), [earlier mechanism](rh-frontier-reference-2026-09-12.md#candidate-bsh).

<a id="candidate-ctf"></a>

### CTF

- **Closed / available:** Sparse cubic occurrence and critical-scale source floors remain. The tail-`L¹` obstruction now covers every measurable moving family with finite tail norm, with no uniform `L∞` bound, and also every finite-tail array with a summable quantitative `L¹` Cauchy modulus. Escaping boundedness or omitting an explicit limit does not repair the Bose response.
- **Open:** Construct a genuinely tail-`L¹`-noncompact moving array, or prove an all-grade source orientation law. Any surviving array must carry noncompact tail mass rather than converge or be summably Cauchy in tail `L¹`.
- **Evidence:** [Integrable-tail no-go](../../../../formal/GaloisForLFunctions/RHTower/ChronologicalTailL1IntegrableNoGo.lean), [Cauchy no-go](../../../../formal/GaloisForLFunctions/RHTower/ChronologicalTailL1CauchyNoGo.lean), [fact audit](ctf-l1-stability-own-research-facts.md).

<a id="candidate-edq"></a>

### EDQ

- **Closed / available:** Two-log signed-quotient ceiling remains an RH receiver. Physical divisor-closed LCM panels are positive discrepancy squares, but a literal initial prefix is negative (`−45/196`). The centered residue source now has an exact finite DFT/period-covariance Parseval identity, nonzero modes only at reduced denominators `≤N`, and an absolute variance ceiling `N H_N²/12`; the top-frequency band is explicitly classified. These are source-side Fourier ingredients, not the physical-window estimate.
- **Open:** Prove the *retained signed* two-log quotient ceiling, especially fixed-start Möbius-window energy, Mertens-weighted cross-panel cancellation and the incomplete high-LCM boundary. Reduced-Farey/dual-sieve transfer would formalize a paper `o(1)` high-clock improvement, but the existing `O(log N)` error already suffices for the RH receiver; sharper leakage alone is not the bottleneck.
- **Evidence:** [Centered Fourier energy](../../../../formal/GaloisForLFunctions/RHTower/EulerDeletionCenteredSourceFourierEnergy.lean), [spectral support](../../../../formal/GaloisForLFunctions/RHTower/EulerDeletionLiteralResidueSpectralSupport.lean), [variance ceiling](../../../../formal/GaloisForLFunctions/RHTower/EulerDeletionMobiusVarianceHarmonicBound.lean), [panel conservation](../../../../formal/GaloisForLFunctions/RHTower/EulerDeletionCenteredLcmCoprimeConservation.lean), [two-log receiver](../../../../formal/GaloisForLFunctions/RHTower/EulerDeletionTwoLogClockRHEndpoint.lean).

<a id="candidate-egc"></a>

### EGC

- **Closed / available:** The pole-safe inner contour lands on finite Xi-copy rows. The *complete* shifted-residue row is a summable difference of relative resolvent traces, and on source-admissible shifts equals the difference of continued prime–archimedean source values. At centered observation and small positive shift, **every** Xi copy, including a hypothetical off-line one, contributes strictly negative real correction; no nonempty finite cluster cancels internally.
- **Open:** Prove source-side decay or compensated real-part cancellation at noncentered outer observations along a pole-safe cofinal contour. Exact all-copy accounting and centered negativity do not establish a global covariance limit.
- **Evidence:** [Complete source trace](../../../../formal/GaloisForLFunctions/RHTower/XiCauchyPairShiftResidueSourceTrace.lean), [all-copy centered sign](../../../../formal/GaloisForLFunctions/RHTower/XiMeromorphicCauchyPairAllCopyCenteredCorrection.lean), [inner landing](../../../../formal/GaloisForLFunctions/RHTower/XiMeromorphicCauchyPairSourceLanding.lean).

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

- **Closed / available:** The completed safe-displacement Euler--Gamma current and positive averaged Xi-multiplicity transgression remain. Uniform-grid positive packets can have alias tending to zero, so positivity alone gives no variance. A new physical-census bound caps the compact fixed-period alias variance saving at `37/100` of total zero count asymptotically; this particular alias cannot bridge the stated two-thirds-to-three-quarters ceiling gap.
- **Open:** Prove arithmetic anti-equidistribution for the actual boundary packet or find a different, quantitatively stronger source carrier, then transport its positive interval-square budget to the transverse divisor with a cofinal trace ceiling.
- **Evidence:** [Vertical interval source](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmCriticalFeatureVerticalIntervalSourceIncrement.lean), [alias ceiling](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmCriticalFeatureVarianceSavingCeiling.lean), [uniform-grid no-go](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmCriticalFeatureUniformGridAliasNoGo.lean).

<a id="candidate-hdl"></a>

### HDL

- **Closed / available:** The source-work/KL-chirality weld remains one RH receiver. On paper, the literal one-sided Möbius–theta boundary tail has an exact RH-equivalent subpower criterion, shared with L and PSRC; finite critical Abel/Mellin identities do not prove its bound.
- **Open:** Derive signed source cancellation for that causal tail or a singular source-work equality **before** divisor specialization. These formulations relocate, not pay, the arithmetic burden.
- **Evidence:** [Causal paper criterion](../2-fully-proven/causal-mobius-theta-boundary-criterion.md), [source-chirality weld](../../../../formal/GaloisForLFunctions/RHTower/MobiusThetaAdaptiveGreenSourceChiralityWeld.lean).

<a id="candidate-hj"></a>

### HJ

- **Closed / available:** A normalized rational-Hurwitz fibre recovers each `n^s`; modulus-two reflected equality is the first-prime seam and, over all Xi fibres, RH-equivalent. The literal first-prime co-Poisson Mellin residual now realizes that seam with a diagonal-safe factor; its vanishing on all Xi copies is likewise an RH-equivalent receiver.
- **Open:** Prove residual vanishing from an independent arithmetic source law. The literal seed identifies the exact producer obligation but does not establish it.
- **Evidence:** [First-prime seed](../../../../formal/GaloisForLFunctions/RHTower/PrimeTailSeedHurwitzReflection.lean), [Hurwitz seam](../../../../formal/GaloisForLFunctions/RHTower/XiHurwitzRationalFiberSeam.lean).

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

- **Closed / available:** Shifted-theta Gram/moment gates remain. Paper CDF-action network identifies positive conductances and dipole response, but positivity holds in a **grounded** voltage gauge; the Xi quotient uses a decaying-at-infinity gauge differing by a constant outside `ℓ²`. No bounded coercive finite-range Fourier symmetrizer exists for the literal quotient on paper. Generic Riccati/three-charge laws still allow off-real zeros.
- **Open:** Prove the **literal theta** coupled fifth-versus-lower-moment inequality and a global, nonlocal boundary-gauge orientation of the Xi-bearing quotient.
- **Evidence:** [Resistance network, paper](../2-fully-proven/theta-quantile-resistance-network.md), [finite-range no-go, paper](../2-fully-proven/theta-cdf-no-finite-range-symmetrizer.md), [Hermite algebra](../../../../formal/GaloisForLFunctions/RHTower/PrimeArchHermiteMomentBoundary.lean).

<a id="candidate-mplf"></a>

### MPLF

- **Closed / available:** Cofinal Gram remains an RH receiver; bounded forward recovery and local-defect index shortcuts fail. The paper theta zero-history quotient retains every **nonzero** Xi eigenvalue while excluding fixed bounded symmetrization; finite prime translates require a graded or singular carrier. None gives spectral orientation.
- **Open:** Derive packet-uniform cofinal Gram bounds or a singular source transport preserving the **complete** divisor, prime chronology and cross-parameter orientation.
- **Evidence:** [Cofinal Gram classification](../../../../formal/GaloisForLFunctions/RHTower/MeixnerRootPrimeLaplaceCofinalGramClassification.lean), [zero-Jordan quotient, paper](../2-fully-proven/theta-compact-inverse-zero-jordan-history.md), [terminal admission, paper](../2-fully-proven/theta-prime-deletion-graded-terminal-admission.md).

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

- **Closed / available:** Prime-shift residue graph and paper causal RH receiver remain. The finite moving-cusp port recovers the causal tail to superpolynomial accuracy; a hypothetical off-line zero forces a finite-source power-growth witness. Paper theta reflection reduces the primorial observation to the signed largest-prime/sieve-dilation current with superpolynomial nonterminal error. The cutoff/reflected-current transfer has the same reciprocal-zeta resonance, not an independent exclusion law.
- **Open:** Prove source closability, control the finite-clock annular correlation and establish signed subpower cancellation of the directed atom / sieve-dilation port. Finite-source occurrence and nonterminal suppression do not pay it.
- **Evidence:** [Finite moving-cusp criterion](../2-fully-proven/finite-prime-moving-cusp-causal-criterion.md), [positive transfer](../2-fully-proven/theta-chronological-boundary-positive-transfer.md), [primorial transition](../2-fully-proven/causal-mobius-theta-primorial-transition.md).

<a id="candidate-ptr"></a>

### PTR

- **Closed / available:** The co-rotating symbol and charge-sector split now have a Lean pointwise full-complex-jet Gårding bound; this is **not** distributional regularity. Five further Lean no-gos close one-clock stroboscopic `ζ` return, uniformly finite-order prime clusters for the shifted channel, commutative occupation of literal prime cells, any unital commutative quotient of their source algebra, and raw three-prime cyclic trace as an order-insensitive Euler landing. Survivors include an exact prime-cluster top interaction, ordered pair chirality and cubic trace orientation.
- **Open:** Build a source-faithful all-grade weak Maxwell/interface relation on an admitted trace domain, prove subluminal distributional transmission regularity and connect arithmetic prime data to a **fixed local** OAM-diagonal trace—or exhibit a genuinely ordered/nonlocal/driven port with correct pole and confinement. None of these no-gos retires PTR as a whole.
- **Evidence:** [Full-jet bound](../../../../formal/GaloisForLFunctions/RHTower/PhotonicCorotatingFullJetGarding.lean), [source-frame and Euler bridge](ptr-euler-dilation-source-frame.md), [five scoped no-go cards](../5-failed/ptr-single-clock-stroboscopic-return-no-go.md), [prime-cluster](../5-failed/ptr-finite-order-prime-cluster-return-no-go.md), [commutative occupation](../5-failed/ptr-literal-prime-cell-commutative-occupation-no-go.md), [abelianization](../5-failed/ptr-literal-prime-source-abelianization-no-go.md), [cyclic trace](../5-failed/ptr-raw-cyclic-trace-euler-landing-no-go.md).

<a id="candidate-rfhm"></a>

### RFHM

- **Closed / available:** Support/grade carrier and closed literal creators; reversible/source-linear sewing no-gos.
- **Open:** Break inverse covariance or replace literal creation while retaining phase, depth, compounds and a nonzero Xi connecting class.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-rfhm).

<a id="candidate-rg-eta"></a>

### RG-ETA

- **Closed / available:** Finite paired-eta fluxes converge diagonally to the complete heat detector; their vanishing is RH-equivalent. The partner-minus-original prefix sign is another receiver. Dyadic work telescopes exactly and has a sharp positive limit at a hypothetical right-half zero; at multiplicity one, weighted head-cosine work has the opposite sharp negative limit.
- **Open:** Prove an opposing nonpositive or little-o dyadic source bound; control the separate higher-multiplicity cross-correlation. Neither receiver supplies that arithmetic estimate. Subordinate to RG.
- **Evidence:** [Dyadic finite-work audit](rg-eta-dyadic-finite-work.md), [finite flux criterion](../../../../formal/GaloisForLFunctions/RHTower/RiemannGaussian/RiemannXiSuzukiPositiveCriticalStripEtaFiniteArithmeticFluxCriterion.lean).

<a id="candidate-rg-hf"></a>

### RG-HF

- **Closed / available:** Finite Hardy approximants and exact reflection-resultant/phase-dispersion alternatives.
- **Open:** Prove source-pinned finite-to-entire rigidity excluding both alternatives. Subordinate to RG.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-rg-hf).

<a id="candidate-rhist"></a>

### RHist

- **Closed / available:** Big-Witt ambient-norm darkness and positive-observation price escape remain. Paper theta zero-Jordan history shows why a bounded fixed inverse metric cannot read the nonzero Xi divisor while retaining finite prime translations; the zero-history quotient keeps nonzero occurrence but loses literal prime actions in its fixed Hilbert space.
- **Open:** Construct a divisor-independent vector history with singular prime observation, nonescaping reciprocal price and a source-specific **cross-parameter** index law, then exhaust Xi copies.
- **Evidence:** [Zero-Jordan history, paper](../2-fully-proven/theta-compact-inverse-zero-jordan-history.md), [full-inverse Lean no-go](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmThetaZeroHistoryNoGo.lean), [Big-Witt price escape](../../../../formal/GaloisForLFunctions/RHTower/DeningerBigWittCrossPrimeRHistPriceEscape.lean).

<a id="candidate-s6f"></a>

### S6F

- **Closed / available:** Source-proved order-23/24 moments and finite Ward certificates remain. A formal abstract countermodel has strictly positive centered scalar reciprocal traces at **all orders** with an off-axis zero and negative shifted Hankel minor. At paper level fixed finite theta heads change sign behavior after center integration; unintegrated finite-head Hankel diagonals still have infinitely many negative orders.
- **Open:** Prove source-specific **general-packet/cofinal Hankel orientation** and joint cutoff/order control, not merely scalar traces at every order. The completed C5 slope and all-order signed product-kernel inequality remain open.
- **Evidence:** [Scalar all-order no-go](../../../../formal/GaloisForLFunctions/RHTower/XiCenteredScalarTraceAllOrderNoGo.lean), [fixed-head paper asymptotic](theta-center-pair-singularity-condensation.md), [direct order-23 closure](../../../../formal/GaloisForLFunctions/RHTower/PrimeArchMomentTwentyThreeClosure.lean).

<a id="candidate-sc"></a>

### SC

- **Closed / available:** Stokes/Witt descent and all-prime polarized Krein carrier; pointwise unmarked fibres are indistinguishable.
- **Open:** Find a source-fixed signed/indefinite restriction or cross-fibre invariant that preserves Xi landing without universal target fitting.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-sc).

<a id="candidate-sec"></a>

### SEC

- **Closed / available:** The one-ended adjacent-prime seam interface has an exact essential-norm formula: seam-charge jump divided by the positive Euler scale. Both adjacent seam charges vanish along the prime ray at *every* strip point, so even Euler-rescaled asymptotic essential-norm smallness is automatic and nonselective.
- **Open:** Prove actual eventual compactness/equality of seam values, or a stronger source-faithful non-asymptotic selection law. The norm limit cannot replace exact compactness or distinguish an off-line Xi copy.
- **Evidence:** [Adjacent Calkin no-go](../../../../formal/GaloisForLFunctions/RHTower/XiPrimeSeamAdjacentEssentialNormNoGo.lean), [candidate architecture](rh-frontier-reference-2026-09-12.md#candidate-sec).

<a id="candidate-sqb"></a>

### SQB

- **Closed / available:** Compact-resolvent Friedrichs carrier and paper weighted no-radiation occurrence remain. A new paper causal-mode calculation shows every finite prime deletion keeps a two-ended Xi-zero mode while cofinal deletion converges locally to the Gaussian response with **nonzero negative-cusp radiation**; local convergence cannot retain the missing boundary condition. Separately, Γ(N) Eisenstein continuation and its Maass–Selberg identity are now Lean-closed in an absolutely convergent region; critical-line continuation of the pairing and spectral decomposition remain open, so this is infrastructure, not SQB orientation.
- **Open:** Formalize the weighted occurrence/complete-row domain, retain the escaping cusp datum in a singular carrier and orient the determinant-graded arithmetic current to obtain a closed symmetric Xi-bearing operator.
- **Evidence:** [Causal-mode escape, paper](../2-fully-proven/sqb-prime-deletion-causal-mode-escape.md), [SQB–Hedenmalm bridge](sqb-hedenmalm-periodization-dispersion.md), [Γ(N) Maass–Selberg region](../../../../formal/GaloisForLFunctions/RHTower/SelbergMaassSelbergGammaN.lean), [continuation status](selberg-eisenstein-gamma-n-continuation.md).

<a id="candidate-tcd"></a>

### TCD

- **Closed / available:** Literal convolution/full-jet connectors, native D1 and small-cluster positivity remain. The fixed-cutoff paper pair-singularity analysis separates eventually positive **integrated** jets from negative unintegrated finite-head Hankel diagonals; neither limit controls a growing cutoff.
- **Open:** Prove joint cutoff/order source-to-divisor landing and completed C5/general-packet orientation. Native D1 and fixed-head asymptotics do not imply it.
- **Evidence:** [Center-pair paper theorem](theta-center-pair-singularity-condensation.md), [finite-atom order escape](theta-finite-atom-order-escape.md), [earlier architecture](rh-frontier-reference-2026-09-12.md#candidate-tcd).

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

<a id="candidate-tqfq"></a>

### TQFQ

- **Closed / available:** The paper pinned theta quotient has exact Xi occurrence. Its CDF action is now identified on paper with a positive long-range resistance network, but grounded voltage positivity differs from the Xi-bearing boundary gauge by a non-`ℓ²` constant. A finite-range coercive Fourier symmetrizer is ruled out on paper. Finite packet factorization has positive bulk plus a strictly oblique one-port term, and both pieces diverge in norm while their difference stays bounded; a bulk-first bounded-operator limit is impossible. The rational-cusp connection coefficient is computed on paper, without zero-location control.
- **Open:** Formalize these theta Fourier/network laws and prove a **source-specific boundary-gauge orientation** of the full infinite quotient, retaining the singular counterterm and all cross-frequency modes.
- **Evidence:** [Resistance network](../2-fully-proven/theta-quantile-resistance-network.md), [finite-range no-go](../2-fully-proven/theta-cdf-no-finite-range-symmetrizer.md), [quotient and oblique port](theta-quantile-fourier-action-quotient.md), [rational-cusp law](../2-fully-proven/theta-rational-cusp-boundary-law.md).

<a id="candidate-ueb"></a>

### UEB

- **Closed / available:** Translated Xi Bezoutian and all-depth source tangent of negative type.
- **Open:** Prove coefficient-faithful source-tangent landing with the required sign before divisor polarization.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-ueb).

<a id="candidate-w1c"></a>

### W1C

- **Closed / available:** Closed positive-ray weight-one Clifford operator. Its unchanged square has exactly two reflected frequencies per attained energy fibre, **no point spectrum** at any real mass, and no compact resolvent at `i`; the natural Clifford root also has no eigenvectors. Bare discrete-eigenvalue and compact-resolvent Fredholm Xi occurrence are excluded.
- **Open:** Construct a genuinely new arithmetic operator/domain or source-derived scattering denominator and prove its Xi occurrence identity; the free Clifford relation alone supplies no discrete Xi spectrum.
- **Evidence:** [Spectral no-go and exact fibre](../../../../formal/GaloisForLFunctions/RHTower/WeightOneCliffordSpectralNoGo.lean), [failed subroute card](../5-failed/w1c-bare-clifford-eigenvalue-occurrence.md).

<a id="candidate-wbf"></a>

### WBF

- **Closed / available:** Source-normal jet, prime-Poisson fracture and finite Hodge/energy laws.
- **Open:** Prove depth-uniform source-normal completion that annihilates the anomaly and lands in Xi.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-wbf).

<a id="candidate-ws2"></a>

### WS2

- **Closed / available:** Depth-two signed operator and trace-class relocation remain. The paper theta alignment has an exact **Hilbert–Schmidt but non-trace-class** Xi-bearing correction; the resistance-network Schur complement now identifies its conductance/clock one-port. Causal-mode escape shows the missing datum at the negative cusp, not in the local Gaussian limit.
- **Open:** Formalize the alignment and orient the nonlocal determinant/one-port boundary work; no bounded self-adjoint similarity follows from network positivity or determinant equality.
- **Evidence:** [WS2–theta bridge](ws2-theta-cdf-hilbert-schmidt-bridge.md), [network Schur complement](../2-fully-proven/theta-quantile-resistance-network.md), [causal-mode escape](../2-fully-proven/sqb-prime-deletion-causal-mode-escape.md).

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

The complete catalogue contains **all 465 named entries**, not a selected list. Each family
opens a name index followed by one structured result/survivor card per mechanism.
The 17 original-label records above are included in that total; FD2 and RBH also have
their longer architecture verdicts in the reference.

| Browse closed mechanisms | Entries |
|---|---:|
| [Retired original route labels](rh-killed-routes.md#retired-labels) | 17 |
| [CCM-FU: prime scheduling and current bounds](rh-killed-routes.md#ccm) | 37 |
| [E, EDQ, HCF, T1/T2, LI and Estermann: arithmetic cancellation](rh-killed-routes.md#arithmetic) | 62 |
| [HB, FZZ and PW: scattering and physical action](rh-killed-routes.md#scattering) | 98 |
| [Theta, Schur, spectral and positivity mechanisms](rh-killed-routes.md#theta) | 49 |
| [Singular descent, formation and completion](rh-killed-routes.md#completion) | 29 |
| [Ward, Suzuki, prime–Gamma and operator landing](rh-killed-routes.md#ward) | 75 |
| [Analytic roots, multiplicity and regularization](rh-killed-routes.md#roots) | 12 |
| [Other finite, scalar and source-blind selectors](rh-killed-routes.md#other) | 86 |

## Shared infrastructure and unlabelled continuation problems

These are not additional active-route labels. Their value is the exact problem they
remove—or expose—inside the named routes.

### Reflection, ordinate and genus receivers

- **Closed in Lean:** Hermitian reflection fixes precisely critical Xi divisor points. The mod-2 norm image and canonical left-half section are explicit; every finite ordinate window has `#support points=#fixed points+2·#left points`. The trace-form orbit identity supplies a negative monomial witness for an off-line orbit. These are exact support-set receivers, not multiplicity-weighted classical zero counts or sign computations from arithmetic.
- **Qualification:** Reflection-even values agree on partners but may still detect a free orbit. Ordinary free-orbit Tate cocycles are boundaries; a fixed-part genus calculation cannot exclude them. The classical Nevanlinna termwise sign criterion is already present in stronger Hermite–Biehler form in this corpus; the newest termwise witness does **not** create another route.
- **Open:** Compute a source-derived signature/negative index or otherwise prove **free count zero**. Pure counting, discriminant parity, and the Nevanlinna reformulation do not supply the missing prime-side sign.
- **Evidence:** [Boundary-map image](../../../../formal/GaloisForLFunctions/RHTower/BoundaryMapImage.lean), [trace-form orbit sign](../../../../formal/GaloisForLFunctions/RHTower/TraceFormSignature.lean), [Nevanlinna termwise receiver](../../../../formal/GaloisForLFunctions/RHTower/NevanlinnaSignCriterion.lean), [angular-field retraction](angular-energy-quantization.md), [retired genus producer](../5-failed/genus-programme-retired.md).

### Transverse zero network and angular threshold

- **Closed in Lean:** The reciprocal-square zero network and angular/Poisson receivers remain. Each off-line reflection pair contributes exactly one unit of angular energy; paired off-line points force the Poisson potential at their ordinate to reach `2`. Finite-window free-orbit count and the boundary-map image are exact. The Cauchy bump's peak remains `1` while every integrable average scales with its width; a local bound growing with height cannot cross the strict `<2` integer threshold. The normalized influence matrix is exactly stochastic, so strict Dobrushin contraction has no margin.
- **Open:** Obtain a source-derived **uniform** subthreshold bound at every height, or a source-derived trace-form signature computation. The angular, Poisson, local-count and Nevanlinna criteria are receivers; no route gains RH by rephrasing them. The uniform-certificate program's finite-local contraction and mixed-cone SOS/dual shortcuts are closed, but recurrence or a genuinely new arithmetic certificate remains open.
- **Evidence:** [Angular threshold](../../../../formal/GaloisForLFunctions/RHTower/AngularEnergyQuantization.lean), [local count bound](../../../../formal/GaloisForLFunctions/RHTower/LocalCountBound.lean), [scaling degree](../../../../formal/GaloisForLFunctions/RHTower/ScalingDegreeLaw.lean), [stochastic influence](../../../../formal/GaloisForLFunctions/RHTower/ZeroInfluenceStochastic.lean), [uniform-certificate status](uniform-certificate-program.md).

### Cofinal theta sieve: two-sign cusp escape

- **Closed on paper, Lean-pending:** Along finite prime sets increasing through all primes, positive and negative variations of the literal sieved theta source both diverge at the negative cusp, while total signed mass tends to zero. After taking the cofinal limit at each fixed cusp cutoff `R`, the lower scale is `e^{R/2}/R`. Thus no uniformly bounded-total-variation signed-measure or `L¹` boundary limit can perform this source-to-seed passage. This is a topology obstruction, not a sign or RH theorem.
- **Open:** Control the coupled prime–polar–Gamma cancellation in a distributional/trace topology that preserves the divisor, with joint cutoff/rate information if needed. The fixed-`R` lower bound is not a uniform two-parameter asymptotic.
- **Evidence:** [Bidirectional variation and proof status](../2-fully-proven/theta-sieve-bidirectional-cusp-variation.md).

### Theta derivative packets and finite-data blindness

- **Paper-level no-go:** For each fourth-multiple derivative order, a sufficiently small positive deformation `k+t k⁽⁴ᵐ⁾` of the completed theta density preserves all moments below that order and the entire real-zero divisor, yet its Fourier transform gains a symmetric off-real zero packet at radius `t⁻¹ᐟ⁴ᵐ`. Positivity and strong log-concavity of the full deformed density are proved on paper; Lean currently closes only the derivative-polynomial leading sign needed for its tail. Finite moment depth, compact spectral tests and real-zero data alone cannot distinguish the packet.
- **Further closed on paper:** Compact positive theta perturbations can place a zero inside the Xi strip while preserving finite anchors; a positive one-sided Bernstein gauge can keep two anchors and an off-line zero. In contrast, all-prime deletion Bernstein conditions make the **actual** theta source a pure ray, and two prime quantile flows recover its normalized density. These source-fidelity laws expose why finite/one-sided data are insufficient, but do not orient its actual divisor. An endpoint `L¹` harmonic-completeness criterion is RH-equivalent; every `L^p`, `p>1`, analogue has infinite defect even under RH.
- **Still open:** Formalize the paper packet, cone and endpoint results, and derive a theta-specific all-scale **orientation** from literal Euler/modular data. Pure-ray uniqueness and exact occurrence are not positivity of the Xi zero spectrum.
- **Evidence:** [Derivative packet](../2-fully-proven/theta-derivative-dark-divisor-packets.md), [compact strip zero engineering](../2-fully-proven/theta-compact-critical-strip-zero-engineering.md), [pure-ray theorem](../2-fully-proven/theta-prime-deletion-bernstein-pure-ray.md), [endpoint completeness](../2-fully-proven/theta-endpoint-harmonic-completeness.md).

### Theta quantile/CDF cross-frequency transport

- **Closed on paper:** The theta quotient has exact Xi occurrence and singular one-port feedback. Opposite-frequency `2×2` blocks cannot carry the required cross-frequency capacity. Its CDF action is now a positive dipole-response network, but Xi uses a different, non-`ℓ²` boundary gauge. Finite-range coercive symmetrization fails, and finite-packet positive bulk and oblique port each diverge while their difference stays bounded. The theta CDF prime clock still matches the Poisson/Mertens clock only up to a trace-class correction.
- **Open:** Formalize the quotient/network claims and prove a literal-theta, nonlocal orientation of the coupled bulk and singular port. Network positivity, bounded-block reality and clock alignment do not transfer Xi spectral reality.
- **Evidence:** [Resistance network](../2-fully-proven/theta-quantile-resistance-network.md), [finite-range no-go](../2-fully-proven/theta-cdf-no-finite-range-symmetrizer.md), [oblique-port factorization](theta-quantile-fourier-action-quotient.md), [CDF-action capacity](../2-fully-proven/theta-cdf-crossfrequency-rvm-capacity.md).

### Theta Euler completion and boundary chronology

- **Closed on paper:** The older finite-Euler charge escape remains. The exact integer-cutoff/deletion commutator has a uniform cofinal vanishing error for **every** moving prime schedule; its limit is a signed Möbius Gaussian current, not a new chronology phase. Moving-cusp reflection gives a different signed-totient current, but a positive transfer relates their **same** reciprocal-zeta resonance. Lean proves finite reflection/totient inverse identities only; the cofinal transport, sign change and regularity claims are paper-level.
- **Open:** Control the shared signed resonance from an arithmetic law retaining prime coefficients and a singular cusp carrier. Positive transfer and compact-local convergence do not orient the divisor; finite-stage pole ports still require growing-order renormalization.
- **Evidence:** [Commutator collapse](../2-fully-proven/theta-deletion-cutoff-commutator-collapse.md), [moving-cusp dual](../2-fully-proven/theta-prime-deletion-moving-cusp-dual-source.md), [positive transfer](../2-fully-proven/theta-chronological-boundary-positive-transfer.md), [finite Lean duality](../../../../formal/GaloisForLFunctions/RHTower/ThetaFiniteEulerMovingCuspDuality.lean).

### Singular theta metric and differential-pencil interface

- **Closed:** The source-defined closed boundary relation now carries its complete monopole--dipole record, bounded augmented embedding/readout and exact adjoint intertwining. Literal conjugation yields anti-linear Hodge operators on source and boundary carriers with square `-1`; the completed cup form has an explicit positive Hodge diagonal, while its finite boundary correction is represented by one hyperbolic fundamental symmetry. Relation reflection transports nonzero vertical fibres and recovers completed-Xi zero reflection.
- **Killed shortcut:** The singular metric range itself is not closed, so that metric coordinate alone cannot provide the graph topology. The source graph coordinate is genuinely additional data.
- **Still open:** Derive a source-side index, capacity or confinement law exploiting the positive Hodge diagonal while controlling the signature-reversing boundary reflection. Exact adjoint/Hodge/Green structure remains receiver infrastructure; it does not exclude off-line fibres.
- **Evidence:** [Metric pencil](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmThetaMetricPencil.lean), [closed-graph barrier](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmThetaMetricClosedGraphBarrier.lean), [differential pencil](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmThetaSourceDifferentialPencil.lean), [two-port Green law](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmThetaSourceDifferentialGreen.lean).

<a id="hb--theta-cusp-hawking-causal-scattering"></a>

### HB receiver stack after route retirement

- **Closed:** The B2 bulk is now source-explicit: complementary causal branches have total clock `−6`; their product obeys a forced stream equation, its coexact covector is smooth/divergence-free, and every linearized Einstein component is explicit. Full cusp-subtracted forcing and weak response obey literal source reflection. The full Einstein current, master contact and contact-completed angular current are exactly CTP-skew, matching the ordered causal pairing; finite full-kernel Goursat transposition and advanced-source differentiation are also available. Off-line copies retain a nonzero lower-Weyl mixed cusp coefficient, so any boundary transport must remove a literal growing channel.
- **Killed producer:** Group-independent scattering cannot constrain second-sheet poles; the PSL₂(ℤ) arithmetic loop through Hecke positivity, Hecke--Maass--Selberg, Rankin--Selberg, Kuznetsov, Ward stationarity and Hardy/inner--outer formulations yields receivers or RH-equivalent premises. Coefficientwise B2 cancellation is false at Hardy's on-line zeros. HB is therefore retired as an RH route.
- **Still open, receiver-side only:** Prove the complete noncompact ordered two-event functional equals the complementary incoming Einstein current while retaining the explicit full-minus-native lift defect and Weyl finite part. Then identify cap/contact transport at the noncompact boundary. These may complete the physical model but do not restore an independent arithmetic producer.
- **Evidence:** [Ordered physical current](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMLiteralCyclicPeierlsOrderedCurrent.lean), [cross-branch bidegree](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMLiteralCyclicPeierlsCrossBranchBidegree.lean), [source reflection](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFullAngularSourceReflection.lean), [self-mixed cusp flux](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMLiteralCyclicPeierlsSelfMixedCuspFlux.lean), [source audit](fzz-p-rbh-pw-b-ptr-source-facts.md).

### Off-line first moment and large-value selection

- **Closed:** The product approximate-functional-equation chain gives off-line first moment `O(T)`; finite multiplicity/pair-correlation bounds and Montgomery--Taylor `67.25%` simple-critical and `83.62%` distinct-zero lower densities are formal. Any eventual linear upper bound for the nonnegative off-line moment has nonnegative slope. The two-thirds mollified mean-square gate requires `c≥exp(5R/3)`, and the two-gate Levinson consumer cannot yield a negative slope. This excludes RH by this *slope-only consumer*, not density improvement.
- **Open:** Attain the gate floor to seek `o(T)` off-line moment, or obtain a separate **pointwise** rigidity law forcing every zero onto the line. Positive-density and slope bounds do not exclude a sparse off-line set; large-value selection still needs zero-side fluctuation control.
- **Evidence:** [Slope obstruction and gate floor](offline-moment-slope-obstruction.md), [Lean theorem](../../../../formal/GaloisForLFunctions/RHTower/MollifiedGateConstantFloor.lean), [Montgomery--Taylor Xi densities](../../../../formal/GaloisForLFunctions/RHTower/LamzouriMontgomeryTaylorXiDensity.lean).

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

<a id="barbanvehov-and-levinson-energy-diagnostics"></a>

### Barban–Vehov and Levinson energy diagnostics

- **Closed:** Estermann's one-modulus estimate remains nonselective. Selberg Lean now gives Γ(N) Eisenstein continuation at every cusp on `Re s>1/2` away from `1/2,1`, plus the Γ(N) Maass–Selberg pairing in the **absolutely convergent region** `1<Re v<Re u`, `N≥3`, `Y≥1`. This is spectral infrastructure, not RH closure or critical-line pairing.
- **Open:** Obtain signed cancellation **across moduli** and shifted-divisor correlations. For Selberg, continue the truncated pairing to the critical line, handle `s=1/2`, scattering functional equation/unitarity, spectral decomposition and Kuznetsov.
- **Evidence:** [Critical-line-adjacent continuation](../../../../formal/GaloisForLFunctions/RHTower/SelbergEisensteinCriticalLine.lean), [Γ(N) Maass–Selberg region](../../../../formal/GaloisForLFunctions/RHTower/SelbergMaassSelbergGammaN.lean), [Selberg status](selberg-eisenstein-gamma-n-continuation.md).

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

### Xi Laguerre--Pólya and Jensen receivers

- **Closed:** Laguerre--Pólya and all-Jensen-hyperbolicity remain RH receivers. The first Laguerre margin is positive wherever its unit ordinate window contains only on-line copies and `Xi` is nonzero; it is unconditionally nonnegative for `|t|≤58/5`. A threshold-free logarithmic bound counts zero copies in any finite ordinate window. Assuming the first margin is nonnegative, an off-line conjugate pair obeys a quantitative separation lower bound involving local spacing and `log(|t|+4)`.
- **Open:** Derive global Laguerre positivity or Jensen hyperbolicity from an independent arithmetic source, or find an actual negative margin. The window criterion and conditional repulsion merely price an off-line zero; they do not exclude one.
- **Evidence:** [Window and margin](../../../../formal/GaloisForLFunctions/RHTower/XiLaguerreWindowPositivity.lean), [local count](../../../../formal/GaloisForLFunctions/RHTower/XiWindowZeroCount.lean), [separation](../../../../formal/GaloisForLFunctions/RHTower/XiLaguerreSeparation.lean), [audit](xi-local-zero-count-and-laguerre-window.md).

The Hadamard log-derivative gives another exact receiver: RH iff `Re(ξ'/ξ)(s)≥0`
for every `Re s>1/2`. A line-conjugate zero pair has a negative contribution only
inside its explicit off-line disk; positivity is unconditional for `Re s≥1` and
on the proved low-height region, not throughout the critical strip. Full-ordinate
pair averaging loses this local obstruction. The open problem is an independent
arithmetic source law forcing the sign inside the strip, not another reformulation
of the criterion. [Pair law and criterion](xi-hadamard-pair-sign-law.md).

The line-conjugate pair law confines possible negative terms of `Re(ξ'/ξ)`
to zeros within `1/2` in ordinate. Lean now gives unconditional nonnegativity
throughout `Re s>1/2`, `|Im s|≤4`, and for `|Im s|>4` on
`Re s≥1−1/(58 log(|Im s|+1/2))`; `|ξ|` is horizontally nondecreasing on
these regions. This is still short of the RH-equivalent entire right half-strip.
[Sharp positivity and monotonicity](hadamard-positivity-in-strip.md) ·
[formal window law](../../../../formal/GaloisForLFunctions/RHTower/XiHadamardSharpRegion.lean).

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

The register reconciles committed Lean source through the cutoff above. This increment adds
11 scoped no-go records (465 catalogued total), with no new active-route label.
E, STC/CSB/U and theta-operator candidates, PTR, L/PSRC/SQB, CCM-FU, O and BPC have
changed frontiers. Angular-count/signature and uniform-certificate results add receivers
and scoped no-gos, not an independent producer. Γ(N) Maass–Selberg remains spectral
infrastructure. None proves RH.

This is a committed-source and explicitly marked paper-proof audit, not a fresh kernel/dependency validation. No build or generated
check was run. It does not broaden theorem hypotheses or present paper-only arguments as Lean closure. Current source links
support the changed frontiers; historical qualifications remain in the unchanged
[reference snapshot](rh-frontier-reference-2026-09-12.md).
That snapshot also preserves the former executive updates and normalized verdicts;
they are no longer parallel current-status lists.

### Status language

| Term | Meaning |
|---|---|
| Closed / proved | A scoped theorem or obstruction is established at the status stated in its entry: Lean source or explicitly marked paper proof. It is not necessarily an RH-producing theorem. |
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
