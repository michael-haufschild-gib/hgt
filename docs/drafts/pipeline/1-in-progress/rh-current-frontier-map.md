# RH research ledger

**No route proves or disproves RH.** This register separates **24 active routes**,
**37 named candidates**, and **362 closed mechanisms**. “Active” means a formal
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

**Source-audit cutoff: 2026-09-20, `45a84bfa077d5d7b2ff859f5c296c19d1866eef1`.**
Reconciled the 72-file formal-source delta since the prior cutoff
`06ffc635ef27d7e787dc3ca881968b30e5338332` (61 additions and 11 modifications).
No builds, Lean checks, tests, lint or index refresh were run for this ledger update.
Concurrent working-tree source is outside the closed-status audit and is marked **WIP** below.

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

- **Closed:** Complete arity-head energy and insertion charge are exact signed source-pair kernels. At the empty core, entrance energy is the positive rank-weighted diagonal, first-prime charge is the negative rank-weighted prime-shift correlation, and every first insertion is nonpositive. The weighted cutoff diagonal has an exact successor law: unsigned defect covariance plus an explicit positive defect. Fresh-prime deletion is an exact two-scale renewal. Clock-delayed prescribed repayment also closes the old finite-packet budget: halving debt after log-clock `τ` forces inverse-square-root helper mass of exponential size, so the existing exponential-in-mass packet estimate cannot be a global exhaustive budget.
- **Open:** Construct one exhaustive changing-core order with a cancellation-stable relative budget. It must control the positive entrance diagonal, unsigned cutoff defect covariance and nonempty-core signed adjacent-label charge simultaneously, while covering every prime. Local first-step dissipation, sparse histories and fixed finite-family reserves do not give the global orientation or terminal-completed source bound.
- **Evidence:** [Complete-history energy](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorArityHeadCharge.lean), [source-pair kernel](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorArityHeadSourcePairs.lean), [empty-core orientation](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorArityHeadEmptyOrientation.lean), [cutoff diagonal](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorWeightedCutoffDiagonal.lean), [coprime-head deletion](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorCoprimeHeadDeletion.lean), [clock-funding audit](ccm-fu-clock-funding-own-research-facts.md).

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

- **Closed:** Fixed/free trace split, central-band certification and equivalent passivity/moment receivers remain exact; subcritical finite-prefix schedules still fail cofinally. The shared D2/Q source is now explicit: Q reads an oblique projection of `completedPrimeGammaFlux`. A lower bound for its real component alone cannot imply Q passivity because transverse imaginary flux can reverse the sign.
- **Open:** Prove D2's genuinely infinite source lower bound above the critical depth envelope. Any cross-route producer for Q must additionally control the phase/oblique projection; a real-part-only D2 estimate is not enough.
- **Evidence:** [D2--Q oblique flux](../../../../formal/GaloisForLFunctions/RHTower/PrimeArchD2QObliqueFlux.lean), [subcritical finite-prefix obstruction](../../../../formal/GaloisForLFunctions/RHTower/PrimeArchFinitePrefixSubcriticalScheduleNoGo.lean); [earlier architecture](rh-frontier-reference-2026-09-12.md#source-line-752).

<a id="e--squarefree-wold-transport"></a>

### E — squarefree Wold transport

- **Closed:** Marker supply, endpoint reversal, singleton factorization and the sign-complete finite degree/variance law remain exact. In the all-nonunit inactive-factor subclass, a finite receiver cap automatically supplies the formerly assumed activation exponent `K = log₂ U + 1`; under `W^55 < L^30`, a sufficiently long singleton history cannot have five distinct physical receiver slots.
- **Open:** Handle inactive units, other occupancy patterns and the signed covariance/physical shell mass. Alternatively beat the classical `M²` Farey-density term using moving-cusp weights or Möbius structure and transport the gain through finite energy and Mellin continuation. Automatic activation closes one hypothesis only; it does not orient the cofinal source.
- **Evidence:** [Automatic activation exponent](../../../../formal/GaloisForLFunctions/RHTower/RouteEAutomaticActivationExponent.lean), [degree and variance](../../../../formal/GaloisForLFunctions/RHTower/RouteESignCompletePhysicalDegree.lean), [source Farey large sieve](../../../../formal/GaloisForLFunctions/RHTower/Sieve/KloostermanSourceFareyLargeSieve.lean), [normalizer circularity](rh-killed-routes.md#no-go-026).

<a id="fzz-p--parity-delay-mellin-orientation"></a>

### FZZ-P — parity-delay Mellin orientation

- **Closed:** Literal neutral cross-depth covariance is genuinely complex off its phase nodes, and opposite external-BRST holonomies multiply to one, so neutral compact integration preserves that orientation. The external-BRST modulus zero locus is exactly the radial selection condition. But every finite or nested all-depth real factorized accumulation is a nonnegative Hermitian Gram square; every real exchange-symmetric kernel has zero imaginary part; a single charged external branch averages to zero; and the literal two-mark OPE/contact source is exchange-symmetric. These close factorized, scalar, symmetric and local two-mark orientation shortcuts.
- **Open:** Derive the full integrated mixed replica–momentum Ward identity with a source-fixed ordered or nonfactorized complex cross-depth kernel. The minimal algebraic survivor is exchange-antisymmetric, but the worldsheet source must produce it before integration while retaining screening, counterterms, normalization and charge weights.
- **Evidence:** [Cross-depth coherence](../../../../formal/GaloisForLFunctions/RHTower/FZZCigarNeutralRadialCrossDepthCoherence.lean), [neutral external-BRST bridge](../../../../formal/GaloisForLFunctions/RHTower/FZZCigarParityExternalBRSTNeutralPairCrossDepth.lean), [all-depth Gram no-go](../../../../formal/GaloisForLFunctions/RHTower/FZZCigarParityCrossDepthAllDepthFactorizedGramNoGo.lean), [symmetric-kernel survivor](../../../../formal/GaloisForLFunctions/RHTower/FZZCigarParityCrossDepthSymmetricKernelNoGo.lean), [single-branch no-go](../../../../formal/GaloisForLFunctions/RHTower/FZZCigarParityExternalBRSTSingleBranchAngularNoGo.lean), [two-mark exchange no-go](../../../../formal/GaloisForLFunctions/RHTower/FZZCigarParityTwoMarkedSourceExchangeNoGo.lean), [source audit](fzz-p-rbh-pw-b-ptr-source-facts.md).

<a id="g--ward-orientation"></a>

### G — Ward orientation

- **Closed:** All-phase Sonin occurrence and prior scalar/isometric obstructions remain exact. A new source-side Walsh lift removes all inter-cell interference before realification: normalized fibre energy is exactly the sum of literal marked completed-source rectangle energies, and the annulus producer is their exact cellwise sum.
- **Open:** Prove the required sign/order for those literal cell annuli and pass it cofinally with integrability uniform in the source family. Walsh orthogonality diagonalizes the bookkeeping; it does not orient each completed prime--polar--Gamma cell or lower the critical source cost.
- **Evidence:** [Walsh source producer](../../../../formal/GaloisForLFunctions/RHTower/XiWardWalshSourceProducer.lean), [all-phase Sonin carrier](../../../../formal/GaloisForLFunctions/RHTower/SoninCofinalComplexPhaseGlobalCarrier.lean), [cofinal-isometry no-go](../../../../formal/GaloisForLFunctions/RHTower/EulerPreScalarGammaCofinalSoninIsometryNoGo.lean), [scalar-shorting no-go](../../../../formal/GaloisForLFunctions/RHTower/XiWardCubicScalarShortingNoGo.lean); [earlier architecture](rh-frontier-reference-2026-09-12.md#source-line-866).

<a id="hc--horizontal-collision-charge"></a>

### HC — horizontal collision charge

- **Closed:** Horizontal charge/conservation, confluent source current and multiplicity-sensitive receiver geometry.
- **Open:** Construct signed off-diagonal cancellation with a singular or unbounded source-to-Gauss–Hodge comparison preserving labels, multiplicity, orientation and wall residue.
- **Evidence:** [Architecture, precise hypotheses and source references](rh-frontier-reference-2026-09-12.md#source-line-2170).

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

- **Closed:** Safe-chamber positive curvature, affine/Sonin source transport and exact critical Ward landing.
- **Open:** Carry safe-chamber order through the singular correction with a source-framed non-Hilbert estimate retaining the conormal residue.
- **Evidence:** [Architecture, precise hypotheses and source references](rh-frontier-reference-2026-09-12.md#source-line-878).

<a id="o--restricted-weil-ground-and-genus-lag-order"></a>

### O — restricted-Weil ground and genus-lag order

- **Closed:** The literal common-age and relative-clock channels now satisfy a coefficient-faithful homogeneous wall transgression: completed polar--Gamma forcing cancels exactly. Fixed heads have an exact Volterra common-clock envelope; for canonical moving cutoffs, every entering arithmetic collar is nonpositive and the full prime-power common-clock charge is bounded above by the smooth channel. A fourth-order-cancelling two-offset affine repair also subtracts a strictly positive endpoint debt and leaves historical prime--polar interaction unchanged.
- **Open:** Prove coercivity/nonexpansion from the already-admitted literal joint block, equivalently a source lower bound strong enough to pay full displacement debt. New-entry counting, two-offset endpoint repair and smooth Gamma normalization cannot supply it. The exact von Mangoldt remainder remains the load-bearing source.
- **Evidence:** [Wall transgression](../../../../formal/GaloisForLFunctions/RHTower/CCMRestrictedWeilPoleParityWallTransgression.lean), [wall closure](../../../../formal/GaloisForLFunctions/RHTower/CCMRestrictedWeilPoleParityWallClosure.lean), [moving common-clock envelope](../../../../formal/GaloisForLFunctions/RHTower/CCMRestrictedWeilPoleParityCommonClockEnvelope.lean), [two-offset endpoint no-go](../../../../formal/GaloisForLFunctions/RHTower/CCMActualHeadMatchedQuantileTwoOffsetEndpointNoGo.lean), [route audit](route-o-whole-connes-closure-audit.md).

<a id="p--paired-primegamma-signed-exterior-wall"></a>

### P — paired prime–Gamma signed exterior wall

- **Closed:** Every active prime-power pair has nonzero forward zero-clock P-G186 support, while reverse chronology vanishes: the finite carrier is all-path and ordered. The full SP-E strict-cross payload is an exact five-profile matrix (`w`, `wd`, `wc`, `wdc`, `wd²`), inserted through literal P incidence with an exact double-sum formula. Its five-channel Krein form is the pullback of two Julia blocks and has an explicit source radical. The terminal coordinate is strictly timelike, has exact additive cutoff control and necessarily escapes every bounded/Bessel carrier.
- **Open:** Build a graph-closed cofinal P action that transports both Julia blocks while preserving the source radical as gauge, the separate terminal connection, labels and order. Then prove the non-Bessel/non-nuclear bound and completed Xi/theta divisor landing. Finite all-path incidence and exact factorization remove carrier ambiguity; they do not supply the cofinal estimate.
- **Evidence:** [Zero-clock history density](../../../../formal/GaloisForLFunctions/RHTower/RoutePJuliaKreinZeroClockHistoryDensity.lean), [full cross-current history](../../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePFullCrossCurrentHistory.lean), [five-channel factorization](../../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePFiveChannelKreinFactorization.lean), [terminal Lorentz cone](../../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszTerminalLorentzCone.lean), [exterior congruence](../../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePExteriorCurrentCongruence.lean).

<a id="pw-b--recoildeninger-ward-transmutation"></a>

### PW-B — recoil/Deninger Ward transmutation

- **Closed:** Exact recoil/FZZ/Ward imbalance equivalence, original current adjoint and admitted fixed-Mellin identity; literal global dual-mass bound excluded. Every inversion-closed extension of finite physical energy support now contains the minimal reciprocal completion and its infinite reciprocal tail, and the forced reciprocal map realizes both Mellin-grade reflection identities globally.
- **Open:** Derive that reciprocal completion from a literal Hawking closed-time-path source seam while retaining finite-energy contacts, then prove source-derived fixed-grade partner balance and Xi occurrence. Support geometry alone is not a physical seam or reflection theorem at all complex grades.
- **Evidence:** [Reciprocal-energy completion](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekReciprocalCompletion.lean); [earlier architecture](rh-frontier-reference-2026-09-12.md#source-line-2039).

<a id="q--exterior-paired-value-passivity"></a>

### Q — exterior paired-value passivity

- **Closed:** Pairing every reciprocal-square atom with its line-conjugate gives an exact phase formula and nonnegative central response. Joined to the order-23 exterior overlap, the source statement covers the positive paired diagonal without a gap through `Re z = 1047/100`, for `0 < Im z < 1/2` away from a zeta pole/zero. Q remains an oblique complex-flux observable, so a D2 real-part bound alone still cannot imply passivity.
- **Working-tree WIP (not promoted):** The new central-phase leaf has uncommitted proof-only elaboration edits and an untracked algebra-extraction dependency. Its theorem statements are included in the committed-source audit, but this tree state was not checked.
- **Open:** Extend paired-diagonal nonnegativity beyond `1047/100` cofinally across the full pole-free upper strip, or produce a pole witness. The remaining source law must orient complex phase, not only real flux.
- **Evidence:** [Central phase pairing](../../../../formal/GaloisForLFunctions/RHTower/PrimeArchCentralPairedDiagonalPhase.lean), [order-23 exterior overlap](../../../../formal/GaloisForLFunctions/RHTower/PrimeArchPositivePairedDiagonalExteriorOverlap.lean), [D2--Q oblique flux](../../../../formal/GaloisForLFunctions/RHTower/PrimeArchD2QObliqueFlux.lean).

<a id="rg--gaussian-arithmetic-and-suzuki-transport-positivity"></a>

### RG — Gaussian arithmetic and Suzuki transport positivity

- **Closed:** Gaussian explicit formula/heat transport and the Suzuki origin/first-tail barrier remain exact. At every real spectral Xi node, the exact carrier density tends to zero on the punctured line; at a simultaneous Xi/derivative zero its literal totalized value is `1/4`, so that representative is not continuous.
- **Working-tree WIP (not promoted):** A one-point removable patch is now source-written; it is a.e. equal to the literal density and continuous at every real spectral node. The edited proof was not checked.
- **Open:** Prove unbounded good Gaussian widths uniformly in center or signed control through every Suzuki prefix/seam. Any RG-HF compactness argument must choose and justify an a.e. representative separately from endpoint regularity; local repair does not supply global source orientation.
- **Evidence:** [Real-node carrier-density no-go](../../../../formal/GaloisForLFunctions/RHTower/RiemannGaussian/RiemannXiSuzukiCarrierRealNodeDensityNoGo.lean); [earlier architecture](rh-frontier-reference-2026-09-12.md#source-line-2194).

<a id="sp-e--signed-prime-dilation-versus-continuum"></a>

### SP-E — signed prime dilation versus continuum

- **Closed:** The complete prime-power history is exactly `− orientation ledger − displacement debt`; equivalently it is the matched-centroid variance minus the equal-mass quantile-centroid variance. Every fixed local covariance-history coordinate diverges to `+∞` along prime cutoffs, so no finite stationary/local history family can carry the cofinal source. The full current nevertheless has the exact finite five-channel P factorization and terminal Lorentz endpoint described above.
- **Working-tree WIP (not promoted):** The centroid-variance identity is in a new untracked source leaf and an edited fact log; it was not checked. The committed orientation-ledger identity and all-history growth no-go are promoted.
- **Open:** Prove a source-derived cofinal inequality between the two physical centroid variances, or equivalently control the orientation ledger relative to debt, inside a graph-closed P action. A fixed adjacent-gap kernel and separate local prime-power cancellation are now the wrong targets.
- **Evidence:** [History ledger](../../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszPrimePowerHistoryLedger.lean), [all-history growth no-go](../../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszCovarianceKernelAllHistoryGrowthNoGo.lean), [WIP variance identity](../../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszPrimePowerHistoryVariance.lean), [fact audit](sp-e-own-research-facts.md).

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

- **Closed:** Each ordered stationary rapidity pair has opposite first and second curvature, zero signature and a positive real amplitude—no Maslov sign. The anti-ordered pair survives every multiplier nonzero near the diagonal, closing regular fixed-diagonal-germ cutoffs. Its phase is positive but compresses to zero when the inner frequency is `o(sqrt u)`, so it is not dispersive. The finite Abel line-bound survivor remains RH-equivalent rather than an independent producer.
- **Open:** Prove signed nonlocal prime-frequency cancellation for the full finite covariance, or derive source order support excluding anti-ordered saddles. Local stationary phase, fixed-width localization and regular diagonal multipliers cannot do this.
- **Evidence:** [Saddle polarity](../../../../formal/GaloisForLFunctions/RHTower/XiMassTwoRapiditySaddlePolarity.lean), [stationary phase](../../../../formal/GaloisForLFunctions/RHTower/XiMassTwoRapidityStationaryPhase.lean), [diagonal-germ no-go](../../../../formal/GaloisForLFunctions/RHTower/XiMassDiagonalGermStationaryNoGo.lean), [fact audit](route-t-saddle-polarity-facts.md).

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

- **Closed / available:** Boolean Sonin full-history/mate interface.
- **Open:** Construct the literal prime–Gamma section and prove mate-boundary vanishing.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-bsh).

<a id="candidate-ctf"></a>

### CTF

- **Closed / available:** Sparse cubic Gamma–zeta occurrence, harmonic-charge removal and critical-scale source floors.
- **Open:** Construct a moving/nonperturbative bounded array with persistent correction and vanishing full error, or an all-grade source orientation law.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-ctf).

<a id="candidate-edq"></a>

### EDQ

- **Closed / available:** Every physical parent fibre is the disjoint union of genuine successor fibres, parent mass is their exact sum, and child predictable drift has zero weighted mean. The child Dirichlet form is an exact pairwise quadratic form in signed source--cofactor contrasts; at terminal depth it becomes a weighted pairwise form in literal chronological innovation tails and physical Möbius cells. The physical EDQ energy is asymptotically negligible relative to uniform complete-period variance, closing uniform-period substitution as a proof strategy.
- **Open:** Prove a cofinal polylogarithmic estimate for the beta-weighted signed child contrasts/innovation tails and sum the complete quotient tail. The exact child decomposition identifies the cancellation coordinates; it does not bound them. Uniform period averaging loses precisely the physical cancellation needed.
- **Evidence:** [Child-fibre contrast](../../../../formal/GaloisForLFunctions/RHTower/EulerDeletionChildFibreContrast.lean), [energy/period separation](../../../../formal/GaloisForLFunctions/RHTower/EulerDeletionEnergyPeriodSeparation.lean), [non-clock lcm bridge](../../../../formal/GaloisForLFunctions/RHTower/EulerDeletionNonclockLcmTailBridge.lean), [truncated-divisor correlation](../../../../formal/GaloisForLFunctions/RHTower/EulerDeletionTruncatedDivisorPairCorrelation.lean).

<a id="candidate-egc"></a>

### EGC

- **Closed / available:** Rational collision-safe covariance with exact finite diagonal correction and source-first landing.
- **Open:** Construct pole-safe nested source contours and prove normalized cofinal covariance vanishing.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-egc).

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

- **Closed / available:** Source Plemelj/alias control, phase selection, five-center density receiver and shrinking-shell detector.
- **Working-tree WIP (not promoted):** A new untracked source leaf proves that horizontal zero crossings contribute a real logarithmic pole, so the scalar imaginary-density source erases the entire multiplicity residue. No build or source check was run.
- **Open:** Prove the source-majorant ceiling 21/100, a compact phase-average gate, or a height-summed cross-scale frame budget. Density improvement is not full RH.
- **Evidence:** [WIP horizontal-pole blindness](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmCriticalFeatureSourceHorizontalPoleBlindness.lean), [exact mechanism and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-hcf).

<a id="candidate-hdl"></a>

### HDL

- **Closed / available:** Prime-normal half-density and exact double-log residue/codiagonal classifier.
- **Open:** Construct a singular/noncontinuous or quotient differential retaining provenance; continuous same-space annihilation also kills the source.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-hdl).

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

- **Closed / available:** Prime-indexed signed relocation and exact target-side reciprocal-Xi spectral constraints.
- **Open:** Recover carrier, eigenbasis and determinant from prime source without importing ordered zero ordinates.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-k-rvm).

<a id="candidate-mplf"></a>

### MPLF

- **Closed / available:** Complete prime-Laplace frame and finite Gram interpolation.
- **Open:** Derive uniform source Gram bounds and pass cofinally.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-mplf).

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

- **Closed / available:** Prime clocks realize the exact infinite Deninger sideband measure, while one global clock and finite uncoupled clock arrays are impossible. The prime monodromy first jet is the parabolic transfer only in a prime-dependent frame; scalar and positive-metric realizations are excluded. A genuine non-scalar prime two-slab cycle exists, and a literal source-free temporal-Maxwell plane-wave model with positive permeability/permittivity realizes that cycle and its parabolic two-cycle transfer. Clock-to-cover phase, calibrated detuning, helical coefficient, OAM selection and conservative three-channel port flow are exact. Finite closed Floquet truncation is impossible without a boundary-dark mode; the infinite complex-PTC multiplier is exactly `p^(1/2-s)` and its global Xi moderation is already RH-equivalent.
- **Open:** Derive the rotating/OAM infinite-ladder amplitude law from the literal Maxwell temporal-boundary problem, or prove the required modal-overlap boundary-dark law, then establish an independent defect-confinement source theorem. The homogeneous two-slab Maxwell transfer closes physical occurrence of the finite parabolic layer, not the infinite conormal ladder or confinement.
- **Evidence:** [Prime-clock lattice](../../../../formal/GaloisForLFunctions/RHTower/PhotonicPrimeClockDeningerLatticeNoGo.lean), [parabolic jet bridge](../../../../formal/GaloisForLFunctions/RHTower/DeningerPhotonicParabolicJetBridge.lean), [cyclic slab realization](../../../../formal/GaloisForLFunctions/RHTower/PhotonicPrimeCyclicSlabParabolicRealization.lean), [temporal-Maxwell realization](../../../../formal/GaloisForLFunctions/RHTower/PhotonicTemporalMaxwellSlabRealization.lean), [source audit](fzz-p-rbh-pw-b-ptr-source-facts.md).

<a id="candidate-rfhm"></a>

### RFHM

- **Closed / available:** Support/grade carrier and closed literal creators; reversible/source-linear sewing no-gos.
- **Open:** Break inverse covariance or replace literal creation while retaining phase, depth, compounds and a nonzero Xi connecting class.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-rfhm).

<a id="candidate-rg-eta"></a>

### RG-ETA

- **Closed / available:** Actual finite flux approximation, sharp lower-prefix removal and exact top-order coupled term.
- **Open:** Bound the retained coupled prefix at square-root scale through anti-alignment, not separate component size. Subordinate to RG.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-rg-eta).

<a id="candidate-rg-hf"></a>

### RG-HF

- **Closed / available:** Finite Hardy approximants and exact reflection-resultant/phase-dispersion alternatives.
- **Open:** Prove source-pinned finite-to-entire rigidity excluding both alternatives. Subordinate to RG.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-rg-hf).

<a id="candidate-rhist"></a>

### RHist

- **Closed / available:** Source-history completion, escape classification and exact affine Xi-residue landing remain exact. The literal two-repair scalar source admits a positive norm-dark finite history exactly on the critical line. A genuine normalized Big-Witt cross-prime row is norm-dark, but every continuous positive observer retaining a fixed response--price gap forces price to escape to infinity.
- **Open:** Construct a divisor-independent **vector** polarized history with a singular/noncontinuous observation law and nonescaping reciprocal price, then exhaust Xi copies. Scalar positive repair pairs and ambient continuous finite-price observers are closed.
- **Evidence:** [Positive repair-pair classification](../../../../formal/GaloisForLFunctions/RHTower/XiCanonicalRepairPairPositiveDarkHistoryNoGo.lean), [Big-Witt price escape](../../../../formal/GaloisForLFunctions/RHTower/DeningerBigWittCrossPrimeRHistPriceEscape.lean), [earlier mechanism](rh-frontier-reference-2026-09-12.md#candidate-rhist).

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

- **Closed / available:** Hyperbolic finite-deck gradient density is exactly modular invariant and the full comparison strip costs at most twice fundamental-domain energy. Cell-local Poincaré, scalar witness-line tensorization and one common witness for every finite deck coordinate are formal. Smooth positive height retraction gives global `C¹` representatives; product-grid witnesses have a mesh-squared energy error, and every resulting deck-valued grid step lies in one fixed finite-dimensional cell-constant subspace. This supplies the correct replacement for the invalid 2D vertex grid.
- **Working-tree WIP (not promoted):** `MaassFiniteDeckCoreWitness.lean` has one uncommitted proof-only simplification in the grid-step representative theorem. It was not checked.
- **Open:** Convert the product-grid witness budget into the actual bounded-core `DeckL2` approximation uniformly on the form-norm unit ball, prove total boundedness, and splice with cusp-tail control for compact embedding/resolvent. Spectral selection, Satake factorization and symmetric-power lifts remain downstream.
- **Evidence:** [Rellich energy core](../../../../formal/GaloisForLFunctions/RHTower/MaassFiniteDeckRellichCore.lean), [global/grid witnesses](../../../../formal/GaloisForLFunctions/RHTower/MaassFiniteDeckCoreWitness.lean), [witness-line Poincaré](../../../../formal/GaloisForLFunctions/HTGeometry/WitnessLinePoincare.lean), [grid decomposition](../../../../formal/GaloisForLFunctions/HTGeometry/RectangleGridDecomposition.lean), [mechanism audit](new_scientific_knowledge/sqb-two-cell-witness-line-rellich-bridge.md).

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

The complete catalogue contains **all 362 named entries**, not a selected list. Each family
opens a name index followed by one structured result/survivor card per mechanism.
The 17 original-label records above are included in that total; FD2 and RBH also have
their longer architecture verdicts in the reference.

| Browse closed mechanisms | Entries |
|---|---:|
| [Retired original route labels](rh-killed-routes.md#retired-labels) | 17 |
| [CCM-FU: prime scheduling and current bounds](rh-killed-routes.md#ccm) | 26 |
| [E, EDQ, HCF, T1/T2 and LI: arithmetic cancellation](rh-killed-routes.md#arithmetic) | 41 |
| [HB, FZZ and PW: scattering and physical action](rh-killed-routes.md#scattering) | 75 |
| [Theta, Schur, spectral and positivity mechanisms](rh-killed-routes.md#theta) | 32 |
| [Singular descent, formation and completion](rh-killed-routes.md#completion) | 28 |
| [Ward, Suzuki, prime–Gamma and operator landing](rh-killed-routes.md#ward) | 53 |
| [Analytic roots, multiplicity and regularization](rh-killed-routes.md#roots) | 10 |
| [Other finite, scalar and source-blind selectors](rh-killed-routes.md#other) | 80 |

## Shared infrastructure and unlabelled continuation problems

These are not additional active-route labels. Their value is the exact problem they
remove—or expose—inside the named routes.

<a id="hb--theta-cusp-hawking-causal-scattering"></a>

### HB receiver stack after route retirement

- **Closed:** The pulse-layer source, Maass--Selberg model, resonant-state/Hecke receivers and partner-angle tilt remain exact. The B2 principal-square detector now gives every off-line Xi copy a reflected left-half representative whose normalized principal-square norm has a positive limit and is eventually bounded below by half its dominant coefficient. Any actual boundary transport must retain that growth rate; it cannot land in a genuinely lower-order term.
- **Killed producer:** Group-independent scattering cannot constrain second-sheet poles; the PSL₂(ℤ) arithmetic loop through Hecke positivity, Hecke--Maass--Selberg, Rankin--Selberg, Kuznetsov, Ward stationarity and Hardy/inner--outer formulations yields receivers or RH-equivalent premises. Coefficientwise B2 cancellation is false at Hardy's on-line zeros. HB is therefore retired as an RH route.
- **Still open, receiver-side only:** Transport the principal growth detector through the complete metric current/cap, dominate the escaping pulse image, justify differentiated noncompact cap transport, upgrade the weak cap to a strong Goursat field and identify the lift defect with `contactField`. These may complete the physical model but do not restore an independent arithmetic producer.
- **Evidence:** [Principal growth detector](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMLiteralCyclicPeierlsPrincipalGrowthDetector.lean), [Maass--Selberg model](../../../../formal/GaloisForLFunctions/RHTower/EisensteinMaassSelbergLineModel.lean), [resonant Hecke moments](../../../../formal/GaloisForLFunctions/RHTower/EisensteinHeckeSecondMoment.lean), [pulse layer](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMLiteralCyclicPeierlsPulseLayer.lean), [producer audit](hb-producer-conjecture-loop.md).

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
