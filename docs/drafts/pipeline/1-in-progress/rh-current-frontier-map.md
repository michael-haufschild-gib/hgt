# RH research ledger

**No route proves or disproves RH.** This register separates **25 active routes**,
**37 named candidates**, and **324 closed mechanisms**. “Active” means a formal
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

**Source-audit cutoff: 2026-09-16, `e876f08380382e6380c9d063c28c4cc057e2a526`.**
Reconciled the 107-file formal delta since `c65e250f973631df9cc59552bf8498bf99975290`
(90 additions and 17 modifications, including import umbrellas). Uncommitted work is
outside this audit. No builds, Lean checks, tests, lint or index refresh were run.

## Active routes

### Find a route

| Family | Active routes |
|---|---|
| Current, Ward and prime–Gamma | [CCM-FU](#ccm-fu--completed-current-and-fixed-aperture-suzuki-checkpoint), [D2](#d2--continued-primearchimedean-free-sector-passivity), [G](#g--ward-orientation), [MSC](#msc--möbius--sonin-affine-critical-boundary-renormalization), [P](#p--paired-primegamma-signed-exterior-wall), [SP-E](#sp-e--signed-prime-dilation-versus-continuum) |
| Arithmetic cancellation | [E](#e--squarefree-wold-transport), [T1](#t1--theta-tail-core-current), [T2](#t2--natural-abel-singular-wold-divisor), [HC](#hc--horizontal-collision-charge), [LI](#li--finite-paired-li-prime--gamma-order) |
| Weil, theta and paired positivity | [C1](#c1--class-space-quotient-and-global-weil-positivity), [O](#o--restricted-weil-ground-and-genus-lag-order), [Q](#q--exterior-paired-value-passivity), [CLG/TTF](#clgttf--completed-theta-bezoutian-no-escape), [SV2](#sv2--suzuki-projective-limit-and-shifted-kernel-inertia) |
| Cofinal source comparison | [STC](#stc--exterior-sonin-seam-coherence), [CSB](#csb--cofinal-bernstein-sourcetarget-comparison), [U](#u--adaptive-shifted-xi-hankel-frontier-renewal), [RG](#rg--gaussian-arithmetic-and-suzuki-transport-positivity) |
| Singular descent | [CDC](#cdc--constitutive-dagger-confluence), [L](#l--singular-greenbv-to-physical-descent) |
| Nonlinear scattering | [HB](#hb--theta-cusp-hawking-causal-scattering), [FZZ-P](#fzz-p--parity-delay-mellin-orientation), [PW-B](#pw-b--recoildeninger-ward-transmutation) |

Routes are alphabetical below. The family index is a navigation aid, not an exhaustive
dependency graph.

<a id="c1--class-space-quotient-and-global-weil-positivity"></a>

### C1 — class-space quotient and global Weil positivity

- **Closed:** Finite adelic trace, positive global-mean completion, nuclear-root budget obstruction and reflection-twisted Weil target.
- **Open:** Construct source-to-Weil incidence outside the excluded nuclear-root ideal, then prove cofinal positivity. The isolated first-trace question cannot restore the killed all-moment producer.
- **Evidence:** [Architecture, precise hypotheses and source references](rh-frontier-reference-2026-09-12.md#source-line-724).

<a id="ccm-fu--completed-current-and-fixed-aperture-suzuki-checkpoint"></a>

### CCM-FU — completed current and fixed-aperture Suzuki checkpoint

- **Closed:** Completed current, affine/Gamma source sewing, matched PNT rate and existing RH receivers remain exact. Actual matched polar coverage now has a finite adjacent-codiagonal normal form. Its constant mode vanishes, while its first mass mode equals completed node error plus a forced nonnegative endpoint excess; endpoint renormalization recovers the completed error exactly. A literal Suzuki resolvent carries positive graph energy and has an exact Green-boundary quotient, but its closure component is not orthogonal to the spectral vector. Contiguous two-sided cancellation around a large prime needs combined logarithmic reach; every sublogarithmic schedule fails cofinally. Scalar rectangular-Euler inversion is also closed: an unbounded affine quadratic source has uniformly bounded response.
- **Open:** Bound the signed adjacent-codiagonal pairing with the actual nonconstant translation-defect/autocorrelation profile, or prove an equivalent signed growing-range source estimate. Any viable transport must be nonlocal at least on logarithmic scale (or noncontiguous), preserve the closure--source cross term, and retain prime--polar cancellation. Absolute, scalar, fixed/sublogarithmic-memory and orthogonal-split repairs are closed.
- **Evidence:** [Adjacent codiagonal](../../../../formal/GaloisForLFunctions/RHTower/CCMActualHeadMatchedQuantilePolarAdjacentCodiagonal.lean), [two-sided range obstruction](../../../../formal/GaloisForLFunctions/RHTower/CCMFUSuzukiCriticalBidirectionalTransportRangeNoGo.lean), [rectangular-Euler no-go](../../../../formal/GaloisForLFunctions/RHTower/CCMFUSuzukiRectangularEulerNoGo.lean), [actual resolvent energy](../../../../formal/GaloisForLFunctions/RHTower/SuzukiTaActualResolventHerglotzEnergy.lean), [Green-boundary quotient](../../../../formal/GaloisForLFunctions/HTGeometry/DeficiencyResolventBoundaryQuotient.lean), [critical remainder variation criterion](../../../../formal/GaloisForLFunctions/RHTower/CCMFUSuzukiCriticalRemainderVariation.lean); [earlier architecture](rh-frontier-reference-2026-09-12.md#source-line-340).

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

- **Closed:** Fixed/free trace split, central-band certification through 141858/10000 and equivalent passivity/moment receivers. Every height-dependent finite von Mangoldt prefix with eventual `c·depth^(3/4) ≤ log(height)` for any `c>42` still has cofinally unbounded-below D2 defect; the exact critical envelope and its slack are formal.
- **Open:** Prove one common source-side lower bound for the genuinely infinite pure-prime log-height defect above that threshold, or an interior-window lower bound using a schedule beyond the new critical depth envelope. Boundary control and subcritical finite schedules are insufficient.
- **Evidence:** [Subcritical finite-prefix obstruction](../../../../formal/GaloisForLFunctions/RHTower/PrimeArchFinitePrefixSubcriticalScheduleNoGo.lean); [earlier architecture](rh-frontier-reference-2026-09-12.md#source-line-752).

<a id="e--squarefree-wold-transport"></a>

### E — squarefree Wold transport

- **Closed:** Marker supply, endpoint reversal and singleton factorization; the sign-complete finite degree satisfies `2 degree = squarefree shell mass − μ(source) × shell Möbius sum`, with a corresponding variance bound. For positive stored indices whose actual clocks `q+1` are pairwise coprime, global Kloosterman collision fibres have at most two orientations. Collision energy is therefore at most twice the square of aggregate weighted unit-frequency source energy. Inverse units are reduced Farey points, giving the unconditional classical-scale bound `(N + M²(1 + log(M²/2 + 1))) Σ|bₙ|²`, and a uniform `|w_q|² ≤ W` costs only the factor `W` before squaring.
- **Open:** Beat the classical `M²` Farey-density term using the actual moving-cusp weights or Möbius source structure, then transport that gain through finite energy and Mellin continuation; alternatively prove physical shell-density/Möbius-energy and seam-flux estimates giving cofinal Hall/load control, or obtain cofinal bounded moving-cusp signed covariance. Keep hard-cutoff birth terms. Signed normalizer flux is exactly twice the original signed imbalance under its symmetry/nonzero-row hypotheses: renaming it is [not a cancellation proof](rh-killed-routes.md#no-go-026).
- **Evidence:** [Degree and variance](../../../../formal/GaloisForLFunctions/RHTower/RouteESignCompletePhysicalDegree.lean), [normalizer identity](../../../../formal/GaloisForLFunctions/RHTower/RouteESignedNormalizerFluxCircularity.lean), [source Farey large sieve](../../../../formal/GaloisForLFunctions/RHTower/Sieve/KloostermanSourceFareyLargeSieve.lean), [coprime collision bound](../../../../formal/GaloisForLFunctions/RHTower/Sieve/KloostermanGlobalCollisionCoprime.lean); [earlier architecture](rh-frontier-reference-2026-09-12.md#source-line-764).

<a id="fzz-p--parity-delay-mellin-orientation"></a>

### FZZ-P — parity-delay Mellin orientation

- **Closed:** Theta/FZZ Mellin occurrence, finite charge transport and one-sided radial orientation. Five new shortcut classes are closed: the raw cubic zero-collar integral diverges without its structural counterterm; the nonzero Fermi characteristic is not the divisor-bearing parity-Mellin amplitude; shared-coupling direct affine phase matching fails; and neither an additive Hermitian chiral reporter nor a scalar-real renormalized plane derivative can cancel the radial response's fixed imaginary part.
- **Open:** Derive a literal full integrated mixed replica–momentum Ward identity with a source-fixed **complex, non-scalar, cross-depth coherent** contribution, or use support motion/nonfactorization before integration. Retain fractional screening, both counterterms, physical normalization and cross-charge weighting. Renormalization, normalization, direct phase equality and Hermitian/scalar reporters no longer supply the missing orientation.
- **Evidence:** [Raw cubic cutoff no-go](../../../../formal/GaloisForLFunctions/RHTower/FZZCigarCubicRawCutoffNoGo.lean), [characteristic/amplitude no-go](../../../../formal/GaloisForLFunctions/RHTower/FZZCigarFermiCharacteristicMellinAmplitudeNoGo.lean), [direct phase no-go](../../../../formal/GaloisForLFunctions/RHTower/FZZCigarFermiSharedCouplingDirectPhaseNoGo.lean), [Hermitian chiral no-go](../../../../formal/GaloisForLFunctions/RHTower/FZZCigarOneSidedRadialHermitianChiralWardNoGo.lean), [renormalized-plane no-go](../../../../formal/GaloisForLFunctions/RHTower/FZZCigarOneSidedRenormalizedPlaneWardNoGo.lean); [earlier architecture](rh-frontier-reference-2026-09-12.md#source-line-1935).

<a id="g--ward-orientation"></a>

### G — Ward orientation

- **Closed:** Ward landings, real-channel reduction, affine G-CE source and real-reflection debt transfer remain exact. One source-defined cofinal Sonin schedule now transports the full complex Fisher score and reporter uniformly on every compact phase window, so all-phase occurrence is no longer missing. Isometric carrier changes nevertheless preserve the literal Euler source's critical squared cost `8`, not the required `4`; Gram-faithful compression cannot lower it. Reflection-compatible scalar shorting also preserves the opposite-radial negative norm-square signature.
- **Open:** Prove the one-scale real Ward inequality through a genuinely non-isometric, non-scalar signed incidence, or construct a literal zero-clock complementary cross-channel before scalarization. All-phase transport exists; the unresolved burden is source order, not occurrence.
- **Evidence:** [All-phase Sonin carrier](../../../../formal/GaloisForLFunctions/RHTower/SoninCofinalComplexPhaseGlobalCarrier.lean), [cofinal-isometry no-go](../../../../formal/GaloisForLFunctions/RHTower/EulerPreScalarGammaCofinalSoninIsometryNoGo.lean), [scalar-shorting no-go](../../../../formal/GaloisForLFunctions/RHTower/XiWardCubicScalarShortingNoGo.lean), [real-reflection cancellation](../../../../formal/GaloisForLFunctions/RHTower/MobiusGammaXiRealReflectionCancellationNoGo.lean); [earlier architecture](rh-frontier-reference-2026-09-12.md#source-line-866).

<a id="hb--theta-cusp-hawking-causal-scattering"></a>

### HB — theta-cusp Hawking causal scattering

- **Closed:** Complete original source profile has the exact late normal form `exp(2su)(A+uB)`. Genuine original Green poles survive on a relative-density-one subset of simple critical sources; there `B≠0`, excluding scalar late clocks, finite exponential packets and fixed linear physical-clock readouts. The positive survivor is exact: the unchanged physical clock realizes the profile as a quartic observation with its first time moment, and its integral is the complete canonical value. Full future-pulse assembly, corner regularity, fixed-source horizon caps, weighted source admission and plane-kernel bounds are formal. Same-frequency Peierls sewing is impossible, the uncorrected on-shell source has unit pole residue, and native on-shell radial `L²` realization is paper-closed; compact retarded weak realization is also paper-closed.
- **Open:** Prove the noncompact causal cutoff-face/action transgression carrying the unit pole residue, frequency-defect cochain, explicit wave cochain and recovered contact term to the retained `mixedField` two-leg boundary. Formalize the compact weak assembly and native `L²` instantiation, then prove the global hyperbolic polar integration/differentiation and noncompact left-QNM pairing needed by that action comparison. A nonzero cutoff face kills the final distributional realization; zero gives the required identification. No theorem yet derives RH.
- **Evidence:** [Green-pole matching no-go](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMOriginalGreenPoleMatchingNoGo.lean), [source-clock rigidity and quartic survivor](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMOriginalSourceClockRigidity.lean), [future-pulse identity](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFuturePulseIdentity.lean), [complete source admission](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCompleteSourceAdmission.lean), [plane-kernel admission](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMPlaneKernelAdmission.lean), [frequency-defect cochain](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMStreamFrequencyDefectCochain.lean), [on-shell source pole](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMLiteralOnShellSourcePole.lean), [same-frequency no-go](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMLiteralSameFrequencyPeierlsNoGo.lean), [paper-closed native `L²` no-go](../2-fully-proven/hb-onshell-cleared-native-l2-no-go.md), [paper-closed compact weak bridge](../2-fully-proven/hb-retarded-compact-weak-realization.md).

| Remaining HB front | What is closed | What is not closed |
|---|---|---|
| Original scalar/circle period | Actual circle period equals the physical source coefficient times the Legendre circle kernel; all principal corrections cancel on restoration. The complete source profile is `exp(2su)(A+uB)`; surviving Green poles force `B≠0`. Scalar/finite-packet clocks fail, while a quartic physical-clock observation recovers the profile and complete action exactly. | Transport the retained first-moment coordinate through the noncompact action boundary. Clock occurrence and local profile reconstruction are closed; the global Peierls extinction law is not. |
| Physical metric current | Original forced scalar/coexact contact and finite-domain orbit-current identities are closed. Complete finite-time boundary, source, forcing and static metric collars retain both temporal endpoints, all four transfers and all three counterterms; their independent horizon/cusp restoration is formal. The whole two-frequency source resolvent, reader diagonal regularization and exact fixed-source derivative reduction are now closed. | Relate the restored source derivative's finite QNM value to fixed-Hawking-clock extinction and the modular spectral form. Cutoff control no longer supplies the missing arithmetic sign or vanishing law. |
| Angular cusp face | Full future pulse is jointly smooth after exact three-chart assembly. Both horizon caps share one fixed source radius; the actual response and full source are admitted at the physical weight, and the plane-kernel density is exact. | Prove the global hyperbolic polar integration identity, parameter differentiation and noncompact left-QNM pairing. Local weighted admission is no longer the missing estimate. |
| Horizon, radial and QNM corner | Source/forcing pullbacks retain both horizon branches and all source-determined counterterms. The on-shell transform has unit residue, the frequency defect factors by `w-2s`, and the quotient has a complete frozen-metric representative. Native radial `L²` realization is paper-excluded but compact retarded weak realization is paper-closed. | Prove the noncompact cutoff-face transgression and recover the contact term as boundary data. Same-frequency sewing and uncorrected holomorphic pole removal are closed; only a meromorphic/distributional action realization survives. |
| Stationary two-rate kernels | Exact SS/VV and mixed current/trace formulae, finite parts, tilt detectors and harmonic sign laws. The constant-mode FE-invariance receiver detects `σ=1/2` for `0≤σ≤1`, `t≥92`. | Source-produced FE invariance and transport to the original causal action. SS and VV have opposite signs on an explicit band; [amplitude-independent kernel sign is excluded](rh-killed-routes.md#no-go-268). Arbitrary copywise unit phase [cannot alter universal darkness](rh-killed-routes.md#no-go-280), and a regular horizontally robust five-half collision trap is [null/terminal](rh-killed-routes.md#no-go-281). |
| On-line spectral comparison | SS plateau satisfies `abs(Im K)≤t⁹` for `t≥50`, while its constant mode is at least `t¹¹/2176`. The modular Dirichlet form is dense and closable, its covariance is `(1−Δ)⁻¹`, and the [assembled spectral inequality](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSkewPlateauCovarianceKernel.lean) holds for every modular `L²` field: constant-mode contribution minus `t⁹` times orthogonal energy bounds the quadratic form below. | Identify the actual source-retaining HB field in this `L²` space and prove the source-specific domination `orthogonal energy = o(t² × constant energy)` (or a sufficient explicit variant), then connect the form to the original causal current. The general spectral theorem does not supply that source estimate. |

Additional evidence: [native-reader decay](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMMixedNativeReaderFlux.lean), [particular cusp resonances](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMMixedParticularCuspFlux.lean), [finite static slabs](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMActualIngoingCurrent.lean), [mixed radial overlap](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMMixedRadialOverlap.lean), [left-QNM exchange](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMLeftQNMCorrectionExchange.lean), [constant-mode receiver](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMEvenSectorSkewConstantFE.lean).

Current matching evidence: [principal matching](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMOriginalPrincipalMatching.lean), [complete four-transfer boundary](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMOriginalCompleteTransfer.lean), [joint collar restoration](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMOriginalFullCollarRestoration.lean), [canonical action](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMOriginalCanonicalMetricAction.lean), [complete static continuation](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMOriginalStaticCanonicalAction.lean).

Current spectral evidence: [uniform kernel bound](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMEvenSectorSkewUniformBound.lean), [constant-weight positivity](../../../../formal/GaloisForLFunctions/RHTower/XiLogDerivLineOnePositive.lean), [logarithmic-derivative growth](../../../../formal/GaloisForLFunctions/RHTower/XiLogDerivLineOneGrowth.lean), [Bessel bound](../../../../formal/GaloisForLFunctions/RHTower/BesselKImaginaryOrderUniformBound.lean), [Eisenstein bound, `t≥1`, `1/2≤Y≤1`](../../../../formal/GaloisForLFunctions/RHTower/EisensteinCuspTailImaginaryOrderBound.lean), [modular form assembly](../../../../formal/GaloisForLFunctions/HTGeometry/ModularDirichletFormDomain.lean), [closability](../../../../formal/GaloisForLFunctions/HTGeometry/ModularDirichletFormClosable.lean).

<a id="hc--horizontal-collision-charge"></a>

### HC — horizontal collision charge

- **Closed:** Horizontal charge/conservation, confluent source current and multiplicity-sensitive receiver geometry.
- **Open:** Construct signed off-diagonal cancellation with a singular or unbounded source-to-Gauss–Hodge comparison preserving labels, multiplicity, orientation and wall residue.
- **Evidence:** [Architecture, precise hypotheses and source references](rh-frontier-reference-2026-09-12.md#source-line-2170).

<a id="l--singular-greenbv-to-physical-descent"></a>

### L — singular Green/BV-to-physical descent

- **Closed:** Green/BV/Tate source transport, normalized cyclic reader, damped original-source limits and exact scalar pole/normalization classification.
- **Open:** Compare the complete original Green/BV source with the fixed physical reader through a justified singular domain/reader change. Control reciprocal leading jets and the zero-damping full-packet passage; existing projection or damped convergence does not do this.
- **Evidence:** [Architecture, precise hypotheses and source references](rh-frontier-reference-2026-09-12.md#source-line-890).

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

- **Closed:** Ground/lag/counting-function RH endpoints remain exact. At every actual outgoing quantile cutoff, Fourier curvature is now exactly signed barycentric displacement credit minus nonnegative squared-displacement debt. The mass-clock/time-clock Stieltjes crossing is source-faithful: after exact archimedean centering, the outgoing moment is one threshold-centered completed prime--polar action plus nonnegative crossing credit. This is the same finite invariant as terminal-mass action plus crossing credit.
- **Open:** Prove a cofinal lower bound for that one exact signed invariant, equivalently that barycentric credit pays the full displacement debt on the required heads. Gamma-head positivity, absolute transport work, model clocks and separate prime estimates cannot replace it. The older L2 constrained-ground and complete-support lag alternatives remain open.
- **Evidence:** [Barycentric credit/debt](../../../../formal/GaloisForLFunctions/RHTower/CCMActualHeadOutgoingQuantileBarycentricDebt.lean), [Stieltjes crossing and centered action](../../../../formal/GaloisForLFunctions/RHTower/CCMActualHeadOutgoingQuantileStieltjesCrossing.lean); [earlier architecture](rh-frontier-reference-2026-09-12.md#source-line-1243).

<a id="p--paired-primegamma-signed-exterior-wall"></a>

### P — paired prime–Gamma signed exterior wall

- **Closed:** Paired source operators, cubic trace and all-order cold orientation remain exact. Depth squaring now transports every summable cubic-weighted source on infinite support with exact factor `1/8`. The actual physical Hellinger pivot is Hilbert--Schmidt-null after normalization, so its ordinary determinant converges locally uniformly to the same aperture wall; the wall/Xi quadratic-jet mismatch therefore closes pivot retuning. Synchronized Gamma recovery has forced cross-prime curvature and a coefficient-faithful mixed source factor. The PCOB cubic birth is fixed on the literal prime-history core, identified with the critical-Laplace reporter, and transported by a denominator-free theta Wronskian ladder throughout `|Im w|<1`.
- **Open:** Assemble the labelled mixed finite source and unbounded graph reporter into one completion-stable signed global primitive/current, retaining cross terms. For the theta formulation, construct the closed `Graph(cl A_*)` morphism and relative Calderón/boundary class carrying the same four-level Xi filtration to both escape incidence and nuclear budget. Scalar evaluation at an Xi zero erases a nonzero one-prime cubic symbol and is closed.
- **Evidence:** [Infinite depth-square energy](../../../../formal/GaloisForLFunctions/RHTower/RoutePPrimitiveDepthSquareInfiniteEnergy.lean), [physical pivot-wall no-go](../../../../formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaPhysicalStokesPivotWallTransferNoGo.lean), [mixed Gamma curvature](../../../../formal/GaloisForLFunctions/RHTower/GammaSewnSynchronizedRecoveryMixedCurvature.lean), [cubic orbit birth](../../../../formal/GaloisForLFunctions/RHTower/PrimeHodgeCubicOrbitBirth.lean), [critical-Laplace bridge](../../../../formal/GaloisForLFunctions/RHTower/PrimeHodgeCubicCriticalLaplaceBridge.lean), [complex-strip theta jet](../../../../formal/GaloisForLFunctions/RHTower/PrimeLogThetaStripWronskianCubicJet.lean); [earlier architecture](rh-frontier-reference-2026-09-12.md#source-line-1351).

<a id="pw-b--recoildeninger-ward-transmutation"></a>

### PW-B — recoil/Deninger Ward transmutation

- **Closed:** Exact recoil/FZZ/Ward imbalance equivalence, original current adjoint and admitted fixed-Mellin identity; literal global dual-mass bound excluded. Every inversion-closed extension of finite physical energy support now contains the minimal reciprocal completion and its infinite reciprocal tail, and the forced reciprocal map realizes both Mellin-grade reflection identities globally.
- **Open:** Derive that reciprocal completion from a literal Hawking closed-time-path source seam while retaining finite-energy contacts, then prove source-derived fixed-grade partner balance and Xi occurrence. Support geometry alone is not a physical seam or reflection theorem at all complex grades.
- **Evidence:** [Reciprocal-energy completion](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekReciprocalCompletion.lean); [earlier architecture](rh-frontier-reference-2026-09-12.md#source-line-2039).

<a id="q--exterior-paired-value-passivity"></a>

### Q — exterior paired-value passivity

- **Closed:** Explicit paired kernel, finite rational matrices and exact RH endpoint. The continued prime–Gamma reciprocal-square sector sign on the centered upper strip is exactly equivalent to RH, with a local negative pole witness at every off-line zero. Exact linear-tail summation extends unconditional source positivity to `701/100 < Re z ≤ 261/25`, `0 < Im z < 1/2` away from poles.
- **Open:** Extend the source sector sign from that finite exterior band to its full pole-free upper-strip domain, equivalently prove global exterior paired-diagonal nonnegativity. The enlarged band still lies below the proved divisor-frequency radius and does not reach a pole witness.
- **Evidence:** [Exact source-sector criterion](../../../../formal/GaloisForLFunctions/RHTower/PrimeArchReciprocalSquareSectorGate.lean), [positive exterior overlap](../../../../formal/GaloisForLFunctions/RHTower/PrimeArchPositivePairedDiagonalExteriorOverlap.lean); [earlier architecture](rh-frontier-reference-2026-09-12.md#source-line-1407).

<a id="rg--gaussian-arithmetic-and-suzuki-transport-positivity"></a>

### RG — Gaussian arithmetic and Suzuki transport positivity

- **Closed:** Gaussian explicit formula and heat transport; Suzuki origin/first-tail barrier; safe-chart source formation/current/phase.
- **Open:** Prove unbounded good Gaussian widths uniformly in center or signed control through every remaining Suzuki prefix/seam. Source continuation through the zero-bearing strip is an alternative interface, not a new route.
- **Evidence:** [Architecture, precise hypotheses and source references](rh-frontier-reference-2026-09-12.md#source-line-2194).

<a id="sp-e--signed-prime-dilation-versus-continuum"></a>

### SP-E — signed prime dilation versus continuum

- **Closed:** The completed outgoing charge has an exact one-step quarter-dilation balance; its cumulative imbalance is unconditionally `o(sqrt N)`, while uniform boundedness is equivalent to RH. The literal Eulerian discrepancy differs from completed outgoing charge by an explicit bounded residual, so boundedness of the actual discrepancy is also equivalent to RH. Every SP-E Abel cell is reconstructed from successive Weil-lag tails, yielding an exact finite Green identity and an integer-lag formula. Positive regular and atomic Ward masses share the `sqrt N/3` leading scale; direct negative-light payment leaves a `sqrt N/6` residual. Type-B top-signature factorization kills the first four-label curvature and makes the canonical Plücker pencil singular.
- **Open:** Prove the source-derived endpoint-corrected signed integer-lag-mean law, equivalently a uniform bound for the literal accumulated quarter-dilation/completed-outgoing imbalance. The law must retain cross-scale orientation and descent-bottom incidence before positive Gram or scalar completion. Separate positive masses, finite moments, top signatures and local energy cannot supply it.
- **Evidence:** [Completed dilation balance](../../../../formal/GaloisForLFunctions/RHTower/SuzukiCompletedOutgoingDilationBalance.lean), [actual discrepancy rigidity](../../../../formal/GaloisForLFunctions/RHTower/SuzukiEulerianOutgoingChargeRigidity.lean), [Weil-lag bridge](../../../../formal/GaloisForLFunctions/RHTower/SuzukiWeilLagTailBridge.lean), [continuous co-divergence](../../../../formal/GaloisForLFunctions/RHTower/SuzukiWardContinuousCoDivergence.lean), [completed-light residual no-go](../../../../formal/GaloisForLFunctions/RHTower/SuzukiWardCompletedLightResidualNoGo.lean), [top-fibre collapse](../../../../formal/GaloisForLFunctions/RHTower/PrimeGammaSignedEulerianTopFiberNoGo.lean); [earlier architecture](rh-frontier-reference-2026-09-12.md#source-line-2115).

<a id="stc--exterior-sonin-seam-coherence"></a>

### STC — exterior Sonin seam coherence

- **Closed:** Exterior coherence endpoint and a target-free fixed-prime Gamma-six/Sonin lift with exact Calkin bounds.
- **Open:** Identify or construct the canonical all-prime seam from source, then prove its cofinal sub-root Calkin growth law.
- **Evidence:** [Architecture, precise hypotheses and source references](rh-frontier-reference-2026-09-12.md#source-line-846).

<a id="sv2--suzuki-projective-limit-and-shifted-kernel-inertia"></a>

### SV2 — Suzuki projective limit and shifted-kernel inertia

- **Closed:** Projective/Schur receivers, shifted-kernel inertia, rational-node witnesses and finite-prime tails. For every positive movable height, the literal completed covariance is the characteristic of a scaled self-adjoint extension: it has all-angle real zeros, is strictly Schur, and its second disk jet tends to zero at coalescence. Before scalarization it lands in constrained CCM coordinates; after exact two-pole removal the movable deficiencies remain total, and actual finite families span every reducing exceptional block. Reflection-compatible causal phase sends every odd source into the even sector, so its diagonal quadratic readout vanishes identically.
- **Open:** Prove the joint quadratic/graph-energy inequality using signed cross terms, or construct an off-diagonal/affine source channel. Totality, strict Schur behavior, second-jet decay, generatorwise positivity, position torque, and the [odd diagonal phase](rh-killed-routes.md#no-go-292) do not imply it. Excluding every finite tail-certified negative Pick witness directly from primes remains an alternative.
- **Evidence:** [Odd-phase diagonal no-go](../../../../formal/GaloisForLFunctions/RHTower/SuzukiVolterraPhaseOddDiagonalNoGo.lean), [movable characteristic](../../../../formal/GaloisForLFunctions/RHTower/SuzukiTaMovableCompletedCovarianceCharacteristic.lean), [CCM landing](../../../../formal/GaloisForLFunctions/RHTower/SuzukiTaMovableCompletedCovarianceCCMBridge.lean), [totality and exact energy criterion](../../../../formal/GaloisForLFunctions/RHTower/SuzukiTaMovableDeficiencyTotality.lean).

<a id="t1--theta-tail-core-current"></a>

### T1 — theta-tail core current

- **Closed:** Finite theta/prime decompositions, signed receivers and the co-moving Levinson landing remain exact. The actual mass kernel's Hermitian square is now the full two-rapidity oscillatory integral, and the moving von Mangoldt cone is attached exactly to its complete finite prime-pair covariance. Deep mass compresses each stationary rapidity pair, but distinct frequencies enter every fixed-width diagonal tube; diagonal localization by a fixed rapidity width is therefore closed. Direct affine transport to Vaughan's antitone log phase also remains impossible.
- **Open:** Prove eventual boundedness through a genuinely signed estimate for the full finite prime-pair covariance, or derive frequency–rapidity order support excluding anti-ordered saddles. Pointwise nonstationarity, fixed-width tubes and unchanged phase identification do not control the two-variable integral. Levinson filters still need cofinal/infinite structure or signed cancellation with exact landing retained.
- **Evidence:** [Exact prime-pair covariance](../../../../formal/GaloisForLFunctions/RHTower/XiMassTwoRapidityCorrelationGeometry.lean), [direct mass-phase transport no-go](../../../../formal/GaloisForLFunctions/RHTower/XiMassNearDiagonalStationaryNoGo.lean), [co-moving zero-jet landing](../../../../formal/GaloisForLFunctions/RHTower/XiMassLevinsonComovingZeroJetLanding.lean); [earlier architecture](rh-frontier-reference-2026-09-12.md#source-line-2131).

<a id="t2--natural-abel-singular-wold-divisor"></a>

### T2 — natural-Abel singular Wold divisor

- **Closed:** Natural Abel continuation and multiplicity-sensitive singular residue divisor; current assembly and tomography.
- **Open:** Construct a second source-derived singular comparison or relative invariant excluding strict-right residues. Requiring regularity of the known continuation merely restates RH.
- **Evidence:** [Architecture, precise hypotheses and source references](rh-frontier-reference-2026-09-12.md#source-line-2143).

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

- **Closed / available:** Literal physical source is identified cellwise with the truncated reciprocal Möbius-divisor tail, including exact block energy and signed Gram rectangles. Chronological projection has exact weighted-residue coarea; predictable drift has a pointwise signed residue-quotient expansion and exact covariance formula. Its norm decomposes into orthogonal history-layer energies, and each layer is a reverse complete Möbius tail. Cofinal polylog control of this exact covariance implies RH. The tempting positive all-gcd completion is fully classified instead: it is a totient-weighted sum of squares containing a fixed fraction of squared late-prime mass and is superquadratic.
- **Open:** Prove the cofinal polylogarithmic bound for the exact signed residue covariance/predictable drift, then control the complete quotient tail. Cancellation must remain joint across history layers, divisor levels and multiple inserted primes. Positive-semidefinite gcd completion, absolute values, moving-window means and one-step core bounds erase or dominate the required cancellation.
- **Evidence:** [Physical cell Möbius identity](../../../../formal/GaloisForLFunctions/RHTower/EulerDeletionPhysicalCellMoebiusIdentity.lean), [weighted residue projection](../../../../formal/GaloisForLFunctions/RHTower/EulerDeletionWeightedResidueProjection.lean), [nested covariance layers](../../../../formal/GaloisForLFunctions/RHTower/EulerDeletionNestedProjectionCovariance.lean), [signed covariance criterion](../../../../formal/GaloisForLFunctions/RHTower/EulerDeletionSignedResidueCovariance.lean), [inclusive-gcd no-go](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorInclusiveGcdGramNoGo.lean), [superquadratic asymptotic](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorInclusiveGcdGramAsymptotic.lean).

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
- **Open:** Prove the source-majorant ceiling 21/100, a compact phase-average gate, or a height-summed cross-scale frame budget. Density improvement is not full RH.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-hcf).

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

- **Closed / available:** Exact analytic photonic return receiver: the transfer response reduces to `diag(1, ζ(s)²)`, defect confinement is equivalent to RH, and its zero kernel is the parabolic flux-null line. The logarithmic phase lift has an explicit nontrivial deck character whose invariant projection recovers the regular germ and first-jet return matrix.
- **Open:** Derive the transfer matrix and ramified phase coordinate from a physical Maxwell/time-crystal source, then prove a source law confining defects. Algebraic return identities and monodromy do not provide physical occurrence or confinement.
- **Evidence:** [Parabolic return and confinement receiver](../../../../formal/GaloisForLFunctions/RHTower/PhotonicParabolicReturn.lean), [phase-cover monodromy](../../../../formal/GaloisForLFunctions/RHTower/PhotonicReturnMonodromy.lean).

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

- **Closed / available:** Source-history completion, escape classification and exact affine Xi-residue landing.
- **Open:** Construct a divisor-independent positive polarized history with norm-dark packets and nonescaping reciprocal price, then exhaust Xi copies.
- **Evidence:** [Exact mechanism, qualifications and remaining theorem](rh-frontier-reference-2026-09-12.md#candidate-rhist).

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

- **Closed / available:** Rational correspondence now acts linearly on the zero-inclusive fixed Maass cusp eigenspace. Traces compose along nested finite-index chains, rational pullback commutes with trace, and positive-rational analytic trace works on mapped stabilizer intersections. Double-coset orbit/stabilizer decomposition, global block summation and literal Mackey trace composition are formal; together they give the finite rational Mackey product law. This closes the finite-correspondence composition engine. It does not repair direct coercivity: every nonzero exceptional rational trace has strictly negative `coreQuarter` at the transition cutoff, and every finite positive weighted average remains negative.
- **Open:** For the direct route, find a sign-indefinite/source-sensitive lower-flux or density-weighted quartic comparison; positive trace averaging is closed. For the global route, identify every Mackey stabilizer block as a rational principal endomorphism, prove a commuting/self-adjoint finite-place Hecke algebra on a finite-dimensional or compact-resolvent eigenspace, construct its adelic realization, and then compatible unbounded symmetric-power lifts.
- **Evidence:** [Hecke eigenspace and linear traces](../../../../formal/GaloisForLFunctions/RHTower/SelbergMaassHeckeEigenspace.lean), [double-coset trace](../../../../formal/GaloisForLFunctions/RHTower/SelbergMaassDoubleCosetTrace.lean), [trace base change](../../../../formal/GaloisForLFunctions/RHTower/SelbergMaassTraceBaseChange.lean), [Mackey composition](../../../../formal/GaloisForLFunctions/RHTower/SelbergMaassMackeyTraceComposition.lean), [positive-rational trace](../../../../formal/GaloisForLFunctions/RHTower/SelbergMaassPositiveRationalTrace.lean), [positive-average no-go](../../../../formal/GaloisForLFunctions/RHTower/SelbergMaassTraceAverageNoGo.lean); [earlier architecture](rh-frontier-reference-2026-09-12.md#candidate-sqb).

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

The complete catalogue contains **all 324 named entries**, not a selected list. Each family
opens a name index followed by one structured result/survivor card per mechanism.
The 16 original-label records above are included in that total; FD2 and RBH also have
their longer architecture verdicts in the reference.

| Browse closed mechanisms | Entries |
|---|---:|
| [Retired original route labels](rh-killed-routes.md#retired-labels) | 16 |
| [CCM-FU: prime scheduling and current bounds](rh-killed-routes.md#ccm) | 22 |
| [E, EDQ, HCF, T1/T2 and LI: arithmetic cancellation](rh-killed-routes.md#arithmetic) | 37 |
| [HB, FZZ and PW: scattering and physical action](rh-killed-routes.md#scattering) | 69 |
| [Theta, Schur, spectral and positivity mechanisms](rh-killed-routes.md#theta) | 26 |
| [Singular descent, formation and completion](rh-killed-routes.md#completion) | 26 |
| [Ward, Suzuki, prime–Gamma and operator landing](rh-killed-routes.md#ward) | 39 |
| [Analytic roots, multiplicity and regularization](rh-killed-routes.md#roots) | 9 |
| [Other finite, scalar and source-blind selectors](rh-killed-routes.md#other) | 80 |

## Shared infrastructure and unlabelled continuation problems

These are not additional active-route labels. Their value is the exact problem they
remove—or expose—inside the named routes.

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

The register reconciles committed Lean source through the cutoff above. The 107-file formal delta
contains 90 additions and 17 modifications across HB, CCM/O, EDQ, SQB, G/P/SP-E/U/S6F,
shared HTGeometry infrastructure and import umbrellas. All changed formal files were classified;
modified statements and route fact logs were compared. The audit adds 14 grouped no-go records
and strengthens two earlier records with their new two-sided and physical-channel closures.

The 25 active routes and 37 candidates are unchanged. Closed work removes HB compact/source-plane
admission, scalar/finite-packet clock matching, finite rational-trace composition, EDQ covariance
identification, SP-E lag reconstruction, Route-P finite/infinite source incidence and several
scalar/positive completion subproblems. No independent signed prime/Möbius covariance estimate,
compact-core coercivity, adelic symmetric-power lift, global graph-to-current assembly, or HB
noncompact action-boundary theorem was closed.

This is a source-statement audit, not a fresh kernel/dependency validation. It does not
broaden theorem hypotheses or promote uncommitted paper arguments. Current source links
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
