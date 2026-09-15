# RH research ledger

**No route proves or disproves RH.** This register separates **25 active routes**,
**37 named candidates**, and **293 closed mechanisms**. “Active” means a formal
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

**Source-audit cutoff: 2026-09-15, `277d498a24567a583bcd09ff24dd56243b687e89`.**
Reconciled the 54-file formal delta since `160e2ed5ae8b335f72eeac2239f6e3ceb81e6b27`
(45 additions and nine modifications, including import umbrellas). Uncommitted work is
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

- **Closed:** Completed current, source transport, coprime pairing, arity balance, finite scheduling/capacity and RH receivers. Generalized von Koch is formal for every Xi half-plane width, and RH is exactly equivalent to one sharp dyadic weighted-prime-window subpower upper law. The all-height movable Suzuki covariance lands in the exact two-pole constrained CCM form domain; after pole removal its literal source family is total. The restricted-Weil odd-pole Green residual equals the raw CCM-FU triangular prime window coefficient by coefficient. Its pole diagonal is the sharp exponential-pole trace, is eventually positive, and the even critical wall response is nonpositive after entry. The critical ordered remainder splits into uniformly summable source-free variation plus exact prime-polar Mertens deviation. Every prime `p≥27` creates a positive critical cell of size at least `log p/(2p)`; absolute variation diverges, and any nonpositive compensating forward block must have length at least `log p/2`.
- **Open:** Prove one independent **signed, growing-range** source estimate: the joint quadratic/graph-energy inequality on finite pole-corrected source combinations, the equivalent critical Mertens-deviation variation bound, the dyadic subpower law, or a cofinal raw-energy history with transverse cancellation and an `O(M)` terminal head. Fixed-range transport, cellwise/absolute estimates, totality and pole-trace positivity do not supply the missing cancellation.
- **Evidence:** [Critical cell sign](../../../../formal/GaloisForLFunctions/RHTower/CCMFUSuzukiCriticalCellSign.lean), [absolute-variation pressure](../../../../formal/GaloisForLFunctions/RHTower/CCMFUSuzukiCriticalAbsoluteVariationPressure.lean), [growing-range obstruction](../../../../formal/GaloisForLFunctions/RHTower/CCMFUSuzukiCriticalTransportRangeNoGo.lean), [restricted-Weil pole trace](../../../../formal/GaloisForLFunctions/RHTower/CCMRestrictedWeilPoleTracePositivity.lean), [pole-wall response](../../../../formal/GaloisForLFunctions/RHTower/CCMRestrictedWeilPoleWallResponseSign.lean), [critical remainder variation criterion](../../../../formal/GaloisForLFunctions/RHTower/CCMFUSuzukiCriticalRemainderVariation.lean), [pole-corrected source totality and energy criterion](../../../../formal/GaloisForLFunctions/RHTower/SuzukiTaMovableDeficiencyTotality.lean); [earlier architecture](rh-frontier-reference-2026-09-12.md#source-line-340).

<a id="cdc--constitutive-dagger-confluence"></a>

### CDC — constitutive dagger confluence

- **Closed:** Canonical pre-divisor potential, calibrated mate gain and exact wall-classifying confluence/proof-erasure receivers.
- **Open:** Derive semantic descent or three-slot proof erasure on every closed Xi-error fibre from the literal arithmetic source.
- **Evidence:** [Architecture, precise hypotheses and source references](rh-frontier-reference-2026-09-12.md#source-line-742).

<a id="clgttf--completed-theta-bezoutian-no-escape"></a>

### CLG/TTF — completed theta Bezoutian no-escape

- **Closed:** Theta Bezoutian/Krein incidence, separated-tail positivity, global native D1, low-rank center-mixed sections and uniform small-cluster results. For the even compact polynomial-ODE incidence bridge, determinant coefficient identities are now formal at gap degrees `0–7` and `12–20`; the new certified cofactor slices close degrees `4–7` without external coefficient assumptions.
- **Open:** Close the four remaining determinant coefficients `8–11` and final polynomial extensionality, then prove the compact inner/middle comparison and general-packet/all-order source orientation. Finite coefficient closure alone does not prove the required rank-seven or global positivity law.
- **Evidence:** [Gap coefficient 4](../../../../formal/GaloisForLFunctions/HTGeometry/PolynomialODEEvenCompactGapCoefficient4.lean), [gap coefficient 7](../../../../formal/GaloisForLFunctions/HTGeometry/PolynomialODEEvenCompactGapCoefficient7.lean), [higher cofactor normalizer](../../../../formal/GaloisForLFunctions/HTGeometry/PolynomialODEEvenCompactGapCofactorHigherNormalizer.lean); [earlier architecture](rh-frontier-reference-2026-09-12.md#source-line-1417).

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

- **Closed:** Theta/FZZ Mellin occurrence, finite charge transport, fixed-dimensional cubic values and position-log ratio. The original normalized first marked plane-screening integral vanishes exactly on its chart line `y=0`. For the one-sided radial response, reflection is conjugate-odd and its real component selects zero momentum, while its imaginary component has fixed negative orientation. An explicit all-depth model now shows that neutrality plus nonzero activation at every screening depth still permits exact cancellation of the factorized scalar Ward response.
- **Open:** Derive the full integrated mixed replica–momentum Ward identity with a source-fixed complex phase and a genuine cross-depth coherence/noncancellation law, or use support motion/nonfactorization before integration. Retain fractional screening, physical normalization and cross-charge weighting. Factorization plus all-depth activation is [insufficient](rh-killed-routes.md#no-go-290).
- **Evidence:** [All-depth factorized no-go](../../../../formal/GaloisForLFunctions/RHTower/FZZCigarParityNeutralAllDepthFactorizedWardNoGo.lean), [actual marked-integral zero locus](../../../../formal/GaloisForLFunctions/RHTower/FZZCigarPlaneScreeningMarkedZeroClassification.lean), [one-sided reflection selector](../../../../formal/GaloisForLFunctions/RHTower/FZZCigarOneSidedRadialReflectionSelector.lean); [earlier architecture](rh-frontier-reference-2026-09-12.md#source-line-1935).

<a id="g--ward-orientation"></a>

### G — Ward orientation

- **Closed:** Ward landings, real-channel reduction, fixed least certified sample scale and affine G-CE source.
- **Open:** Prove the one-scale real Ward inequality, or annihilate the G-CE cofinal coefficient before scalarization. Any surviving annihilator must escape the finite-local no-go.
- **Evidence:** [Architecture, precise hypotheses and source references](rh-frontier-reference-2026-09-12.md#source-line-866).

<a id="hb--theta-cusp-hawking-causal-scattering"></a>

### HB — theta-cusp Hawking causal scattering

- **Closed:** Both actual angular polarizations decay as `O(1/Y)`; the modular defect tensor vanishes. The literal scalar quadratic source is identified in all 16 components, and its full nonseparated SS and contact-inclusive SV particular metrics solve their sourced equations. For the original causal field, all five source jets, every boundary transfer and all source-fixed power/log counterterms are retained. The new source-resolvent stack derives both endpoint limits, reader-pole subtraction, diagonal matching, native forcing finite part, and the complete two-frequency identity. Independent horizon/cusp, outer-cusp, moving-corner and whole-static-metric restoration are formal. The physical Green metric plus complete temporal corner reduces exactly to a fixed-source derivative with forcing retained; at either QNM its density is one elementary source core, and the canonical finite value equals an explicit connection-cleared derivative quotient.
- **Open:** Evaluate that canonical source finite part and prove its exact extinction/nonextinction relation to the unit left-source clock. Generic Xi reflection/conjugation symmetry cannot exclude a strict-right half-affine zero collision, so any bridge also needs an Xi-specific affine-collision invariant or a different source-retaining receiver. Then identify the field in the modular `L²` comparison and prove source-specific orthogonal-energy domination. No theorem yet derives RH.
- **Evidence:** [Whole source resolvent](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMOriginalWholeSourceResolvent.lean), [source-action reduction](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMOriginalPhysicalSourceAction.lean), [canonical QNM value formula](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMOriginalMetricQNM.lean), [whole static metric](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMOriginalWholeStaticMetric.lean), [symmetry-only collision no-go](../../../../formal/GaloisForLFunctions/RHTower/XiAffineCollisionSymmetryModelNoGo.lean), [canonical action and removable QNM](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMOriginalCanonicalMetricAction.lean); [earlier architecture](rh-frontier-reference-2026-09-12.md#source-line-1646).

| Remaining HB front | What is closed | What is not closed |
|---|---|---|
| Original scalar/circle period | Actual circle period equals the physical source coefficient times the Legendre circle kernel; all principal corrections cancel on restoration. The original time integral equals the continued reduced Green family. The height-weighted causal orbit has a genuine cusp-time `L²` limit and Laplace transform, and the physical angular reader may be applied before time integration. | Identify the resulting canonical QNM value with an explicit source invariant strong enough to decide extinction. Scalar-period and `L²` convergence alone do not evaluate that value. |
| Physical metric current | Original forced scalar/coexact contact and finite-domain orbit-current identities are closed. Complete finite-time boundary, source, forcing and static metric collars retain both temporal endpoints, all four transfers and all three counterterms; their independent horizon/cusp restoration is formal. The whole two-frequency source resolvent, reader diagonal regularization and exact fixed-source derivative reduction are now closed. | Relate the restored source derivative's finite QNM value to fixed-Hawking-clock extinction and the modular spectral form. Cutoff control no longer supplies the missing arithmetic sign or vanishing law. |
| Angular cusp face | All five actual base operations are differentiated through the original source cube. Literal and canonical principal coefficients agree, including onset lift. Their products with both physical angular reader operations have arbitrary cusp decay. Assembly-before-continuation now incorporates all evolved-source channels into the canonical action. | Prove source-specific `L²` occurrence and orthogonal-energy domination. Equal-reader vanishing still does not justify unrenormalized split-reader continuity: [the family has a genuine pole](rh-killed-routes.md#no-go-271). |
| Horizon, radial and QNM corner | Source/forcing pullbacks retain both horizon branches and source-determined power/log counterterms. The canonical radial value is meromorphic, its literal metric cutoff converges off resonance, and the complete static metric action has a unique analytic representative at both fundamental QNMs. Its finite value is now the explicit connection-cleared derivative quotient of the canonical endpoint action numerator. | Evaluate that quotient from the elementary QNM source core and prove its source-dependent zero/nonzero classification. Generic Xi symmetry does not exclude the [half-affine collision](rh-killed-routes.md#no-go-291) that can kill the self-source amplitude. |
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

- **Closed:** Ground/lag/counting-function RH endpoints, finite-head reduction, attained-top exclusion and exact L1 growth-rate classification.
- **Open:** Derive subexponential L2 constrained-ground negativity or a complete-support lag upper law from primes. The sharp L2 zero-side upper rate still needs local zero-density control; single-base sampling also retains nonattained-shadow escape.
- **Evidence:** [Architecture, precise hypotheses and source references](rh-frontier-reference-2026-09-12.md#source-line-1243).

<a id="p--paired-primegamma-signed-exterior-wall"></a>

### P — paired prime–Gamma signed exterior wall

- **Closed:** Paired source operators and exact arithmetic rectangle cubic trace equal Xi multiplicity; the direct determinant's Xi mismatch is proved. A second-moment radius `‖α⁻²‖<1/150` now controls every higher reciprocal-square moment, and every cold Malgrange target from order two onward has its exact alternating orientation without finite-order enumeration or RH.
- **Open:** Connect this all-order cold orientation to the literal exterior wall/current and prove strict-right cubic zero-charge or exterior tail passivity. Alternatives still need modular admissibility or a singular moving-reference current; oriented target jets alone do not establish source occurrence.
- **Evidence:** [Second-moment radius](../../../../formal/GaloisForLFunctions/RHTower/XiReciprocalSquareSecondMomentRadius.lean), [all-order Malgrange orientation](../../../../formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesPrimeGammaWallAllOrderMalgrangeOrientation.lean); [earlier architecture](rh-frontier-reference-2026-09-12.md#source-line-1351).

<a id="pw-b--recoildeninger-ward-transmutation"></a>

### PW-B — recoil/Deninger Ward transmutation

- **Closed:** Exact recoil/FZZ/Ward imbalance equivalence, original current adjoint and admitted fixed-Mellin identity; literal global dual-mass bound excluded.
- **Open:** Produce source-derived fixed-grade partner balance through a justified singular/global law. Complete physical domain/Xi occurrence and endpoint control without replacing the retained contact terms.
- **Evidence:** [Architecture, precise hypotheses and source references](rh-frontier-reference-2026-09-12.md#source-line-2039).

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

- **Closed:** Signed source/continuum decomposition, completed source admission, growing-rank occurrence and formation-energy comparison. The corrected Chebyshev mass-error current is now an exact Eulerian prime-minus-continuum sum. Its positive actual-prime component is unbounded on width-five blocks, while the Gamma channels cancel to an explicit sub-root lattice prefix. The remaining non-elementary term is exactly the signed half-order Selberg--Abel action of the Chebyshev remainder, and the mass-error gate is asymptotically welded to the completed outgoing source.
- **Open:** Prove signed moderation of that exact completed outgoing/half-order Abel current. Positive prime pressure, separate absolute variation, and Gamma estimates cannot do this; required theorem is global cancellation against continuum and remaining prime history.
- **Evidence:** [Eulerian mass-error bridge](../../../../formal/GaloisForLFunctions/RHTower/SuzukiChebyshevMassErrorEulerianBridge.lean), [prime-block pressure](../../../../formal/GaloisForLFunctions/RHTower/SuzukiEulerianPrimeBlockPressure.lean), [signed Gamma current](../../../../formal/GaloisForLFunctions/RHTower/SuzukiEulerianSignedGammaCurrent.lean), [Selberg--Abel weld](../../../../formal/GaloisForLFunctions/RHTower/SuzukiEulerianSelbergAbelWeld.lean); [earlier architecture](rh-frontier-reference-2026-09-12.md#source-line-2115).

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

- **Closed:** Finite theta/prime decompositions, Type-I/II infrastructure, fixed-order harmonic models and signed current receivers. The literal co-moving Levinson zero jet equals the von Mangoldt half-density inside its aperture and lands exactly on the moving prime-power cone, so forward-line boundedness is fixed-Weil boundedness and hence an RH criterion. For the mass-phase comparison, diagonal distinct-frequency phase is nonstationary, but the full two-rapidity correlation has an off-diagonal stationary pair with reversed frequency/rapidity order; same-order causal support excludes that saddle. Direct affine transport from the even timelike mass action to the strictly antitone Vaughan log phase is impossible.
- **Open:** Prove eventual uniform boundedness from an independent arithmetic estimate. A mass-phase route needs a genuine bilinear diagonal-localization or same-order support theorem controlling the full two-variable integral; pointwise diagonal oscillation and unchanged phase identification are insufficient. Levinson filters still need cofinal/infinite structure or signed phase cancellation while retaining exact landing.
- **Evidence:** [Two-rapidity geometry](../../../../formal/GaloisForLFunctions/RHTower/XiMassTwoRapidityCorrelationGeometry.lean), [direct mass-phase transport no-go](../../../../formal/GaloisForLFunctions/RHTower/XiMassNearDiagonalStationaryNoGo.lean), [co-moving zero-jet landing](../../../../formal/GaloisForLFunctions/RHTower/XiMassLevinsonComovingZeroJetLanding.lean), [finite depth-charge classification](../../../../formal/GaloisForLFunctions/RHTower/XiMassLevinsonComovingDepthChargeNoGo.lean); [earlier architecture](rh-frontier-reference-2026-09-12.md#source-line-2131).

<a id="t2--natural-abel-singular-wold-divisor"></a>

### T2 — natural-Abel singular Wold divisor

- **Closed:** Natural Abel continuation and multiplicity-sensitive singular residue divisor; current assembly and tomography.
- **Open:** Construct a second source-derived singular comparison or relative invariant excluding strict-right residues. Requiring regularity of the known continuation merely restates RH.
- **Evidence:** [Architecture, precise hypotheses and source references](rh-frontier-reference-2026-09-12.md#source-line-2143).

<a id="u--adaptive-shifted-xi-hankel-frontier-renewal"></a>

### U — adaptive shifted-Xi Hankel frontier renewal

- **Closed:** Adaptive terminal frontiers, contact/residue pricing, parabolic confinement and fixed-degree positivity machinery.
- **Open:** Synchronize source positivity with every possible cofinal strict frontier through a degree-uniform rate or adjacent-degree history law; rule out sparse quadratic escape.
- **Evidence:** [Architecture, precise hypotheses and source references](rh-frontier-reference-2026-09-12.md#source-line-2156).

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

- **Closed / available:** Literal deletion/source reconstruction, compensated currents, full Möbius-tail energy identities and sharp shortcut obstructions. The complete physical Möbius source now has an exact Ramaré decomposition into a rough remainder minus prime packets; every packet is a physical dilation of its p-free cofactor plus a compulsory affine boundary correction. Dilation energy, tapered-source covariance with temporal cross terms, residual omitted-tail form, and subpower control of the gcd head modulo its explicit harmonic polynomial are formal.
- **Open:** Prove a cofinal subpower/logarithmic bound for the full signed rough-minus-packet energy, including prime--prime, prime--rough, affine/harmonic cross terms and omitted tails; or prove signed pre-saddle/chronological orientation with all terms retained. Exact decomposition and head asymptotics do not cancel the leading harmonic/tail contributions.
- **Evidence:** [Physical Ramaré decomposition](../../../../formal/GaloisForLFunctions/RHTower/EulerDeletionRamarePhysical.lean), [dilation identity](../../../../formal/GaloisForLFunctions/RHTower/EulerDeletionRamareDilation.lean), [dilation energy](../../../../formal/GaloisForLFunctions/RHTower/EulerDeletionRamareDilationEnergy.lean), [averaged covariance](../../../../formal/GaloisForLFunctions/RHTower/EulerDeletionAveragedDivisorCovariance.lean), [gcd-head subpower remainder](../../../../formal/GaloisForLFunctions/RHTower/EulerDeletionGcdHeadSubpower.lean), [residual tail form](../../../../formal/GaloisForLFunctions/RHTower/MoebiusResidualTailForm.lean).

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

- **Closed / available:** Literal sixth-jet source, strict D1/center mixture, order-eight connectors and small-cluster positivity. Generated ninth-order rational quadrature on the `1/64` mesh now proves all five first-atom bounds required by the existing centered-order-24 sixth-trace closure. The sixth reciprocal trace is also exactly one signed triple-product-kernel inequality, equivalently the third logarithmic coefficient of the normalized Xi square-coordinate jet.
- **Open:** Extend the source argument to every order or general-packet/cofinal incidence; a finite order-24 closure does not control the full jet hierarchy. Uniform signed product-kernel/log-coefficient inequalities are one concrete all-order target. The separate completed C5 slope remains open.
- **Evidence:** [High-order source quadrature](../../../../formal/GaloisForLFunctions/RHTower/PrimeArchThetaFirstAtomHighOrderQuadrature.lean), [source moment bounds](../../../../formal/GaloisForLFunctions/RHTower/PrimeArchThetaFirstAtomHighOrderMomentBounds.lean), [order-24 reduction](../../../../formal/GaloisForLFunctions/RHTower/XiCenteredOrderTwentyFourSixthTraceClosure.lean), [product-kernel/log-coefficient identity](../../../../formal/GaloisForLFunctions/RHTower/PrimeArchThetaThirdCumulantProductKernel.lean); [earlier architecture](rh-frontier-reference-2026-09-12.md#candidate-s6f).

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

- **Closed / available:** Smooth actual Maass ladders, model intertwining and quotient infrastructure; finite source transforms and compensated positivity regions. Exceptional congruence sources have exact zero deck mean, so mixing energy equals density and is bounded by block and generator energies; level one has no exceptional source. The Bessel seam is nonnegative above an explicit cutoff, forcing any exceptional source's compact-core quarter form to be strictly negative there. Exact raising/lowering energy transfer now gives factorial bounds for all diagonal-generator iterates. The resulting source-attached analytic vectors have all orbit derivatives, Taylor transport at every time, and stay in the closed completed-model range.
- **Open:** Prove a source-attached lower bound for the compact-core quarter form, or another signed core–cusp coercive inequality strong enough to exclude that forced negativity. Arithmetic-to-Maass occurrence or rank-seven/all-order signed positivity with cofinal residual control also remains open. Mean-zero, local generator energy and diagonal loss do not supply global quarter coercivity.
- **Evidence:** [Analytic-vector bounds](../../../../formal/GaloisForLFunctions/RHTower/MaassModelHilbertAnalyticVectorBounds.lean), [orbit derivatives and closed-range transport](../../../../formal/GaloisForLFunctions/RHTower/MaassModelHilbertOrbitDerivatives.lean), [boundary positivity reduction](../../../../formal/GaloisForLFunctions/RHTower/SelbergMaassBoundaryPositivity.lean), [quartic density identity](../../../../formal/GaloisForLFunctions/RHTower/SelbergMaassDensityQuartic.lean), [diagonal loss](../../../../formal/GaloisForLFunctions/RHTower/SelbergMaassDiagonalLoss.lean); [earlier architecture](rh-frontier-reference-2026-09-12.md#candidate-sqb).

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

The complete catalogue contains **all 293 named entries**, not a selected list. Each family
opens a name index followed by one structured result/survivor card per mechanism.
The 16 original-label records above are included in that total; FD2 and RBH also have
their longer architecture verdicts in the reference.

| Browse closed mechanisms | Entries |
|---|---:|
| [Retired original route labels](rh-killed-routes.md#retired-labels) | 16 |
| [CCM-FU: prime scheduling and current bounds](rh-killed-routes.md#ccm) | 18 |
| [E, EDQ, HCF, T1/T2 and LI: arithmetic cancellation](rh-killed-routes.md#arithmetic) | 33 |
| [HB, FZZ and PW: scattering and physical action](rh-killed-routes.md#scattering) | 57 |
| [Theta, Schur, spectral and positivity mechanisms](rh-killed-routes.md#theta) | 23 |
| [Singular descent, formation and completion](rh-killed-routes.md#completion) | 26 |
| [Ward, Suzuki, prime–Gamma and operator landing](rh-killed-routes.md#ward) | 32 |
| [Analytic roots, multiplicity and regularization](rh-killed-routes.md#roots) | 9 |
| [Other finite, scalar and source-blind selectors](rh-killed-routes.md#other) | 79 |

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
  available for both Chebyshev `ψ` and its Perron interface. Separately, the abstract
  half-log trace theorem now permits a bounded signed profile and weighted signed trace;
  positivity and a one-sided numerator hypothesis are no longer required.
- **Open:** Supply the source-specific exact normal equation, bounded signed profile,
  weighted-trace control and average needed by a named route. The unconditional PNT error
  does not imply CCM-FU's RH-equivalent dyadic subpower window law.
- **Evidence:** [Chebyshev power-log PNT](../../../../formal/GaloisForLFunctions/RHTower/ChebyshevPsiPowerLogPNT.lean), [Perron power-log PNT](../../../../formal/GaloisForLFunctions/RHTower/PerronPowerLogPNT.lean), [signed half-log trace](../../../../formal/GaloisForLFunctions/HTGeometry/LogNormalEquationSignedTrace.lean).

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

The register reconciles committed Lean source through the cutoff above. The 54-file delta
contains 23 HB leaves, 25 other RHTower leaves, four HTGeometry leaves and two import umbrellas.
All changed leaves were inspected for scope; imports and modified statements were compared.
The HTGeometry applications close reusable character-space, partial-trace, cone-separation,
concavity and Lipschitz facts, but supply no new RH source handoff. The Xi-mass additions sharpen
T1's bilinear geometry; they do not prove a Vaughan/Maass estimate.

The 25 active routes and 37 candidates are unchanged; five scoped mechanisms join the
no-go catalogue. No route's independent source estimate, global orientation, affine-collision
control, compact-core coercivity, or canonical QNM extinction theorem was closed.

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
