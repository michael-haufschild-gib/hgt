# Current Formal Frontier Toward Proving or Disproving the Riemann Hypothesis

## Scope, evidence, and status language

This document states where the `HTGeometry`, `HilbertMetric`, and `RHTower` Lean corpus stands now.
It maps architectures, theorem chains, open cores, and terminal mechanisms. It is not a chronology,
work log, literature survey, or inventory of every RH-equivalent proposition.

**Formal-corpus cutoff:** 18 August 2026, commit
`9f81eb328b1d87de4e40d2e4f4010f4efac20b76`, plus declaration-index review of Lean working-tree
sources. Scientific status below comes only from Lean declarations, dependencies, theorem docstrings,
and explicit gap/no-go markers. Pipeline cards and papers are not evidence for this map.

Terms:

- **proved**: unconditional Lean theorem;
- **endpoint**: proved implication/equivalence ending in RH; not evidence for its premise;
- **receiver**: constructed object detecting off-line zero after further source law;
- **producer**: theorem derived from literal arithmetic/analytic source before choosing Xi divisor;
- **open core**: first unproved producer after proved connectors and RH-equivalent reformulations;
- **live route**: source, connector chain, and RH endpoint are formal, with an independent open
  producer problem;
- **candidate**: novel receiver architecture exists, but source handoff or divisor exhaustion does
  not;
- **terminal**: corpus proves proposed producer impossible or all surviving premises RH-equivalent.

RH and its negation remain unproved.

## Executive map

Formal corpus currently supports twelve live architectures: established
`CCM-FU, C1, D2, E, G, L, O, P, Q, T, U`, plus newly separated
**HC (horizontal-collision quantum)**. It supports one especially coherent new candidate,
**IW (internal Weyl descent)**, and several earlier-stage source-mechanism candidates. Route R is
terminal as independent producer.

| Architecture | Proved chain | First open core |
|---|---|---|
| CCM-FU | completed Guinand--Weil third-grade source -> Xi-screw Green -> second-Abel continuation -> RH | Linear growth of one Cesaro primitive of literal third-grade prime-minus-polar cumulative source. |
| C1 | theta/prime--Gamma source -> Weil/Connes positive form or real spectral realization -> RH | Derive positive form or exhaustive real spectral measure from source, not postulated reflection positivity. |
| D2 | continued prime--arch trace -> one-sided anti-Herglotz/finite ceiling -> RH | Uniform source control of sole positive-frequency tail above proved central band. |
| E | squarefree Wold source -> exact integer-pair incidence -> unit-load Hall transport with moving flux -> RH | All-interval Hall/load and co-moving flux for one source-fixed physical relation encoded by exact Ramaré incidence. |
| G | Suzuki/Mobius/Gamma source -> marked pre-scalar boundary carrier -> wall orientation -> RH | Compare normalized zero-mode readout with transported escaped coefficient before scalar erasure. |
| L | completed Green/BV/Big-Witt source -> singular Calderon--Witt comparison -> physical reader -> RH | Bounded square-summable all-prime restriction whose radical is exactly arithmetic boundaries and whose target is existing physical landing. |
| O | exact restricted-Weil operator -> canonical true-ground heads -> coherent signed producer -> nonnegative floor -> RH | Sign of cancellation-preserving coherent finite-head producer, equivalently eventual reverse-prime control on canonical actual heads. |
| P | source-horizontal second-Cartier orbit -> radial Krein energy -> endpoint moderation -> RH | Produce endpoint order globally before divisor selection; finite circle measure after Xi selection and literal scalar short are formally ruled out. |
| Q | continued Hurwitz/Cauchy source -> exterior positive-frequency paired kernel -> orientation zero -> RH | Passivity/PSD of explicit finite reduced prime--Gamma matrices on exterior positive poles. |
| T | finite Xi-Taylor/theta-tail source -> exact reflection bridge -> raw core-current bound -> RH | Joint upper estimate for combined top-row plus surviving finite-translation remainder at same cutoff/depth. |
| U | shifted hard-edge source -> cofinal shifted Hankel tail or first-contact exclusion -> RH | Uniform cofinal source positivity excluding completed-boundary rough null ground. |
| HC | two-prime/Cayley source -> quantized horizontal collision charge -> strict sub-two bound -> RH | Absolute source estimate below indivisible collision quantum for coefficient-faithful finite-window carrier. |

Many exact source criteria below are formal equivalences with RH. Rewriting RH as positivity,
boundedness, passivity, flatness, or collision absence advances nothing unless corpus also supplies an
independent producer. Most remaining problems are constitutive source laws, not formal packaging.

## Live architectures

### CCM-FU — four-unit source-codiagonal incidence

**Architecture.** Literal completed Guinand--Weil source is differentiated to first noncentral
centered response. First two centered jets are blind; cubic jet is Loewner incidence. Incidence is
identified with affine-normalized Xi-screw Green curvature. Three derivatives remove inverse-cubic
grade and recover critical Mellin completed error. A primitive plus second Abel transform gives RH
under linear Cesaro growth.

**Proved.** Corpus contains exact finite source quotient; polar, von-Mangoldt, and singular Gamma
densities; complete restricted-Weil packet; first-jet negative rank-one contraction killed by
centering; central second jet killed by centering; centered PSD cubic Loewner third jet; exact
third-grade/Xi-screw Green identity; second-Abel continuation; RH from every subcubic envelope; RH
from one linear Cesaro primitive; and contrapositive superlinear Cesaro escape under non-RH.

Formal sources: `CCMGuinandWeilPrimeEntryThirdJetTransverse.lean`,
`CCMGuinandWeilXiScrewGreenConnection.lean`,
`CCMGuinandWeilThirdGradeCesaroCompleteness.lean`.

**Open core.** For some fixed `b>0`, prove from literal source

```text
| integral_b^H E_b(h) dh | <= C (H + 1)
```

for every `H>b`, where `E_b` is completed third-grade prime-minus-polar cumulative source. This is
broader than pointwise subcubic control because large oscillations are allowed.

**Closed detours.** First/second jets, arbitrary scalar dressing, and fixed finite quotient are
blind. Unit-Riesz Volterra/Laplace weld is exact and its two lower laws are equivalent without
exponent loss (`CCMUnitRieszCompletedSourceLaplaceWeld.lean`): remaining content is source lower law,
not transform. Positive first-clock Markov transport exists exactly when original scalar is
nonnegative, and universal feasibility is RH
(`CCMFirstClockBarycentricOrientationCompleteness.lean`).

### C1 — Weil/Connes positive spectral realization

**Architecture.** Completed theta or prime--Gamma source is represented as reflection form,
spectral measure, or self-adjoint vacuum. Positivity or real support forces Xi divisor onto centered
real axis.

**Proved.** Complete square-summable Xi Weil form and positivity endpoint; regular two-Cauchy packet
exhaustion (`riemannHypothesis_iff_regularTwoCauchy_nonneg`); finite Laurent/Galerkin sections and
floor convergence; exact finite Schur reduction; prime--arch reflection-positive Gram, endpoint
saturation, and self-adjoint vacuum each equivalent to RH (`PrimeArchConnesReflectionMain.lean`);
two independent dilations force momentum symmetry; positive temperate representation is unique;
theta-null representation is atomic and carried by real Xi divisor
(`TwoDilationSpectralRepresentation.lean`).

**Open core.** Derive from fixed theta/prime--Gamma source, before divisor selection, one of:

1. reflection-positive form on source-dense class exhausting full Weil space;
2. positive two-dilation representation with comparison exhausting complete Xi divisor, not merely
   already-real part;
3. self-adjoint vacuum realization of normalized completed moments.

Bare positivity, saturation, or self-adjoint realization is circular: Lean classifies each as
RH-equivalent. C1 is global class-space architecture; O selects restricted ground and Q restricts to
exterior Cauchy packets. Their open producers differ.

### D2 — continued prime--arch one-sided tail

**Architecture.** Euler-convergent deficit continues to completed prime--Gamma relative trace.
Anti-Herglotz control on centered upper half-strip excludes off-line poles. Corpus reduces global
condition to one positive-frequency tail beyond a proved central band.

**Proved.** Unconditional sign on `|Re z| <= 161/40`; source-pure verified band through radius four;
under any verified-height band only positive tail remains; any finite upper ceiling proves RH and is
equivalent to RH; non-RH forces arbitrarily high positive spikes.

Formal sources: `PrimeArchEndpointFrequencyAccretivity.lean`,
`PrimeArchVerifiedHeightAccretivity.lean`, `PrimeArchSourceUpperBoundGate.lean`.

**Open core.** Prove finite upper control, or stronger anti-Herglotz sign, for literal continued
positive-frequency source tail above radius four from independent source passivity/continuation.
Analytic continuation, central band, reflected negative tail, and countable reduction are closed.
Scalar ceiling itself is exact RH, so viable advance must be stronger source order upstream.

### E — squarefree Wold Hall transport

**Architecture.** Möbius source is reduced to squarefree depth-zero central Wold sector. Exact
Ramaré reindexing turns prime off-diagonal into ordinary integer-pair incidence retaining both
Möbius signs and Mellin kernel. A source-fixed relation must provide distinct opposite-parity
targets with unit normalized load, interval Hall expansion, moving cutoff exchange, and half-power
Gibbs cost.

**Proved.** Two-or-more-large-prime remainder; positive valuation-depth tail; prime-anchor capacity;
opposite-sign supply; every fixed off-normal Wold tail; finite Wold readers; patch seams as exact
coboundary; finite differential-algebraic Euler germs cannot select free infinite prime-clock orbit;
unconditional Step 1 Hall supply (`eventually_fibre_step_one_closed`); exact Type-II cancellation,
cell/family energy, covered-set forms, and covered Type-II power saving
(`MatomakiTeravainenTypeIIAmplitudeCells.lean`); exact ordinary integer-pair incidence
(`RouteERamareIntegerIncidence.lean`).

**Open core.** Construct/extract one exact relation on ordinary squarefree integers directly from
factorization data represented by Ramaré incidence, fixed independently of observed Möbius
imbalance, and prove simultaneously:

1. normalized row load and physical incoming co-degree at most one;
2. Hall expansion for every interval using distinct opposite-sign targets;
3. crossing of co-moving zero/one-large-prime cutoff with charges `-1,+1`;
4. total mixed-difference Gibbs cost `X^(1/2+o(1))`.

Step 1, Type-II amplitude cells, and seam estimates are no longer frontier. Existential complete
bipartite transport is not enough: its defect is original Möbius imbalance. On squarefree hard
support valuation depth is fixed; hard axis is all-prime breadth.

### G — marked Suzuki/Mobius/Gamma boundary orientation

**Architecture.** Source current is retained before scalarization as affine carrier containing
completed prime--polar--Gamma charge and marked odd clock jet. It is transported to
Suzuki/restricted-Weil boundary receiver. RH follows if coefficient-faithful boundary
renormalization makes escaped coefficient pay zero-mode debt with correct orientation.

**Proved.** Source-native affine producer retaining charge and source orders; canonical probe
detects nonzero charge; zero-clock jet vanishes while charge survives; positive-clock packet retains
odd jet; exact scalar readout/ports (`MobiusGammaXiPreScalarAffinePrimePolarGammaProducer.lean`);
first Xi Livsic defect and persistent Suzuki leakage floor (`SuzukiXiFirstDefectJetSource.lean`);
unique Gamma/Euler boundary renormalization; coefficient-faithful Wold domination of boundary
Hessian; universal domination RH-equivalent; scalar cancellation reduces to RH or universal source
erasure; actual multiplicity-faithful Euler--Wold transverse reporter converges to half primitive
budget and eventually lies strictly inside budget, while no linear reporter can both remain
source-budgeted and dominate literal endpoint
(`SourceHorizontalEulerWoldTransverseDefectBudgetReporter.lean`).

**Open core.** Construct pre-scalar boundary comparison transporting prime label, multiplicity, and
escaped coefficient; compare it to normalized zero-mode debt; exclude universal erasure; and prove
favorable signed inequality on actual wall/ground state. More floor identities, positive scalar
shadows, or zero-clock commutators cannot close route because Lean separates surviving charge from
vanishing jet. Transverse half-budget reporter closes source occurrence but also proves missing
endpoint comparison must be nonlinear or distinct-channel, not another linear budget reporter.

### L — Deninger/Green/Cartier singular boundary comparison

**Architecture.** Completed Xi Green primitive and BV/Big-Witt arithmetic boundary are sent to
resolved Calderon--Witt/Meyer target. Physical reader must kill genuine target boundaries while
recovering Burnol/Deninger coefficient. This forces conormal defect `K_n(rho)` to vanish.

**Proved.** Completed Xi Green operator and nonzero primitive; coefficient-faithful isometric
Green-to-Calderon--Witt comparison; relative Tate boundary/top-coordinate recovery; Burnol conormal
classification; ordinary-integer Hochschild boundary; cross-prime Koszul cycle retaining Xi
coefficient; rational-adelic relative complex and strict resolved-Xi chain map; Big-Witt
Frobenius-two ghost transgression reading exact physical seam
(`DeningerBigWittFrobeniusPrimeSeamTransgression.lean`); pullback of nonnegative Green forms with
radical=kernel (`DeningerGreenFormPullbackTransport.lean`); continuous packet restrictions under
square summability; singular Gamma transgression whose sewing cost beats every finite Rees order
(`DeningerCalderonWittSingularGammaTransgression.lean`); physical residue/minimal-boundary critical
line classification with prime and multiplicity provenance
(`MobiusThetaSourceDaggerMinimalBoundaryLaw.lean`).

**Open core.** Construct source-derived bounded square-summable continuous all-prime restriction
such that common kernel is exactly arithmetic boundary subspace, target-zero component is existing
physical landing, reader kills resulting boundaries, prime/depth/multiplicity survive, and
construction precedes divisor. Equivalently: prove radical-identification for continuous Green
restriction together with physical-landing comparison.

**Closed detours.** Residue-factored packet cannot classify boundaries unless middle cohomology is
already trivial; cofinite unit-normalized packet floor forbids square summability; generic mapping
cones/Koszul exactness merely relocate or erase `K_n`; finite Rees completion cannot match
exponential sewing singularity.

### O — exact restricted-Weil ground and canonical actual heads

**Architecture.** Exact restricted-Weil Friedrichs operator has ground energy `epsilon_a`.
Canonical finite Gamma--Slepian heads are extracted from true ground, converge to it, and carry
literal prime, polar, Gamma, endpoint, and completed-error blocks. Exact cancellation reduces floor
nonnegativity to sign of one coherent signed producer on actual heads.

**Proved.** Exact self-adjoint operator and true Rayleigh floor; attained nonzero ground
representative; aperture antitonicity/continuity; non-RH gives negative ground; Laurent/Galerkin and
Gamma--Slepian finite reductions; canonical true-ground heads converge quantitatively; eventual
reverse-prime inequality on heads iff ground nonnegative; same inequality iff sign of actual
completed-error, signed Gamma, Gamma-wall, wall-Gram, and coherent completed-Gamma producers;
monotone quantile transport cancels prime/polar mass cellwise; coherent operator-valued producer is
exact; pointwise completed-symbol positivity suffices.

Formal sources: `CCMRestrictedWeilCanonicalGroundHeadEnergy.lean`,
`CCMRestrictedWeilActualHeadCompletedErrorProducer.lean`,
`CCMActualHeadSignedCompletedErrorGammaProducer.lean`,
`CCMActualHeadOutgoingQuantileTransportProducer.lean`,
`CCMActualHeadCoherentCompletedGammaProducer.lean`,
`CCMActualHeadCoherentQuantileGammaProducer.lean`.

**Open core.** At every aperture, prove cofinally on canonical actual heads literal reverse-prime
bound, equivalently nonnegativity of cancellation-preserving coherent completed producer at exact
threshold. Stronger sufficient target: pointwise nonnegative completed symbol.

This supersedes old prolate-seed frontier. Canonical heads are now selected from true ground and
converge to it. Remaining problem is arithmetic sign on those heads, not constructing/evaluating a
seed or classifying all near-ground profiles. Unsigned Gamma envelopes and phase-free chi-square
separation cannot replace inseparable joint producer.

### P — source-horizontal second-Cartier orbit moderation

**Architecture.** Primitive Euler/Burnol source produces second-Cartier/Krein-polarized ghost orbit.
Exact energy measures reciprocal radial escape. Bounded orbit is endpoint moderation; strict-right
Xi divisor forces unbounded escape. Source theorem bounding actual orbits would prove RH.

**Proved.** Second-Cartier orbit/Krein polarization; exact radial energy decomposition; bounded iff
unit character; every strict-right actual Xi orbit unbounded with energy tending to infinity;
endpoint moderation iff bounded orbit; universal actual-orbit boundedness iff RH
(`SourceHorizontalSecondCartierOrbitCoercivity.lean`); bilateral non-scalar admission/topology;
finite positive circle moments are moderate, no finite circle measure represents any occupied
strict-right literal endpoint, universal representability is RH-equivalent, and no scalar multiple
of the literal non-spectral conormal short bounds actual radial energy
(`SourceHorizontalSecondCartierCompactCircleFirewall.lean`);
completed conormal base residue and Cauchy-cube Gram; primitive base trace budget below one;
strictly positive radial source work and exact positive-gain equality between Ward anomaly energy
and radial work (`HedenmalmThetaAnomalyWardRadialSourceWorkBridge.lean`); Gamma-six shell Green
moments agree coefficientwise with Wold prime-clock moments, while equality of reflected shell
responses is exactly critical-line condition (`SourceHorizontalShellGreenPrimeClockProfile.lean`).

**Open core.** Derive endpoint moderation/order globally from literal completed source before divisor
selection while retaining coefficient and multiplicity. Universal boundedness and universal finite
circle representability are RH-equivalent. Post-selected compact positive-measure admission is
impossible on every strict-right copy, and the literal static conormal short admits no uniform orbit
budget. Viable producer must therefore be pre-divisor and source-natural; indefinite conservation,
determinant, Krein form, compactness language, or scalar shorting cannot supply it.

### Q — Hurwitz/Cauchy source orientation

**Architecture.** Canonical Hurwitz orientation vector measures FE-versus-Schwarz transverse defect.
Continued prime--Gamma Cauchy packets reconstruct vector and energy. Exterior positive-frequency
Schwarz-paired packets suffice. Passivity of explicit finite reduced kernel forces orientation zero.

**Proved.** Orientation energy is nonnegative, convergent, multiplicity-sensitive, zero iff RH;
explicit separated packet sequence converges to orientation vector; eventual sequence
nonnegativity iff RH; vector lies in exterior Cauchy closure beyond any admissible band; positivity
only on exterior core implies RH; vector lies in positive-frequency paired closure; four-block
paired kernel reduces to one real positive-frequency kernel; finite reduced matrix passivity iff RH
and radius `218/25` suffices; exact squared distance to nonnegative Weil cone is
`orientationEnergy/2`; two null boundary axes have mixed incidence `-orientationEnergy/2`; off RH
mixed incidence dominates separately positive diagonal energies.

Formal sources: `XiHurwitzOrientationSeparatedSourceReconstruction.lean`,
`XiHurwitzOrientationExteriorCauchyClosure.lean`,
`XiHurwitzOrientationPositivePairedSource.lean`,
`XiHurwitzOrientationSharpNonnegativeConeDistance.lean`,
`XiHurwitzOrientationBoundaryMixedIncidence.lean`.

**Open core.** Prove PSD of explicit finite one-sided reduced prime--Gamma kernel matrices on
separated positive exterior poles from source passivity or stronger order. Packet construction,
exterior exhaustion, positive-frequency reduction, and central-band removal are closed. More
diagonal budgets cannot work: missing datum is mixed polarized incidence. Monotone quantile
transport preserves distribution but remains orientation-blind.

### T — Xi-Taylor/theta-tail finite-arithmetic core current

**Architecture.** Canonical theta-tail core current is represented through finite arithmetic at
minimal Prouhet order. Reflection returns prefix and creates top row plus finite-translation
survivor. Existing finite coefficient gate turns sublinear raw-current bound into RH.

**Proved.** Exact finite-arithmetic raw bridge; canonical Prouhet order/prefix; top-row current real;
at fixed cutoff top row tends to zero but translation survivor tends to conserved raw-current
residue; between depths every top-row change transfers oppositely into survivor; combined remainder
equals raw current minus returned prefix and is depth-independent; joint selector controls
prefix/top interface; conditional capstone isolates one combined-remainder estimate; favorable
coherent product-fibre base and unavoidable corrected joint seam are exact.

Formal sources: `XiCTaylorThetaTailCoreCurrentCapstone.lean`,
`XiCTaylorThetaTailProductFiberHermitianCollapse.lean`.

**Open core.** Prove joint upper estimate for
`canonicalThetaTailCoreFiniteArithmeticRemainderCurrent` at same cutoff and depth as prefix selector,
retaining cancellation between top-row and translation pieces. More top-row decay is dead work:
survivor conserves exactly what row loses. Separate absolute-value bounds destroy sign.

Finite-Hermite contour, critical mass/Dirichlet cone, co-moving mass cone, and sharp spacelike
summability are alternative formal receivers/partial decompositions. Current most concrete single
quantity is combined finite-arithmetic remainder.

### U — shifted Hankel hard edge and completed-boundary first contact

**Architecture.** Shifted-Xi Hankel blocks and canonical source moments form degree/mass tower. RH
follows from one cofinal fixed-shift Hankel tail or exclusion of first completed-boundary null ground
in restricted-Weil path.

**Proved.** Source-only shifted reciprocal moments are negative-binomial transforms of completed
prime--Gamma moments; every finite prefix may be discarded; shift-one source tail nonnegativity iff
RH; cofinal tail positivity makes translated Xi atoms real; endpoint window/dyadic interfaces close;
adaptive Jacobi differences reduce to diagonal connection; every fixed pair and finite prefix is
eventually ordered; fixed-degree positivity does not control prescribed cofinal diagonal; arbitrarily
fast positive recession schedules with divergent spread exist; non-RH first zero contact is genuine
completion-boundary rough null vector absent from strict smooth interior; no scalar counterterm
renormalizes interior and physical Kelvin charts together; every occupied strict terminal-frontier
rung carries exact adaptive source price, and non-RH produces such source-priced strict renewal
events above every mass threshold (`XiShiftedHankelStrictFrontierCurvatureRenewal.lean`). Thus
cofinal producer admission is closed; favorable sign/exclusion is not.

Formal sources: `XiShiftedReciprocalHankelTailCriterion.lean`,
`XiShiftedCanonicalAdmissionAdaptiveArithmeticSourceDegreeConnection.lean`,
`XiShiftedCanonicalAdmissionCofinalScheduleNoGo.lean`,
`SuzukiFirstContactBoundaryRoughness.lean`,
`XiShiftedHardEdgePrimeGammaKelvinTwoChartNoGo.lean`.

**Open core.** Prove uniform cofinal tail positivity/order for explicit source Hankel matrices, or
construct non-scalar boundary trace/quotient excluding rough first-contact ground. Proof must
synchronize degree with mass/aperture and control upper rate, not fixed-degree limits or positivity
along self-selected recession schedule.

### HC — horizontal-collision quantum

This is not a classical zero-free-region, explicit-formula sign, de Branges, or ordinary
self-adjoint-spectrum route. Primitive invariant is integer-valued multiplicity incidence
reconstructed from coefficient-faithful prime clocks and non-equivariant horizontal Cayley phase.

**Architecture.** Two incommensurable prime clocks separate ordinates. Horizontal Cayley depth
resolves points inside each ordinate fibre. Difference between reflection-quotiented depth zero and
resolved finite depth is information loss. Limit is exact horizontal collision charge. Every
off-line reflected pair contributes indivisible quantum two; absolute bound below two forces RH.

**Proved.** Horizontal collision charge is exact ordered-pair multiplicity census, even and
monotone; reflection self-intersection charge is squared off-line order; collision splits into
forced reflection incidence plus accidental collisions; two-prime phase separates ordinate pairs;
source, phase, and grouped pencils agree; Cesaro energy converges to fibre energy; source excess
converges to collision charge; RH iff source excess tends to zero; eventual excess `<2` iff RH;
three-depth Cayley pencil retains prime labels, both orientations, multiplicity, and source phase;
information loss converges to collision charge; eventual loss `<2` proves RH; Ward--Green
normalization gives stronger uniform quantum; coefficient-faithful exterior contours detect same
boundary quantum; full exterior prime-Cayley source pencil retains both adjacent orientations and
dephases exactly to multiplicity-square packet energy, with RH equivalent to that finite source
energy tending to zero (`XiHorizontalCollisionWardGreenExteriorSourceCarrier.lean`).

Formal sources: `XiHorizontalCollisionChargeEndpoint.lean`,
`XiReflectionSelfIntersectionCharge.lean`,
`XiHorizontalCollisionTwoPrimeCesaroCarrier.lean`,
`XiHorizontalCollisionPrimeCayleyInformationLoss.lean`,
`XiHorizontalCollisionWardGreenCayleyQuantum.lean`,
`XiHorizontalCollisionWardGreenExteriorSourceCarrier.lean`,
`HedenmalmCoefficientFaithfulExteriorSourceContour.lean`,
`HedenmalmExteriorSourceThetaBoundaryGap.lean`.

**Open core.** Prove from finite coefficient-faithful prime--Gamma source carrier, before divisor
specialization, an absolute strict-subquantum bound for source excess/information loss on all late
windows. Normalized `o(N(T))` is insufficient: bound must cross integer quantum two.

HC is genuinely new architecture because mechanism is source-resolution loss versus quantized
reflection incidence, not positivity of classical explicit formula. Global strict-two law is itself
RH-equivalent; progress must be upstream arithmetic evaluation/cancellation of finite source pencil.

## Corpus-born candidate openings

These are Lean architectures, not literature-shaped suggestions. They are not counted as live until
source handoff is built independently of zero tested.

### IW — internal dyadic Weyl descent

`WeldWeylMultiplicity.lean` proves primitive order-`2^k` Weyl commutation forces `2^k` divisibility;
internal Weyl model on actual undoubled SEM hole space gives one RH rung; models at all or cofinal
depths force RH. Open theorem: construct Weyl actions internally from arithmetic source. Auxiliary
tensor factors are forbidden because they manufacture divisibility.

### AP — Arakelov power orbit

`ArakelovPowerOrbitRH.lean` proves explicit `w -> w^n` lift, right-half preservation, convergence to
nonzero Xi anchor, and RH from divisor stability or preperiodicity. Bare stability/preperiodicity is
RH-equivalent. Open theorem: global source endomorphism inducing power law before zero selection.

### SC — prime--Gamma Stokes/Coxeter

`PrimeGammaStokesCoxeterRH.lean` proves Coxeter preservation of symmetrized Seifert form and unit
eigenvalue modulus under positive realization. Zero-indexed unitary packets force RH and are
RH-equivalent. Open theorem: global completed prime--Gamma Stokes/Seifert category, positive form,
and Xi determinant comparison before divisor selection.

### PPM — prime-power centered-mark collision

`PrimePowerCenteredMarkRH.lean` proves centered mark radius encodes horizontal coordinate,
reflection inverts mark, and prime-power Adams law is source-correct. One right-half collision forces
RH; bare collision predicate is RH-equivalent. Open theorem: source forces actual prime-power
collision/finite monodromy globally.

### IRK — irrational-rotation `K_0`

`PrimeIrrationalRotationKZeroRH.lean` proves concrete rotation parameter irrational and integer
trace collision forces Chern coordinate zero. Trace/Chern data at every right-half zero gives RH.
Open theorem: source projective module whose trace is analytic rank and Chern charge is local
off-line multiplicity before zero selection.

### OPUC — paraorthogonal phase gate

`XiOPUCParaorthogonalPhaseGate.lean` and `HTGeometry/ParaorthogonalBlaschkeRoot.lean` prove finite
paraorthogonal roots on unit circle and RH from stable terminal whose dyadic-phase value is nonzero
source multiple of `XiC`. Open theorem: source Toeplitz/OPUC sections plus convergence/value
comparison. Current code is endpoint, not approximation theorem.

### HJ — Hurwitz anchor-jet projective reflection

`XiHurwitzAnchorJetProjectiveReflection.lean` proves complete positive-order projective anchor-jet
compatibility at Xi zero iff critical line; global law iff RH. Open theorem: global source
projective reflection law before divisor selection. This is adjacent to Q but currently receiver.

### TD — two-dilation theta-null representation

`TwoDilationSpectralRepresentation.lean` gives unique positive temperate measure and real-divisor
support for theta-null two-dilation form. Missing theorem is exhaustive comparison with full Xi
divisor. Until exhaustion, TD is C1 subarchitecture, not independent route.

### BW — barrelled prime-depth Wold selection

`PrimeDepthBVWoldBarrelledSourceSelector.lean` proves a Banach--Steinhaus null-orbit principle and
packages exact completed-source certificate: barrelled completion, null cofinal orbit, pointwise
bounded continuous readouts, coefficient preservation, and physical landing. One certificate forces
critical-line placement; a global producer proves RH.

Open theorem: construct global completed barrelled-source certificate from literal prime-depth BV/Wold
source. Current structure names genuine source obligations rather than replacing them by a scalar
summability predicate, but no unconditional global witness exists. BW remains candidate adjacent to
L/P.

### AF — adaptive Fisher contiguity selection

`SourceHorizontalAdaptiveFisherCofinalContiguitySelection.lean` proves reflected adaptive prime
occupation has unbounded Jeffreys work off neutral grade; finite source laws with absolute continuity
cannot support asymptotically perfect separating tests; and actual convergent abelian class laws
supply contiguity. A coefficient-faithful adaptive scale-orbit certificate forces centered rate zero,
and certificates on all multiplicity-resolved Xi copies prove RH.

Open theorem: construct those adaptive class-law scale-orbit certificates globally from source,
before choosing Xi copy. The certificate is more source-specific than bare orbit boundedness but
remains zero-indexed until global handoff is built.

## Terminal and retired mechanisms

Closure applies to named mechanism, not every future use of similar objects.

| Route/mechanism | Terminal statement | Positive survivor |
|---|---|---|
| A | Source-faithful fixed physical-phase transport is identity; nonidentity has connection defect. Positive Markov feasibility is source sign; universal feasibility is RH. | Phase-natural rigidity and barycentric completeness. |
| B | Scaling/grading and distinct prolate parameters cannot share required unitary transport; finite real-zero receiver lacks source orientation. | Relative graph/boundary deformation only. |
| C2/I | Finite theta/dyadic width saturates coordinate; missing width is RH-bearing. | Cauchy/Hurwitz interfaces survive in Q. |
| D1 | Finite/local moment positivity does not orient completed all-degree source. | D2 continued tail and Q exterior kernel. |
| F | Compact Sonin completion/correction has wrong asymptotic order or collapses source. | New order-one pre-Gamma primitive only. |
| G2 | Required relative-Volterra germ is RH-equivalent. | G marked boundary problem survives. |
| H | Even Taylor factorization loses orientation. | Relation-valued indefinite primitive only. |
| J | For `L_m=6 log m`, `m>=25`, bad energy is at least `log(m)/20` at every Julia scale; uniform budget impossible; diagonal subtraction breaks one-node capacity. | Principal-relative current defined before projection; not Route J. |
| K | Quadratic spectral mechanism cannot retain marked source. | Nonlinear incidence in P/HC. |
| M | Gamma--Jacobi reader complete; anchored cofinal flatness is RH. | Receiver only. |
| N | Response equality, endpoint contractivity, or bounded polar work is RH-equivalent. | Shared receiver for L/P/G. |
| R | Intrinsic producer category empty; every surviving external interface RH-equivalent. | Quartic amplitude, singular cap, and physical landing remain reusable receivers. |
| direct prime Ising | Raw/scalar-normalized finite balanced tree partitions cannot converge locally uniformly to XiC; rank growth forces scale collapse. | Only singular critical rescaling outside fixed modal closure could be new. |
| compact Thorin/Markov | Compact Thorin and Markov representations are RH-equivalent; canonical measure unique; theta-likelihood candidate not infinitely divisible. | Upstream positive source measure only, not alternative canonical measure. |

### Route R exact closure

`RouteRTerminalProducerClassification.lean` proves
`routeR_intrinsic_dead_external_equivalent`,
`nonempty_routeRSurvivingProducer_iff_riemannHypothesis`,
`routeRXiCalkinFactorization_iff_riemannHypothesis`, and
`routeRLossZeroFisherPhysicalLanding_iff_riemannHypothesis`.
`RouteRPreDivisorGammaCoronaGlobalizationNoGo.lean` proves no pre-divisor Gamma-corona globalizer.
`RouteRHyperbolicGaugeQuarticPhysicalProducer.lean` constructs unconditional quartic landing and
proves quadratic comparison no-go. R contributed novel architecture/invariants, but no intrinsic
producer survives. It is closed negatively as RH route.

### Cross-cutting formal no-go laws

Corpus proves insufficient:

- finite real-linear probes, seam jets, finite-codimension conditions, prescribed finite symmetry
  jets, exact order, and translation differential-algebraic freeness;
- finite-rank repair invisible on boundary-map kernel and zero-fed Uvarov tautology;
- fixed finite Hankel rank, fixed-degree reciprocal blocks, and one-sided quadratic bounds;
- unrestricted nonnegative source weights for nonzero fixed Loewner budget;
- scalar real-axis inverse-kernel positivity for off-curve Hermitian positivity;
- positive Euler coefficients for PF2/variation-diminishing transfer;
- coefficientwise-positive Li-to-shifted-moment transfer;
- bare `ell^2` closure of finite coefficient summation;
- linear reflection cancellation as substitute for quadratic reflection incidence;
- fixed-degree positive limits as control of degree-matched cofinal diagonal;
- scalar counterterms for incompatible interior/boundary charts;
- source symmetry as proof every orbit point is fixed.

Any successor must retain infinite source provenance, mixed incidence, non-scalar boundary
coordinate, cofinal uniformity, or internal action on actual carrier.

## What routes have in common

### Source/receiver firewall

Almost every route has perfect off-line detector. Hard part is independent source law feeding it.
Reverse implications increasingly turn attractive premise into exact RH equivalence. This locates
circularity boundary.

### Orientation survives where scalar positivity fails

Functional equation and Schwarz reflection supply two orientations. Norms, squares, determinants,
positive Markov transport, diagonal energies, and scalar moments often erase difference. Successful
receivers retain reflection-odd current, mixed incidence, prime phase, signed transgression,
non-equivariant Cayley depth, or projective monodromy/Chern charge.

### Quantized obstructions beat normalized asymptotics

HC and IW exploit indivisible integers: collision quantum two, squared reflection order, or
divisibility by `2^k`. Normalized `o(N)` can coexist with finitely many bad atoms. Source estimate
must cross absolute quantum threshold.

### Ground selection replaced seed construction

Route O has exact true ground and canonical finite heads. Remaining theorem is sign on actual
ground-selected producer, not better trial vector. Across C1/G/O/U finite sections and compactness
are mostly closed; arithmetic order on selected state remains.

### Order of limits is structural

Fixed degree/aperture/packet/source quotient often behaves well while failure moves diagonally. U
gives explicit countermodel and actual escape schedules. T shows refinement transfers current
rather than removing it. Cofinal argument needs synchronized estimate, not iterated pointwise limits.

### Singular boundary is not removable technicality

L, G, P, U, and O reach completion boundary where smooth interior misses state. Gamma sewing beats
finite Rees order; Kelvin charts cannot share scalar renormalization; first contact can be rough.
Needed objects are relative, graph-valued, nonlocal, or non-scalar.

### Non-classical corpus-born mechanism family

HC, IW, AP, SC, PPM, IRK, and HJ share architecture:

```text
literal source operation
  -> internal orbit / monodromy / incidence / information loss
  -> discrete rigidity or quantum threshold
  -> exclusion of off-line divisor
```

Common danger is zero-indexed vacuity. Valid proof must build global source operation before choosing
divisor. HC is furthest because coefficient-faithful finite source carrier and exact quantized limit
already exist; only source estimate remains.

## Fundamental nature of remaining problems

Open cores fall into six classes:

1. **Arithmetic source order:** sign/boundedness/passivity for literal completed prime--Gamma or
   Möbius object (CCM-FU, D2, E, Q, T).
2. **Ground-relative coercivity:** control exact state selected by full operator, not one seed or
   generic packet (C1, O, G, U).
3. **Singular boundary descent:** physical comparison across completion boundary without losing
   coefficient, multiplicity, or orientation (G, L, P, U).
4. **Mixed-incidence control:** preserve cross terms diagonal energies erase (E, Q, HC, T).
5. **Cofinal synchronization:** one estimate uniform in moving degree/aperture/height
   (CCM-FU, E, O, T, U).
6. **Source-native internal dynamics:** endomorphism, Weyl action, projective module, Stokes category,
   or monodromy on actual arithmetic carrier before divisor selection (IW, AP, SC, PPM, IRK, OPUC,
   HJ).

Fundamental remaining obstruction is not another equivalent criterion. Corpus already has many. It
is:

> derive favorable global order or discrete rigidity from literal completed source while retaining
> orientation and mixed incidence erased by scalarization, finite truncation, and post-divisor
> fitting.

## Highest-value questions exposed by Lean

1. Can third-grade Guinand--Weil cumulative source have linearly bounded primitive without zero-free
   input?
2. Can positive-frequency prime--arch trace be controlled by source passivity stronger than its
   RH-equivalent scalar ceiling?
3. What exact squarefree relation realizes Ramaré incidence with unit all-interval Hall load and
   co-moving flux?
4. Can marked Gamma renormalization compare escaped coefficient to zero-mode debt pre-scalar?
5. Can all-prime Green restriction be square-summable with common kernel exactly arithmetic
   boundary and target existing physical landing?
6. Is completed CCM symbol nonnegative on every canonical actual-head density?
7. What pre-divisor completed-source law forces moderation of the literal second-Cartier endpoint,
   despite the proved post-selected finite-measure and scalar-short firewalls?
8. Why is explicit positive-frequency reduced Cauchy kernel PSD on every exterior finite packet?
9. What joint estimate controls T depth-invariant top-row/translation remainder without splitting
   cancellation?
10. What uniform degree--mass law proves shifted reciprocal Hankel tail positivity or excludes rough
    first contact?
11. Can two-prime source excess be bounded absolutely below collision quantum two?
12. Can arithmetic source construct internal dyadic Weyl pair on actual undoubled hole space?
13. Can source globalize Arakelov power, Coxeter, prime-power collision, irrational-rotation `K_0`,
    paraorthogonal phase, or Hurwitz projective reflection before divisor selection?

Until one is answered, endpoint reformulations, finite real-zero models, seed asymptotics, diagonal
moment inequalities, or scalar transport identities do not move formal RH frontier.
