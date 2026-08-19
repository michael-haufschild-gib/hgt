# Current Formal Frontier Toward Proving or Disproving the Riemann Hypothesis

## Scope, evidence, and status language

This document states where the `HTGeometry`, `HilbertMetric`, and `RHTower` Lean corpus stands now.
It maps architectures, theorem chains, open cores, and terminal mechanisms. It is not a chronology,
work log, literature survey, or inventory of every RH-equivalent proposition.

**Formal-corpus cutoff:** 19 August 2026, commit
`f5844561598ffba3d02fb5e207a5e9fcc5baef1d`, plus declaration-index review of current Lean
working-tree sources. Scientific status below comes only from Lean declarations, dependencies,
theorem docstrings, and explicit gap/no-go markers. Pipeline cards and papers are not evidence for
this map. Working-tree declarations are identified as corpus source, not claimed build-audited in
this documentation-only pass.

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
**HC (horizontal-collision quantum)**. Eight corpus-born receiver/source-mechanism candidates
remain: `SC, PPM, IRK, OPUC, HJ, BW, MSC, SV2`. Routes R, IW, and AP are terminal as independent
producers. No latest Lean addition closes an open source premise or proves/disproves RH.

| Architecture | Proved chain | First open core |
|---|---|---|
| CCM-FU | completed Guinand--Weil third-grade source -> exact signed FU reporter -> Xi-screw Green -> second-Abel continuation -> RH | Linear growth of one Cesaro primitive of literal third-grade prime-minus-polar cumulative source; exact signed-symbol cancellation and lower-wall escape are closed. |
| C1 | corrected theta/prime--Gamma source -> Weil/Connes form or real spectral realization -> RH | Construct a source-derived non-dominating or signed correction before final positivity; raw positive/passive Stokes completion is impossible. |
| D2 | continued prime--arch trace -> one-sided anti-Herglotz/finite ceiling -> RH | Source control of sole positive-frequency tail by a reflected signed/non-dominating law; canonical directed passive limits are impossible. |
| E | squarefree Wold source -> two-sign half-power marker supply -> exact integer-pair incidence -> unit-load Hall transport with moving flux -> RH | Build one Ramaré-supported relation joining proved marker supply to relation-specific subinterval Hall, unit load, co-moving flux, and Gibbs cost. |
| G | Suzuki/Mobius/Gamma source -> marked pre-scalar or signed-channel carrier -> exact Ward landing -> wall orientation -> RH | Independent source law forcing the already-transported Ward coefficient to vanish or have the required signed order; Schur coisometry and causal limit do not supply four-unit orientation. |
| L | completed Green/BV/Big-Witt source -> singular Calderon--Witt comparison -> physical reader -> RH | Source-derived singular comparison identifying resolved boundary flatness with existing coefficient-faithful Burnol/Deninger physical landing before divisor specialization. |
| O | exact restricted-Weil operator -> canonical true-ground heads -> coherent signed producer -> nonnegative floor -> RH | Sign of cancellation-preserving coherent finite-head producer, equivalently eventual reverse-prime control on canonical actual heads. |
| P | source-horizontal second-Cartier orbit -> Route-N capacity/radial-work bridge -> radial Krein energy -> endpoint moderation -> RH | Produce endpoint order globally before divisor selection; regular reflection-pair extraction, finite circle measure, and literal scalar short are formally ruled out. |
| Q | continued Hurwitz/Cauchy source -> exterior positive-frequency paired kernel -> orientation zero -> RH | Passivity/PSD of explicit finite reduced prime--Gamma matrices on exterior positive poles. |
| T | finite Xi-Taylor/theta-tail source -> exact reflection bridge -> raw core-current bound -> RH | Joint upper estimate for combined top-row plus surviving finite-translation remainder; in the endpoint specialization, pure short Möbius-block cancellation. |
| U | shifted hard-edge source -> cofinal shifted Hankel tail or first-contact exclusion -> RH | Non-scalar source mechanism excluding the exact nonintegrable strict-frontier quotient, or uniform cofinal tail order. |
| HC | two-prime/Cayley/Gauss--Hodge source -> quantized horizontal collision charge -> strict sub-two or prime-summability law -> RH | Absolute subquantum estimate or source-first prime-summability for the literal paired Gamma-six determinant current. |

Latest corpus changes narrow `CCM-FU, E, G, L, P` and add candidates `MSC, SV2`. They do not move
the first open producer of `D2, O, Q, T, U, HC`. C1 gains a generic trace-class reduction but no
source carrier or spectral orientation. In particular, midpoint polar--prime positivity is a scalar
square identity and has not been transported to O's canonical actual heads; new sieve mean-value
lemmas do not yet prove T's short Möbius block estimate.

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
from one linear Cesaro primitive; and contrapositive superlinear Cesaro escape under non-RH. The
limiting FU reporter now retains both sign regions and its boundary atom in one exact symbol

```text
M(a) = -3 a^2 / (32 (a + 1) (2a + 1)),    a > -1/2,
```

with complex half-plane zero set reduced to the double affine zero at `0`. Its literal finite
source-relative aperture equals this curvature response plus the explicit lower-wall value/first
jet, and that escaped jet tends to zero cofinally for every real critical-Mellin exponent. Separately,
the midpoint-read polar--prime Stieltjes codiagonal is exactly one half of the squared completed
error; midpoint coefficient `1/2` is forced by the prime jump debt.

Formal sources: `CCMGuinandWeilPrimeEntryThirdJetTransverse.lean`,
`CCMGuinandWeilXiScrewGreenConnection.lean`,
`CCMGuinandWeilThirdGradeCesaroCompleteness.lean`,
`CCMUnitRieszCesaroSignedReporterSymbol.lean`,
`CCMUnitRieszCesaroSourceRelativeReporter.lean`,
`CCMPolarPrimeMidpointCodiagonal.lean`.

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
(`CCMFirstClockBarycentricOrientationCompleteness.lean`). Estimating positive and negative FU
regions separately, invoking vertical cancellation, or discarding the positive source wall is no
longer a plausible missing step: exact symbol and escaped-jet laws settle all three. Midpoint
codiagonal positivity is an identity `E^2/2`, not an upper bound on `E`, so it does not close the
Cesaro source estimate.

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
(`TwoDilationSpectralRepresentation.lean`). The canonical reflected critical Stokes source already
has excessive zeroth mass (`not_gammaSewnMobiusApertureStokesCriticalMomentIdentification`), and no
finite positive measure dominating that raw carrier can represent the completed seam germ
(`not_gammaSewnMobiusApertureStokesCriticalPositiveSupercarrierCompletion`).
The one-prime trace-class propagation step is also closed abstractly: a trace-class, finite-rank,
Hilbert--Schmidt-factorized, or nuclear remainder changes every positive modulus power only by a
Schatten-one operator (`ConnesConsaniTraceClassReduction.lean`). This does not construct the literal
one-prime remainder or orient the resulting spectrum.

**Open core.** Derive from fixed theta/prime--Gamma source, before divisor selection, one of:

1. corrected reflection form on a source-dense class exhausting full Weil space;
2. a source-derived carrier which deletes or reweights raw Stokes atoms before final positivity, or
   introduces a signed negative correction and proves the corrected realization exhaustive;
3. self-adjoint vacuum realization of corrected normalized completed moments.

Bare positivity, saturation, or self-adjoint realization is circular: Lean classifies each as
RH-equivalent. More strongly, passive positive completion retaining the canonical raw atoms is now
formally impossible. The exact survivor is non-domination:
`criticalStokes_not_le_of_completedSeamMomentGerm_eq_compactMarkov`. Reflection repairs parity but
not normalization, and the first-moment excess also rules out a constant positive counterterm. TD
therefore survives only as a real-divisor receiver; its stated raw-positive/passive source handoff is
terminal. C1 remains live only through a genuinely corrected, signed/indefinite, or non-dominating
class-space construction. O selects restricted ground and Q restricts to exterior Cauchy packets;
their producers differ.

### D2 — continued prime--arch one-sided tail

**Architecture.** Euler-convergent deficit continues to completed prime--Gamma relative trace.
Anti-Herglotz control on centered upper half-strip excludes off-line poles. Corpus reduces global
condition to one positive-frequency tail beyond a proved central band.

**Proved.** Unconditional sign on `|Re z| <= 161/40`; source-pure verified band through radius four;
under any verified-height band only positive tail remains; any finite upper ceiling proves RH and is
equivalent to RH; non-RH forces arbitrarily high positive spikes. At the fixed centered point `I/4`,
the completed response has zero real part while canonical directed prime-log KMS and subcritical
Stokes limits have incompatible strict real signs. Hence neither directed passive family can
converge to the completed prime--Gamma source
(`PrimeArchDirectedPassiveParityNoGo.lean`). Reflected finite Stokes response restores exact odd
parity and passivity, but the C1 positive-supercarrier theorem blocks positive normalization that
retains all raw atoms.

Formal sources: `PrimeArchEndpointFrequencyAccretivity.lean`,
`PrimeArchVerifiedHeightAccretivity.lean`, `PrimeArchSourceUpperBoundGate.lean`.

**Open core.** Prove finite upper control, or stronger anti-Herglotz sign, for literal continued
positive-frequency source tail above radius four from an independent reflected signed or
non-dominating continuation law.
Analytic continuation, central band, reflected negative tail, and countable reduction are closed.
Scalar ceiling itself is exact RH, so viable advance must be stronger source order upstream.
Canonical directed KMS/Stokes passivity and positive passive completion are closed detours, not
candidate producers.

### E — squarefree Wold Hall transport

**Architecture.** Möbius source is reduced to squarefree depth-zero central Wold sector. Exact
Ramaré reindexing turns prime off-diagonal into ordinary integer-pair incidence retaining both
Möbius signs and Mellin kernel. A source-fixed relation must provide distinct opposite-parity
targets with unit normalized load, interval Hall expansion, moving cutoff exchange, and half-power
Gibbs cost.

**Proved.** Two-or-more-large-prime remainder; positive valuation-depth tail; prime-anchor capacity;
opposite-sign supply; every fixed off-normal Wold tail; finite Wold readers; patch seams as exact
coboundary; finite differential-algebraic Euler germs cannot select free infinite prime-clock orbit;
unconditional Step 1 Hall supply with growing squarefree truncation
(`eventually_fibre_step_one_growing`, `eventually_fibre_step_one_positive`); sharp aggregate fibre
tail with no truncation-level term (`sum_fibre_windowTail_le_budget_sharp`); exact Type-II
cancellation, cell/family energy, raised-threshold loss, dyadic cover, covered-set forms, and covered
Type-II power saving (`MatomakiTeravainenTypeIIAmplitudeCells.lean`); exact ordinary integer-pair incidence
(`RouteERamareIntegerIncidence.lean`). The reciprocal-marker theorem now proves, for every
`9/10 < beta < 1`, both Möbius signs, and every fixed constant, the correct-density supply in
windows

```text
H(Z) = ceil(sqrt(Z) exp((log Z)^beta)).
```

The same window eventually contains at least as many positive-Möbius integers as primes, hence a
prime-to-positive-marker injection at displacement `X^(1/2+o(1))`
(`Sieve/RouteEMarkerHallLaw.lean`).

**Open core.** Construct/extract one exact relation on ordinary squarefree integers directly from
factorization data represented by Ramaré incidence, fixed independently of observed Möbius
imbalance, and prove simultaneously:

1. normalized row load and physical incoming co-degree at most one;
2. relation-specific Hall expansion for every relevant subinterval using distinct opposite-sign
   targets;
3. crossing of co-moving zero/one-large-prime cutoff with charges `-1,+1`;
4. total mixed-difference Gibbs cost `X^(1/2+o(1))`.

Step 1, two-sign half-power cardinal supply, Type-II amplitude cells, and seam estimates are no
longer frontier. Marker cardinality alone does not declare adjacency, prove Hall for the fixed
Ramaré relation, control target co-degree, or cross the moving sector cutoff. Existential complete
bipartite transport is not enough: its defect is original Möbius imbalance. On squarefree hard
support valuation depth is fixed; hard axis is all-prime breadth.

### G — marked Suzuki/Mobius/Gamma boundary orientation

**Architecture.** Source current is retained before scalarization as affine carrier containing
completed prime--polar--Gamma charge and marked odd clock jet. It is transported to
Suzuki/restricted-Weil boundary receiver. Coefficient-faithful affine boundary renormalization now
lands exactly on the continued Ward coefficient and on every actual-head base entry. RH follows
from a source law forcing that transported coefficient to vanish, equivalently from the classified
four-unit orientation.

**Proved.** Source-native affine producer retaining charge and source orders; canonical probe
detects nonzero charge; zero-clock jet vanishes while charge survives; positive-clock packet retains
odd jet; exact scalar readout/ports (`MobiusGammaXiPreScalarAffinePrimePolarGammaProducer.lean`);
first Xi Livsic defect and persistent Suzuki leakage floor (`SuzukiXiFirstDefectJetSource.lean`);
unique Gamma/Euler boundary renormalization; coefficient-faithful Wold domination of boundary
Hessian; universal domination RH-equivalent; scalar cancellation reduces to RH or universal source
erasure; actual multiplicity-faithful Euler--Wold transverse reporter converges to half primitive
budget and eventually lies strictly inside budget, while no linear reporter can both remain
source-budgeted and dominate literal endpoint
(`SourceHorizontalEulerWoldTransverseDefectBudgetReporter.lean`). Exact finite-depth boundary
landing, base-entry comparison, forced complementary correction, and premise-free cofinal transport
are closed (`MobiusGammaXiPreScalarAffineBoundaryRenormalization.lean`); its four-unit positivity is
equivalent to RH.

The squarefree Möbius side now also has a literal infinite signed-channel model: squarefree divisor
probability, unit signed amplitude, vector coisometry and self-adjoint channel projection, exact
coupled-feature norm and cancellation, closed-operator commutation, a Schur contraction on the
closed right half-plane, and exact zeta-ratio multiplier. The safe squarefree correction produces
the reciprocal completed squarefree amplitude and its Ward logarithmic connection before choosing
a Xi divisor. Centered and causal boundary laws converge strongly in `L2`, with causal limit
`exp(-t)`. At criticality its normalized divisor mass escapes every fixed finite coordinate window,
is weakly but not strongly null, and is killed by every fixed compact synthesis. After rescaling
`Y=(sigma-1) log d`, channel law converges to mean-one exponential measure with exact moving-cutoff
quantiles. These theorems close carrier existence, ordinary Schur contractivity, and critical escape,
but explicitly leave coefficient-faithful moving-aperture synthesis into the Xi boundary, concrete
archimedean graph-domain membership, pointed residue continuation, pole-to-divisor covariance, and
four-unit boundary norm open
(`MobiusSignedChannelIncidencePaperCertificate.lean`,
`MobiusSignedSchurComplexMultiplier.lean`,
`MobiusSquarefreeReciprocalProjectivePaperCertificate.lean`,
`MobiusSchurBoundaryPaperCertificate.lean`,
`MobiusChannelCriticalMassEscapePaperCertificate.lean`,
`MobiusCriticalExponentialBoundaryLayerPaperCertificate.lean`).

**Open core.** Derive from literal source, independently of Xi-divisor selection, a nonlinear or
distinct-channel law forcing the already-transported Ward coefficient to vanish or to satisfy the
favorable signed wall order. Construction of a pre-scalar comparison is no longer open. More floor
identities, positive scalar shadows, zero-clock commutators, or another linear budget reporter cannot
close route: Lean separates surviving charge from vanishing jet and classifies the final four-unit
scalar endpoint as RH itself. The new Möbius Schur coisometry supplies one concrete distinct-channel
carrier, but not the missing residue/covariance/four-unit estimate; it is candidate MSC below,
source-isogenous to G rather than a new live route.

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
(`MobiusThetaSourceDaggerMinimalBoundaryLaw.lean`); centered prime-mark Xi fibres and injective
right-half Frobenius orbit; genuine scaled-Xi cross-fibre quotient equivalence and Big-Witt
naturality (`DeningerBigWittScaledXiCrossFiberNaturalTransformation.lean`).

For Burnol's actual source, Lean now proves cosine closure adds no new vectors: reciprocal-seed
landing identifies the cosine branch with another literal co-Poisson source. Hence every right-half
zeta zero annihilates the full closed cosine-invariant co-Poisson source space, not merely the raw
span (`BurnolCoPoissonRawZeroAnnihilator.lean`,
`BurnolCoPoissonCosineClosedZeroAnnihilator.lean`). This closes source annihilation only; aperture
completeness, minimality, higher jets, and physical landing remain separate.

**Open core.** Construct a source-derived singular comparison identifying resolved boundary
flatness with the coefficient-faithful scalar Burnol/Deninger physical landing before divisor
specialization. Operationally, construct a bounded square-summable continuous all-prime same-fibre
restriction whose common kernel is exactly arithmetic boundary subspace, whose target-zero component
is the existing physical landing, and whose reader kills genuine target boundaries while preserving
prime/depth/multiplicity. Cross-fibre naturality and full co-Poisson zero annihilation are closed but
cannot replace this fixed physical comparison.

**Closed detours.** Residue-factored packet cannot classify boundaries unless middle cohomology is
already trivial; cofinite unit-normalized packet floor forbids square summability; generic mapping
cones/Koszul exactness merely relocate or erase `K_n`; finite Rees completion cannot match
exponential sewing singularity; Frobenius is base change inside one fibre, and finite right-half
preperiodicity is impossible. A finite real-descended quaternionic cohomology repair is also blocked:
`C^2=-1` forces even complex multiplicity, while root number `-1` forces odd central order, so an
order-equals-multiplicity real symplectic realization is contradictory. The explicit two-dimensional
`Q8` symplectic generator exists, but does not supply the missing arithmetic/cohomological landing
(`DeningerQuaternionicMultiplicityParity.lean`, `DeningerArtinCentralParityNoGo.lean`).

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
The complete-resolution first normal reader is now identified exactly with the literal prime-two
second-Cartier endpoint, with endpoint energy, conormal coefficient, and support-fibre analytic
multiplicity unchanged.  Across reflection, complete source vectors collapse cofinally while the
endpoint characters remain separated off line; consequently every exact nonlinear extractor has
Lipschitz sensitivity tending to infinity.  The induced pre-divisor order predicate is critical
line placement pointwise, and its universal Xi admission is exactly RH
(`CompleteResolutionSecondCartierNormalOrder.lean`).
The complete resolution now also retains the genuine consecutive products of forward and
reflected prime-peeled adjacent shell transfers as one non-scalar three-coordinate Krein jet before
the normal limit.  The forward product is exactly the half-density power times the
terminal-to-initial peeled residual ratio whenever the traversed residuals are nonzero; no frozen
transfer is externally repeated.  At every fixed orbit depth this finite source jet converges to
the literal second-Cartier endpoint, its positive energy converges to literal radial energy, the
physical conormal coefficient is unchanged, and the
support-fibre sum preserves exact Xi multiplicity.  A single cofinal energy constant for all orbit
depths is equivalent to literal endpoint moderation; on every strict-right Xi copy finite shell
stages exhibit two-stage escape, and universal actual-Xi cofinal budgeting is exactly RH
(`CompleteResolutionReflectedShellSecondCartierDescent.lean`).
Route N's bilateral prime-capacity receiver is now welded to this same invariant: its excess is
exactly the reflected translation-pair excess, and at prime two its excess energy vanishes exactly
when completed radial source work vanishes
(`XiCenteredFlowRouteNSecondCartierRadialWorkBridge.lean`). This identifies N with P's radial-work
receiver; it does not produce the missing source upper budget or reopen N independently.
The regular completed-source class is now closed at its maximal nonlinear level.  Reflected
complete source points collapse cofinally, while their literal endpoint characters stay separated
off line.  Any exact extractor family with even one common continuity modulus on those two points
is therefore impossible off line; conversely such reflection-pair equicontinuous exact extraction
exists on the critical line.  Pointwise regular extraction is equivalent to critical-line
placement, and universal actual-Xi regular extraction is equivalent to RH, without assuming
linearity, positivity, global continuity, or a Lipschitz constant
(`CompleteResolutionReflectionPairEquicontinuityFirewall.lean`).

**Open core.** Derive endpoint moderation/order globally from literal completed source before divisor
selection while retaining coefficient and multiplicity. Universal boundedness and universal finite
circle representability are RH-equivalent. Post-selected compact positive-measure admission is
impossible on every strict-right copy, and the literal static conormal short admits no uniform orbit
budget. Viable producer must therefore be pre-divisor and source-natural; indefinite conservation,
determinant, Krein form, compactness language, or scalar shorting cannot supply it.  Normal-reader
reconstruction alone is also insufficient: its forced sensitivity diverges, and the stronger
reflection-pair theorem excludes every regular nonlinear repair admitting a common continuity
modulus.  Remaining viable shape is singular/projective: an arithmetic order law on the exceptional
normal boundary giving one orbit-depth-independent bound for the genuine consecutive
forward/reflected prime-peeled shell Krein energies.  The shell threshold may depend on orbit depth,
but the energy constant may not.  This estimate must be proved before Xi selection and cannot
replace either reflected leg, conormal coefficient, or multiplicity.  Equivalently it must pair the
singular normal gain with independent arithmetic decay strong enough that
`gain × reflected source displacement → 0` on every Xi zero while deliberately failing every common
reflection-pair continuity modulus.  The formal descent would then give endpoint moderation and RH
without post-selected scalar domination.

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
coherent product-fibre base and unavoidable corrected joint seam are exact. In the separate
Maynard/AFE specialization, direct and dual AFE edges, endpoint-long zeta/log atoms, contour
coefficient absorption, and unconditional endpoint-long Möbius exclusion are closed; remaining
endpoint obstruction is isolated as short Möbius-block cancellation
(`MaynardEndpointMobiusConcentration.lean`).

Formal sources: `XiCTaylorThetaTailCoreCurrentCapstone.lean`,
`XiCTaylorThetaTailProductFiberHermitianCollapse.lean`.

**Open core.** Prove joint upper estimate for
`canonicalThetaTailCoreFiniteArithmeticRemainderCurrent` at same cutoff and depth as prefix selector,
retaining cancellation between top-row and translation pieces. More top-row decay is dead work:
survivor conserves exactly what row loses. Separate absolute-value bounds destroy sign.
For current Maynard specialization, this is pure short Möbius-block cancellation strong enough to
discharge joint current estimate; zeta/log endpoint control is no longer open.

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
events above every mass threshold (`XiShiftedHankelStrictFrontierCurvatureRenewal.lean`). Exact
strict-frontier numerator is continuous/integrable while its Christoffel quotient is not locally
integrable; local integrability at every occupied strict frontier is equivalent to RH
(`XiShiftedStrictFrontierSourceWallIntegrabilityGate.lean`). Non-RH strict frontiers are cofinal but
cannot choose an arbitrarily delayed schedule: they lie inside explicit parabolic degree horizon
(`XiShiftedTerminalFrontierParabolicSynchronization.lean`). Thus cofinal producer admission and
degree--mass synchronization are closed; favorable sign/exclusion is not.

Formal sources: `XiShiftedReciprocalHankelTailCriterion.lean`,
`XiShiftedCanonicalAdmissionAdaptiveArithmeticSourceDegreeConnection.lean`,
`XiShiftedCanonicalAdmissionCofinalScheduleNoGo.lean`,
`SuzukiFirstContactBoundaryRoughness.lean`,
`XiShiftedHardEdgePrimeGammaKelvinTwoChartNoGo.lean`.

**Open core.** Prove uniform cofinal tail positivity/order for explicit source Hankel matrices, or
construct a non-scalar source mechanism that annihilates strict-frontier numerator/excludes its
endogenous admission zero before nonintegrable quotient forms. Generic numerator regularity,
arbitrary schedule delay, scalar counterterms, fixed-degree limits, and positivity along a
self-selected recession schedule are closed or insufficient.

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
energy tending to zero (`XiHorizontalCollisionWardGreenExteriorSourceCarrier.lean`). A second exact
receiver retains prime labels through a multiplicity-faithful Gauss--Hodge current: finite-window
prime summability is equivalent to zero collision charge, global/natural-height summability is
equivalent to RH, and current equals literal Euler derivative of paired Gamma-six suspension
determinant (`XiHorizontalCollisionGaussHodgePrimeCurrent.lean`).

Formal sources: `XiHorizontalCollisionChargeEndpoint.lean`,
`XiReflectionSelfIntersectionCharge.lean`,
`XiHorizontalCollisionTwoPrimeCesaroCarrier.lean`,
`XiHorizontalCollisionPrimeCayleyInformationLoss.lean`,
`XiHorizontalCollisionWardGreenCayleyQuantum.lean`,
`XiHorizontalCollisionWardGreenExteriorSourceCarrier.lean`,
`HedenmalmCoefficientFaithfulExteriorSourceContour.lean`,
`HedenmalmExteriorSourceThetaBoundaryGap.lean`.

**Open core.** Prove from coefficient-faithful prime--Gamma source, before divisor specialization,
either an absolute strict-subquantum bound for source excess/information loss on all late windows or
prime-summability of the literal paired Gamma-six suspension determinant current. Normalized
`o(N(T))` is insufficient: first branch must cross integer quantum two, while second must be an
upstream source estimate rather than already RH-equivalent global summability.

HC is genuinely new architecture because mechanism is source-resolution loss versus quantized
reflection incidence, not positivity of classical explicit formula. Global strict-two law is itself
RH-equivalent; progress must be upstream arithmetic evaluation/cancellation of finite source pencil.

## Corpus-born candidate openings

These are Lean architectures, not literature-shaped suggestions. They are not counted as live until
source handoff is built independently of zero tested.

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

### BW — barrelled prime-depth Wold selection

`PrimeDepthBVWoldBarrelledSourceSelector.lean` proves a Banach--Steinhaus null-orbit principle and
packages exact completed-source certificate: barrelled completion, null cofinal orbit, pointwise
bounded continuous readouts, coefficient preservation, and physical landing. One certificate forces
critical-line placement; a global producer proves RH.

Open theorem: construct global completed barrelled-source certificate from literal prime-depth BV/Wold
source. Current structure names genuine source obligations rather than replacing them by a scalar
summability predicate, but no unconditional global witness exists. BW remains candidate adjacent to
L/P.

### MSC — Möbius signed-channel Schur projection

**Architecture.** Literal squarefree Möbius weights define an infinite signed unit vector. Its
coisometric synthesis projects a vector-valued divisor channel onto one causal source. As criticality
is approached, information moves to divisor scale `log d ~ 1/(sigma-1)`, so physical receiver must
move with that boundary layer rather than be finite or compact. Resulting all-prime Schur multiplier
is a contraction on closed right half-plane; positive safe squarefree correction and archimedean
completion turn it into reciprocal completed squarefree amplitude, whose logarithmic derivative is
projective Ward current. Pointed continuation and four-unit boundary estimate would land in G's RH
endpoint.

**Proved.** Probability normalization, exact critical mass/log-moment rates, coisometry, projection,
coupled-feature norm, arithmetic cancellation, closed-operator commutation, finite and infinite Schur
contractivity, exact zeta-ratio transfer, reciprocal projective Ward connection, unconditional
critical `L2` centered boundary, and causal convergence to `exp(-t)`. Normalized analysis channel
has exact strict gain, loses every fixed finite coordinate while retaining positive total energy,
converges weakly but not strongly to zero, and every fixed compact synthesis kills it. Rescaled
logarithmic divisor clock converges to `Exp(1)`; fixed and moving cutoff masses have exact quantile
limits, and full transport occurs exactly when rescaled cutoff tends to infinity.

**Open core.** Prove for the concrete archimedean feature the graph-domain membership and pointed
residue extension needed by the continuation square, then a nonexpansive pole-to-divisor covariance
or equivalent source estimate reaching the exact four-unit boundary norm through a
coefficient-faithful moving aperture on proved exponential clock scale. These clauses must be
derived before selecting a Xi divisor. A fixed finite/compact receiver is now formally impossible
because it sees asymptotically zero channel mass. Generic moving-node transports and the existing
coisometry do not prove this Xi-boundary transfer: they are compatible with the safe half-plane and
explicitly leave all RH-bearing gates untouched. MSC is a genuinely non-scalar source carrier, but
is source-isogenous to G/CCM and is not yet an independent live route.

Formal sources: `MobiusCoupledFeatureIncidence.lean`,
`MobiusSignedChannelIncidencePaperCertificate.lean`,
`MobiusSignedSchurComplexMultiplier.lean`,
`MobiusSquarefreeReciprocalProjectivePaperCertificate.lean`,
`MobiusCenteredSchurBoundary.lean`, `MobiusCausalSourceLimit.lean`,
`MobiusChannelCriticalMassEscapePaperCertificate.lean`,
`MobiusCriticalBoundaryLayerQuantiles.lean`,
`MobiusCriticalExponentialBoundaryLayerPaperCertificate.lean`.

### SV2 — meromorphic Suzuki characteristic limit

**Architecture.** Entire real-zero characteristic approximants converge locally uniformly only on
a preconnected pole-free open set containing `0` and the whole centered Xi divisor. Closedness of
the real axis then forces every Xi zero to be real and proves RH.

**Proved.** Suzuki's displayed target is exactly

```text
XiC(z) / (XiC(z) + i XiC'(z)).
```

The denominator has an unconditional negative-imaginary zero with nonzero numerator, so target has
a genuine pole. Therefore the literal all-plane compact-open limit of entire real-zero functions is
false. The corrected meromorphic/pole-free convergence wall still implies RH
(`SuzukiV2CharacteristicTarget.lean`). On the literal dense smooth core of Suzuki's energy space,
`i d/dx` is symmetric: its real Fourier multiplier moves between both slots of completed
prime--polar--Gamma Weil form and physical `L2` correction without changing either
(`SuzukiTaSymmetry.lean`). This closes operator symmetry, not self-adjoint exhaustion or
characteristic convergence.

**Open core.** Construct source-defined entire real-zero approximants and prove locally uniform
convergence on one preconnected pole-free domain that contains `0` and every Xi zero. Domain cannot
be chosen after inspecting individual zeros, and finite holomorphic exponential gauges cannot repair
the all-plane wall. Dense-core symmetry alone gives no approximating real-zero characteristics.
SV2 is an exact corrected receiver with no producer, hence candidate rather than live route.

## Formal advances that do not change route count

- `CCMCentralBinomialIntegrality.lean` and `CCMLambertRadicalIntegrality.lean` close the finite
  central-binomial divisibility and algebraic-integrality gate for CCM Lambert radicals. Cyclotomic
  containment and any source-to-RH handoff remain absent.
- `SoninSemilocalDampedCovariancePositivity.lean` proves the Gamma-damped prime-log covariance is
  PSD at every finite matrix and has exact critical half-weight decay. Its strictly positive cross
  terms also prove it cannot equal the additive Euler logarithmic derivative. This is a covariance
  carrier plus no-go, not a new route.
- `ConnesConsaniTraceClassReduction.lean` closes generic propagation from trace-class, finite-rank,
  Hilbert--Schmidt-factorized, or nuclear remainders to every positive modulus power. It does not
  prove a literal source decomposition or spectral sign.
- `MobiusLogarithmicJetLiGenerator.lean` proves the Xi/Li logarithmic generator is unconditionally
  non-holonomic, hence Li coefficients are not accessible through a polynomial-coefficient linear
  ODE or `P`-recursive shortcut. This closes a finite differential route, not RH.
- `RegularizedDivisorHarmonicLimit.lean`, the `StieltjesGammaAffine*` modules, and
  `GammaMeixnerAbelCoronaProbe.lean` construct exact Gamma-affine prime lanes and a singular Abel
  corona detector. They expose source coefficients and boundary singularity but have no Xi landing
  or RH endpoint.
- New generic `HTGeometry` factorization, horizon, channel-rigidity, and moment modules have no
  current `RHTower` import or declaration ending in `RiemannHypothesis`; they are infrastructure,
  not hidden RH routes. New sieve mean-value/Halasz--Montgomery modules similarly have no direct RH
  endpoint beyond their use in source estimates.

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
| N | Response equality, endpoint contractivity, or bounded polar work is RH-equivalent; bilateral capacity excess is now exactly P's reflected translation/radial-work excess. | Shared receiver for L/P/G, not an independent producer. |
| R | Intrinsic producer category empty; every surviving external interface RH-equivalent. | Quartic amplitude, singular cap, and physical landing remain reusable receivers. |
| IW internal SEM Weyl model | Model existence is exactly `2^k` divisibility of actual hole count, depends only on dimension, and universal/cofinal existence is exactly RH. | Exact cyclic clock--shift realization and source-blind divisibility classification; useful certificate, not producer. |
| AP Big-Witt/Scaling-Site power orbit | Big-Witt reporter law holds, but Arakelov square lift has a pole at `1/2`, so no global entire-source pullback exists; actual Scaling-Site covers act differently; fixed-receiver stability/preperiodicity are RH-equivalent. | Source-first Big-Witt Frobenius reporter and valid changed-receiver cross-fibre scaling law. |
| TD/C1 raw positive completion | Four raw reflected critical Stokes atoms already exceed completed zeroth mass; no finite positive supercarrier dominating them can equal completed seam germ. | Any representing carrier must delete/reweight raw atoms or introduce signed negative correction before final positivity. |
| AF class-law scale-orbit | Convergent abelian class-law certificate exists iff centered rate is zero; global certificates on all Xi copies exist iff RH. | Terminal rigidity/selection theorem; successor must change interface to singular/infinite-action or genuinely global aggregate law. |
| Suzuki v2 entire characteristic wall | Displayed target has an unavoidable pole, so no all-plane locally uniform limit of entire real-zero characteristics exists; finite holomorphic exponential gauges do not remove it. | Pole-free meromorphic convergence wall SV2 still implies RH. |
| Deninger finite quaternionic real descent | Quaternionic anti-linear square `-1` forces even complex multiplicity, but root number `-1` forces odd central order; order-equals-multiplicity real symplectic realization is impossible. | Explicit `Q8` symplectic carrier; any successor must alter real finite descent or the physical comparison. |
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

### IW, AP, TD/C1, and AF exact closures

`SEMDyadicWeylExistenceClassification.lean` proves internal SEM Weyl-model existence iff dyadic
hole-count divisibility, source-blindness at fixed dimension, levelwise equivalence with the RH
ladder, and all-level/cofinal equivalence with RH. IW therefore cannot independently generate the
divisibility it was meant to explain. Its positive survivor is the exact internal cyclic
clock--shift representation of already-present divisibility.

`BigWittArakelovSourceEndomorphismTerminal.lean` proves the source-first Big-Witt Frobenius reporter,
then closes every fixed completed-Xi handoff in this architecture: global entire pullback is
impossible, actual Scaling-Site cover is not the power lift, Euler Adams gives dilation rather than
ramification, half-scaling changes receiver, and remaining fixed-receiver conditions are
RH-equivalent. AP is exhausted within Big-Witt/Scaling-Site/completed-Xi architecture.

`GammaSewnMobiusApertureStokesPositiveCompletionNoGo.lean` closes TD/C1's canonical
raw-positive/passive handoff and proves exact non-domination survivor. It does not close corrected
signed/indefinite C1 class-space architecture. `SourceHorizontalAdaptiveFisherGlobalClassLawProducer.lean`
constructs neutral source certificate, proves certificate existence exactly at centered rate zero,
and proves global all-Xi-copy producer equivalent to RH. AF is therefore closed as independent
copywise convergent class-law mechanism, not promoted to live route.

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
- internal finite-dimensional Weyl-model existence as source mechanism: it only restates dimension
  divisibility and is source-blind;
- global entire-source pullback by pole-bearing Arakelov square lift, or replacement by an actual
  Scaling-Site cover that implements a different action;
- positive Hermitian completion preserving or dominating an overmassive canonical raw carrier;
- copywise convergent abelian class-law certificates away from neutral rate;
- holonomic/P-recursive Li-generator closure: infinitely many Xi-zero preimages force poles of every
  iterated logarithmic jet, excluding every polynomial-coefficient linear ODE;
- fixed finite-coordinate or compact synthesis of critical Möbius signed channel: all channel mass
  escapes to the exponential moving divisor boundary layer;
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

### Positive completion can fail before spectral geometry

TD/C1 supplies a sharp mass firewall: reflection can repair parity while canonical raw carrier
already overspends completed zeroth mass. Adding positive sectors only worsens defect. Therefore
"find a larger positive space" is not a neutral move; successors must alter source atoms or
introduce signed cancellation before any final positive quotient. D2's directed-passivity no-go
shows same issue at a fixed centered response point.

### Quantized obstructions beat normalized asymptotics

HC exploits indivisible collision quantum two and squared reflection order. Normalized `o(N)` can
coexist with finitely many bad atoms, so source estimate must cross absolute quantum threshold. IW
shows the limitation of this idea: an abstract internal Weyl model can merely encode desired integer
divisibility and contribute no independent arithmetic production.

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

HC, SC, PPM, IRK, HJ, and BW share architecture:

```text
literal source operation
  -> internal orbit / monodromy / incidence / information loss
  -> discrete rigidity or quantum threshold
  -> exclusion of off-line divisor
```

Common danger is zero-indexed vacuity. Valid proof must build global source operation before choosing
divisor. HC is furthest because coefficient-faithful finite source carrier and exact quantized limit
already exist; only source estimate remains. IW and AP were hostile tests of this family and are now
terminal: IW's operation is exactly the desired divisibility, while AP's genuine source reporter
cannot act on fixed completed-Xi receiver.

MSC and SV2 form a second non-classical family: infinite paired/signed source carrier followed by a
singular or meromorphic boundary landing. MSC has the carrier but lacks pointed divisor covariance;
SV2 has the corrected meromorphic endpoint but lacks source approximants. Neither can be reduced to
a finite positive object or a single scalar response without hitting a proved firewall.

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
6. **Source-native internal dynamics:** projective module, corrected Stokes category, or monodromy
   on actual arithmetic carrier before divisor selection (SC, PPM, IRK, OPUC, HJ, BW, MSC, SV2).
   Abstract Weyl existence, Arakelov power pullback, entire Suzuki convergence, and finite real
   quaternionic descent are classified terminal in their stated architectures.

Fundamental remaining obstruction is not another equivalent criterion. Corpus already has many. It
is:

> derive favorable global order or discrete rigidity from literal completed source while retaining
> orientation and mixed incidence erased by scalarization, finite truncation, and post-divisor
> fitting.

## Highest-value questions exposed by Lean

1. Can third-grade Guinand--Weil cumulative source have linearly bounded primitive without zero-free
   input?
2. Can positive-frequency prime--arch trace be controlled by a reflected signed/non-dominating
   source law after canonical directed passivity and raw-positive completion have failed?
3. What exact squarefree relation realizes Ramaré incidence with unit all-interval Hall load and
   co-moving flux?
4. What independent nonlinear/distinct-channel source law forces already-transported Ward
   coefficient to vanish or acquire favorable wall order?
5. Can all-prime Green restriction be square-summable with common kernel exactly arithmetic
   boundary and target existing physical landing?
6. Is completed CCM symbol nonnegative on every canonical actual-head density?
7. What pre-divisor completed-source law forces moderation of the literal second-Cartier endpoint,
   despite the proved post-selected finite-measure and scalar-short firewalls?
8. Why is explicit positive-frequency reduced Cauchy kernel PSD on every exterior finite packet?
9. What joint estimate controls T depth-invariant top-row/translation remainder without splitting
   cancellation?
10. What source mechanism excludes exact nonintegrable strict-frontier Christoffel quotient or
    proves shifted reciprocal Hankel tail positivity inside proved parabolic horizon?
11. Can two-prime source excess be bounded absolutely below collision quantum two, or can literal
    paired Gamma-six determinant current be proved prime-summable upstream?
12. Can source globalize Coxeter, prime-power collision, irrational-rotation `K_0`, paraorthogonal
    phase, or Hurwitz projective reflection before divisor selection without collapsing to another
    RH-equivalent certificate?
13. Can the concrete Möbius signed-channel feature cross its pointed residue/graph-domain wall and
    satisfy a source-derived four-unit covariance bound?
14. Can source-defined real-zero characteristics converge on one predeclared pole-free domain
    containing the full Xi divisor, as required by corrected Suzuki v2?

Until one is answered, endpoint reformulations, finite real-zero models, seed asymptotics, diagonal
moment inequalities, or scalar transport identities do not move formal RH frontier.
