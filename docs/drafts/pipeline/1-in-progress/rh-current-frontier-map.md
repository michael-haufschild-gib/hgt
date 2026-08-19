# Current Formal Frontier Toward Proving or Disproving the Riemann Hypothesis

## Scope, evidence, and status language

This document states where the `HTGeometry`, `HilbertMetric`, and `RHTower` Lean corpus stands now.
It maps architectures, theorem chains, open cores, and terminal mechanisms. It is not a chronology,
work log, literature survey, or inventory of every RH-equivalent proposition.

**Formal-corpus cutoff:** 19 August 2026, commit
`27258d06f5a7b90a5f3f4d8fc5a45902d4a4db01`, plus declaration-index review of current Lean
working-tree changes. Scientific status below comes only from Lean declarations, dependencies,
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

Formal corpus currently supports thirteen live architectures:
`CCM-FU, C1, D2, E, G, L, O, P, Q, T, U, HC`, and newly promoted
**SV2 (Suzuki spherical characteristic convergence)**. Ten corpus-born receiver/source-mechanism
candidates remain: `SC, PPM, IRK, OPUC, HJ, BW, MSC, PCS, SEC, BPC`. Routes R, IW, and AP are terminal as independent
producers. Latest additions close important intermediate premises, but do not close any route's
final open producer and prove neither RH nor its negation.

| Architecture | Proved chain | First open core |
|---|---|---|
| CCM-FU | completed Guinand--Weil third-grade source -> exact signed FU reporter -> Xi-screw Green -> second-Abel continuation -> RH | Linear growth of one Cesaro primitive of literal third-grade prime-minus-polar cumulative source; exact signed-symbol cancellation and lower-wall escape are closed. |
| C1 | corrected theta/prime--Gamma source -> Weil/Connes form or real spectral realization -> RH | Construct a source-derived non-dominating or signed correction before final positivity; raw positive/passive Stokes completion is impossible. |
| D2 | continued prime--arch trace -> one-sided anti-Herglotz/finite ceiling -> RH | Source control of sole positive-frequency tail by a reflected signed/non-dominating law; canonical directed passive limits are impossible. |
| E | squarefree Wold source -> two-sign half-power marker supply -> exact integer-pair incidence -> unit-load Hall transport with moving flux -> RH | Build one Ramaré-supported relation joining proved marker supply to relation-specific subinterval Hall, unit load, co-moving flux, and Gibbs cost. |
| G | Suzuki/Mobius/Gamma source -> marked pre-scalar or signed-channel carrier -> exact Ward landing -> wall orientation -> RH | Independent source law forcing the already-transported Ward coefficient to vanish or have the required signed order; Schur coisometry and causal limit do not supply four-unit orientation. |
| L | completed Green/BV/Big-Witt/co-Poisson source -> bounded completed jet system -> singular Calderon--Witt comparison -> physical reader -> RH | Bounded higher-jet/closure completeness, then source-derived singular comparison identifying resolved boundary flatness with existing coefficient-faithful Burnol/Deninger physical landing before divisor specialization. |
| O | exact restricted-Weil operator -> canonical true-ground heads -> coherent signed producer -> nonnegative floor -> RH | Sign of cancellation-preserving coherent finite-head producer, equivalently eventual reverse-prime control on canonical actual heads. |
| P | source-horizontal second-Cartier orbit -> Route-N capacity/radial-work bridge -> radial Krein energy -> endpoint moderation -> RH | Produce endpoint order globally before divisor selection; regular reflection-pair extraction, finite circle measure, and literal scalar short are formally ruled out. |
| Q | continued Hurwitz/Cauchy source -> exterior positive-frequency paired kernel -> orientation zero -> RH | Passivity/PSD of explicit finite reduced prime--Gamma matrices on exterior positive poles. |
| T | finite Xi-Taylor/theta-tail source -> exact reflection bridge -> raw core-current bound -> RH | Joint upper estimate for combined top-row plus surviving finite-translation remainder; in the endpoint specialization, pure short Möbius-block cancellation. |
| U | shifted hard-edge source -> cofinal shifted Hankel tail or first-contact exclusion -> RH | Non-scalar source mechanism excluding the exact nonintegrable strict-frontier quotient, or uniform cofinal tail order. |
| HC | two-prime/Cayley/Gauss--Hodge source -> quantized horizontal collision charge -> strict sub-two or prime-summability law -> RH | Absolute subquantum estimate or source-first prime-summability for the literal paired Gamma-six determinant current. |
| SV2 | literal Suzuki energy space -> paired self-adjoint characteristics -> bounded projective normal family -> global Xi projective target -> corrected two-chart spherical limit -> RH | Identify the canonical cofinal subsequential limit with the divisor-faithful global target, then extend convergence over the full finite chart and reciprocal pole chart. |

Latest corpus changes promote SV2 because its actual finite-aperture characteristic, self-adjoint
spectrum, entire Fourier realization, and real-zero law are now formal. They add PCS, SEC, and BPC
as genuinely infinite nonphysical candidates. They narrow `C1, E, G, L, O, HC` without closing their first
producers. The first open producer of `CCM-FU, D2, P, Q, T, U` is unchanged. In particular, the
half-unit Mertens tower is exactly RH rather than a producer; high-height reciprocal-square Xi tails
are closed but do not orient O's true ground; new joint-omega sieve budgets do not define E's fixed
relation or prove T's short Möbius block estimate.

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
one-prime remainder or orient the resulting spectrum. The generic Vivanti--Pringsheim theorem is
now formal: a nonnegative-coefficient power series with finite positive radius cannot continue
through its positive boundary point (`VivantiPringsheim.lean`). No Lean theorem yet instantiates
its hypotheses on the completed Bernstein/Xi source or turns that generic singularity into the
required corrected spectral orientation.

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

The joint-omega sieve layer is also substantially more complete. Lean now has exact two-range
factorization of the joint weighted polynomial, coefficient-variance and Gallagher spectral
reductions, the omega-ladder budget, and the Section-4 disc/annulus, exceptional-cofactor, Q-side,
and master assemblies. Their capstones correctly retain the normalized joint-budget, short-block,
annular saving, cofactor-mean, and defect estimates as hypotheses
(`Sieve/JointOmegaFactorisation.lean`, `Sieve/JointOmegaSpectral.lean`,
`Sieve/JointOmegaBudgetFromLadder.lean`, `Sieve/Section4Master.lean`). Thus the analytic accounting
needed after a relation is supplied is formal. The latest divisor repair replaces the fatal
crude `#Q` ladder-defect coefficient by `(log B0/log RQ+1)^2`
(`Sieve/JointLadderDefectDivisor.lean`). `Sieve/JointSchedule.lean` fixes the short/long prime
ranges, common ladder ratio, Gallagher cut, expiry height, and eventual range disjointness.
`Sieve/JointSpectralDivisor.lean` carries the divisor bound through the joint spectral/fibre bridge,
replacing its fatal cardinality-squared rounding loss by a polylogarithmic bound.
`Sieve/JointNonSpectral.lean` also discharges the normalized Turan--Kubilius variance row of the
joint budget. Equal-weight short-block control, vanishing slope row, exact disc and annulus scale
cancellation, and the nonexceptional block estimate are now formal
(`Sieve/JointEqualWeights.lean`, `Sieve/JointSlopeRow.lean`, `Sieve/Section4DiscPiece.lean`,
`Sieve/Section4AnnPiece.lean`, `Sieve/Section4NonExcPiece.lean`). Remaining budget rows still retain
explicit analytic hypotheses. `Sieve/FreeEtaLadder.lean` also removes fixed-step bookkeeping by
proving exact nonovershoot, one-step top reach, and a harmonic-mass lower bound for a free-ratio
geometric ladder. Working-tree `Sieve/JointLongRange.lean` installs that free ratio in the actual
long designated prime range, proving eventual base admissibility, target reach, and ladder coverage.
None of these theorems
chooses adjacency or supplies the co-moving parity flux.

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
`MobiusSignedSchurTransferPaper.lean`,
`MobiusSchurBoundaryPaperCertificate.lean`,
`MobiusChannelCriticalMassEscapePaperCertificate.lean`,
`MobiusCriticalExponentialBoundaryLayerPaperCertificate.lean`).

At the causal boundary, Lean now identifies the critical Mertens transform exactly with
`1/(w*zeta(1+w))`. One weighted Mertens moment of exponent `alpha` excludes zeta zeros in
`Re(s)>1-alpha`, while the complete tower `0<=alpha<1/2` is equivalent to RH
(`MobiusCriticalLaplaceIdentity.lean`, `MobiusWeightedMomentZeroFree.lean`,
`MobiusHalfUnitMomentTower.lean`, `MobiusRHDecayMoment.lean`). The positive-shift prelimit supplies
an exact centered causal transform and turns one weighted prelimit moment into one zero-free
half-plane (`MobiusPrelimitLaplaceIdentity.lean`), but its unconditional
domain has only widths `alpha<2*omega`. Reaching the critical line needs
`alpha<1/2+2*omega`, leaving an exact invariant deficit `1/2`
(`MobiusPrelimitSafeWidth.lean`). Prime-aperture analysis is equally sharp:
full critical mass is retained exactly when the scaled cutoff tends to infinity, and then
`omega*log(aperture)` diverges. A fixed compact receiver or scalar differential family of order
`exp(O(1/omega))` therefore cannot carry the whole channel
(`MobiusPrimeApertureQuantile.lean`, `MobiusPrimeApertureDifferentialOrder.lean`).

**Open core.** Derive from literal source, independently of Xi-divisor selection, a nonlinear or
distinct-channel law forcing the already-transported Ward coefficient to vanish or to satisfy the
favorable signed wall order. Construction of a pre-scalar comparison is no longer open. More floor
identities, positive scalar shadows, zero-clock commutators, another linear budget reporter, or the
complete half-unit moment tower cannot close route: Lean separates surviving charge from vanishing
jet and classifies both the final four-unit scalar endpoint and complete moment tower as RH itself.
The Möbius Schur coisometry supplies one concrete distinct-channel carrier, but not the missing
residue/covariance/four-unit estimate; it is candidate MSC below, source-isogenous to G rather than
a new live route.

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

For Burnol's actual exponential-window source, every positive logarithmic subwindow now realizes
the exact zeta multiplicity: every completed jet below the multiplicity vanishes and the leading
jet is nonzero (`BurnolCoPoissonCompletedZeroJets.lean`). For every literal compact co-Poisson seed,
the Mellin factor is holomorphic on the relevant strip and all lower completed jets vanish at an
actual right-half Xi divisor. Cosine closure adds no new lower-jet directions, and every finite
algebraic source span lies in the same lower-jet annihilator
(`BurnolCoPoissonGeneralSeedCompletedZeroJets.lean`,
`BurnolCoPoissonCosineClosedLowerJetSystem.lean`). These are coefficient-faithful source laws, not
only raw zero annihilation. On the closed cosine-stable source space, zeroth-jet orthogonality is
now equivalent to `zeta(w)=0`; one literal symmetric subwindow gives the reverse detection
(`BurnolCoPoissonCosineClosedZeroJetDetection.lean`). They do not prove
boundedness of the higher-jet evaluator on the completed Hilbert source, higher-jet
closure/aperture-complement completeness, or the physical descent.

**Open core.** Two completion gates remain in series. First, prove boundedness of the relevant
higher-jet evaluator and the higher-jet closure/aperture-complement theorem needed to pass the algebraic
lower-jet system to the completed source space. Second, construct the source-derived singular
comparison identifying resolved boundary flatness with the coefficient-faithful scalar
Burnol/Deninger physical landing before divisor specialization. Operationally, the latter is a
bounded square-summable continuous all-prime same-fibre restriction whose common kernel is exactly
the arithmetic boundary subspace, whose target-zero component is the existing physical landing,
and whose reader kills genuine target boundaries while preserving prime/depth/multiplicity.
Strict resolved provenance, cross-fibre naturality, and exact lower-jet annihilation cannot replace
these two topological/physical comparison gates.

**Closed detours.** Residue-factored packet cannot classify boundaries unless middle cohomology is
already trivial; cofinite unit-normalized packet floor forbids square summability; generic mapping
cones/Koszul exactness merely relocate or erase `K_n`; finite Rees completion cannot match
exponential sewing singularity; Frobenius is base change inside one fibre, and finite right-half
preperiodicity is impossible. A finite real-descended quaternionic cohomology repair is also blocked:
`C^2=-1` forces even complex multiplicity, while root number `-1` forces odd central order, so an
order-equals-multiplicity real symplectic realization is contradictory. The explicit two-dimensional
`Q8` symplectic generator exists. The literal first and second quadratic fields now have proved
irreducibility and degrees, the degree-eight radical has an exact polynomial certificate, and the
candidate conjugation lifts anti-commute on the top radical. These algebraic closures still do not
supply the missing arithmetic root-number identification, normality/Galois-group theorem, or
cohomological landing
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
exact; pointwise completed-symbol positivity suffices. High-height divisor escape for centered
reciprocal-square tests is no longer open: `XiCentralTailLaw.lean` proves divisor mass
`O(R log R)` and tail `O(G^(1-2r-4j) log G)`, with four additional inverse powers per hard-edge
zero. This controls the remote tail, not the sign of the true-ground finite/low-height block.

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
mixed incidence dominates separately positive diagonal energies. On real regular points the
continued prime--arch source is real, and the reduced paired source kernel is exactly the positive
diagonal congruence of the confluent Loewner matrix of the square-descended Xi seam-log germ
(`XiPositivePairedRealLoewnerSeam.lean`). Thus positivity, inertia, rank, and nullity are the same
Loewner problem; this identifies the boundary geometry but does not prove its sign.

Formal sources: `XiHurwitzOrientationSeparatedSourceReconstruction.lean`,
`XiHurwitzOrientationExteriorCauchyClosure.lean`,
`XiHurwitzOrientationPositivePairedSource.lean`,
`XiPositivePairedRealLoewnerSeam.lean`,
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

The actual Xi divisor also satisfies an unconditional finite charging law. If `N(T)` counts strip
zeros, `N0,s(T)` simple critical zeros, and `H1(T)` horizontal fibres of total multiplicity one,
then

```text
2 N0,s(T) <= 2 H1(T) + (N(T)-N0(T)).
```

Every spoiled simple critical ordinate consumes at least one reflected off-line pair
(`HorizontalSingletonFiberCharging.lean`). This sharpens the finite
incidence census but does not upper-bound the off-line term and therefore does not change HC's
producer.

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

### SV2 — Suzuki energy-space spherical characteristic convergence

**Architecture.** The literal Suzuki energy space at aperture `a` carries a symmetric minimal
derivative with one-dimensional deficiency spaces. Boundary phases select self-adjoint extensions,
and their exact entire Fourier characteristics have only real zeros. The fixed phase pair `0,pi`
forms a pole-compatible projective characteristic. A canonical cofinal aperture family is compact
in an upper-half-plane holomorphic chart. Identifying its limit with the divisor-faithful global Xi
projective pair and extending to the reciprocal chart would satisfy the spherical wall; closedness
of the real axis would then force every centered Xi zero real.

**Proved.** Lean now constructs the minimal derivative, normalized deficiency vectors, every
boundary-phase self-adjoint extension, and canonical spectral vector. The complex eigenspace is
one-dimensional. The finite characteristic is exactly the Green boundary pairing, and

```text
suzukiTaCharacteristic(a,theta,z)=0
  iff z is an eigenvalue of the selected self-adjoint extension.
```

Consequently every finite-aperture characteristic zero is real. The energy-space Riesz moment is
identified with the literal compactly supported physical Fourier integral, so the characteristic
is entire (`SuzukiTaCharacteristicRealization.lean`, `SuzukiTaSpectralEigenspace.lean`,
`SuzukiTaCharacteristicZeros.lean`, `SuzukiTaCharacteristicEntire.lean`). The target remains

```text
XiC(z)/(XiC(z)+i XiC'(z)).
```

Its genuine poles make all-plane ordinary compact-open convergence impossible. Lean instead
formalizes the correct spherical atlas: ordinary convergence on a preconnected finite chart
containing the whole Xi divisor, reciprocal convergence on an infinity chart, and eventual
zero-freeness of the approximants on compacta in that infinity chart. This wall implies RH
(`SuzukiV2SphericalConvergence.lean`). `SuzukiTaV2ProjectiveCharacteristic.lean` now closes the
previous family-selection and local compactness gaps. It builds the literal two-angle quotient,
proves it meromorphic globally, holomorphic and aperture-uniformly bounded in the upper half-plane,
chooses the canonical apertures `a_n=n+1`, and obtains a cofinal subsequence converging uniformly on
a fixed compact upper-half-plane ball to a holomorphic limit. It also proves the cross-multiplied,
division-free identity between the global Xi Livsic pair and the v2 projective target.
`SuzukiTaCovarianceSource.lean` further identifies each abstract Riesz deficiency vector with the
literal completed restricted-Weil covariance applied to `exp(+-x)`, places that density in the
actual finite Friedrichs-operator domain, and proves its exact shifted resolvent equation. Thus the
finite source vector is no longer a choice or abstract representative.

**Open core.** Prove that the canonical normal-family limit is the global Xi projective target,
not an arbitrary bounded holomorphic subsequential limit, and propagate that identification over a
finite chart containing every Xi zero. Then establish reciprocal-chart convergence and eventual
compact zero-freeness at every target pole. Aperture schedule, phase pair, projective normalization,
upper-half-plane denominator control, and local subsequential compactness are closed. The missing
step is coefficient-faithful global limit identification plus the pole chart, not construction of
real-zero approximants. The old all-plane entire wall stays terminal and cannot be repaired by
finite holomorphic exponential gauges.

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
limits, and full transport occurs exactly when rescaled cutoff tends to infinity. The exact causal
Laplace transform is `1/(w*zeta(1+w))`; the positive-shift domain remains short of the RH-bearing
weighted width by exactly `1/2`; and full prime-aperture retention forces
`omega*log(aperture)->infinity`.

**Open core.** Prove for the concrete archimedean feature the graph-domain membership and pointed
residue extension needed by the continuation square, then a nonexpansive pole-to-divisor covariance
or equivalent source estimate reaching the exact four-unit boundary norm through a
coefficient-faithful moving aperture beyond every bounded scalar differential-order scale. These clauses must be
derived before selecting a Xi divisor. A fixed finite/compact receiver is now formally impossible
because it sees asymptotically zero channel mass. Generic moving-node transports and the existing
coisometry do not prove this Xi-boundary transfer: they are compatible with the safe half-plane and
explicitly leave all RH-bearing gates untouched. MSC is a genuinely non-scalar source carrier, but
is source-isogenous to G/CCM and is not yet an independent live route.

Formal sources: `MobiusCoupledFeatureIncidence.lean`,
`MobiusSignedChannelIncidencePaperCertificate.lean`,
`MobiusSignedSchurComplexMultiplier.lean`,
`MobiusSquarefreeReciprocalProjectivePaperCertificate.lean`,
`MobiusSignedSchurTransferPaper.lean`, `MobiusCenteredSchurBoundary.lean`,
`MobiusWeightedMertensVector.lean`, `MobiusCenteredMertensLimit.lean`,
`MobiusCausalSourceLimit.lean`,
`MobiusChannelCriticalMassEscapePaperCertificate.lean`,
`MobiusCriticalBoundaryLayerQuantiles.lean`,
`MobiusCriticalExponentialBoundaryLayerPaperCertificate.lean`.

### PCS — all-prime co-shift boundary complex

**Architecture.** On the genuinely infinite arithmetic Hilbert space `H=l2(N>=1)`, every prime
acts by the multiplicative co-shift `V_p*`. The row

```text
T_(p,s) = V_p* - p^(-s)
```

has a common arithmetic eigenline only to the right of the critical line. A regularized additive
boundary value turns that line into a two-term complex whose homology is born precisely on the
zeta divisor. A completed secondary class capable of distinguishing that homology would give a new
nonphysical, all-prime route to exclude off-line zeros.

**Proved.** Coordinate recursion and unique factorization give the complete common-eigenspace law:
for `Re(s)>1/2` it is exactly `C*(n^(-s))`, while for `Re(s)<=1/2` it is zero
(`PrimeCoShiftModel.lean`). The all-prime row is a closed densely defined operator; its graph domain
is exactly the omega-weighted energy space (`PrimeCoShiftRowGraph.lean`). Explicit one-prime kernel
projections commute, and the row has a uniform spectral gap on the orthogonal complement of the
common eigenline (`PrimeCoShiftKernelProjection.lean`, `PrimeCoShiftSpectralGap.lean`). After
subtracting the Jonquiere singular branch, boundary evaluation is exactly `x_1*zeta(s)`. Hence the
reduced complex is acyclic off the divisor and has one-dimensional kernel and cokernel on it
(`PrimeCoShiftBoundaryComplex.lean`). Its Fredholm index is always zero: kernel and cokernel appear
together.

**Open core.** Construct from the completed all-prime/reflection structure, before selecting a zeta
zero, a secondary orientation, pairing, torsion, or determinant-line class which is not erased by
the zero ordinary index and whose unconditional law forces this boundary complex acyclic throughout
`1/2<Re(s)<1`. No such secondary class or source law is yet in Lean. If supplied, the existing
right-half zero-free endpoint `rh_iff_xi_ne_zero_right` gives RH after the standard Xi/zeta zero
transfer. PCS is therefore a genuine new infinite nonphysical candidate, not a live route and not
a reformulation of classical finite spectral approximation.

### SEC — prime-seam one-ended coherence

**Architecture.** The canonical FE--Schwarz seam charge is a complex label on the infinite prime
set. Put one fixed, source-predeclared preconnected one-ended graph on those primes. If only
finitely many graph edges see a change of seam value, end reconstruction makes the seam eventually
constant; its proved cofinal decay then kills that constant, and one zero seam forces the divisor
onto the critical line. This is an infinite graph-coherence route, not a finite spectral or positive
measure route.

**Proved.** Canonical prime seams decay to zero cofinally throughout the open critical strip, and a
single prime seam vanishes exactly when `Re(rho)=1/2` (`XiPrimeSeamCoherenceCollapse.lean`,
`HeatAperturePrimeSeamReflection.lean`). Arbitrary-label one-ended reconstruction now proves finite
edge variation implies eventual constancy without any finite-value hypothesis
(`ArbitraryLabelEndReconstruction.lean`). Combining them,
`XiPrimeSeamOneEndedCollapse.lean` proves that finite seam variation on any infinite preconnected
finite-boundary one-ended prime graph forces `Re(rho)=1/2`. On the increasing prime ray, eventual
equality of consecutive seam values already suffices. This is strictly weaker in form than demanding
all prime seams equal, whose global Xi version is already exactly RH.

**Open core.** Construct one graph from completed arithmetic source data, independently of Xi
divisors, prove it is preconnected and finite-boundary one-ended, and prove the canonical seam has
finite edge variation on that same graph for every Xi zero copy. The prime-ray specialization asks
for eventual consecutive equality and is a sharp endpoint, not yet a producer. No Lean theorem
derives either variation law from prime--Gamma coefficients. SEC is therefore a genuine new
infinite nonphysical candidate, but not live; arbitrary choice of a graph after inspecting a seam
would be circular.

### BPC — Bernstein--Pringsheim collar

**Architecture.** Form the positive Abel susceptibility whose coefficients are the exact
Loschmidt purities of the completed prime--Gamma Bernstein source. Its complex convergence radius
equals its real Abel radius. If the source germ admits one coherent holomorphic continuation along
the positive collar from inside the unconditional chamber to every real point below one,
Vivanti--Pringsheim forbids any earlier positive boundary singularity. The critical radius must
therefore be one, which is RH. This is an infinite analytic-continuation architecture, not a finite
moment or positive-matrix argument.

**Proved.** The coefficients are nonnegative and source-defined; the susceptibility has a unique
critical radius `R` with

```text
250000/251001 < R <= 1,     RH iff R = 1.
```

Inside `|z|<R` its complex series is analytic, outside `R` it is not summable, and the positive
boundary point `R` is a genuine noncontinuable singularity. `SegmentAnalyticContinuation.lean`
propagates germ equality along a real segment. `PrimeArchBernsteinPringsheimCollar.lean` combines
these facts and proves `riemannHypothesis_of_collarContinuation`; the endpoint `1` is not assumed
to belong to the continuation domain. The prior prime--arch Mobius pullback identifies the central
moment germ with the continued prime--Gamma source near its starting point.

**Open core.** Construct, from the continued prime--Gamma/Mobius source expression and without a
zero-free or radius premise, one analytic function on an open set containing the entire positive
collar `[z0,1)` and prove local equality with the susceptibility germ near `z0`. No Lean theorem
continues the source expression through that collar. Boundedness or summability of the purity on
all `t<1` is already RH-equivalent, so it cannot be used to manufacture the continuation. BPC is a
new candidate, not live: its singularity detector and RH endpoint are complete, but the arithmetic
continuation producer is absent.

## Formal advances that do not change route count

- `CCMCentralBinomialIntegrality.lean`, `CCMLambertRadicalIntegrality.lean`, and
  `CCMLambertCoefficientIntegrality.lean` close central-binomial divisibility, radical
  integrality, and dyadic algebraic integrality of every literal finite equation-(53) Lambert
  coefficient. `CCMCyclotomicLambertIntegrality.lean` now closes the former cyclotomic gap:
  every complex choice of the literal natural radicand square roots lies in the concrete
  cyclotomic integer ring, and every formal Lambert coefficient lies in its dyadic localization
  `Z^cyc[1/2]`. This is coefficientwise formal-series arithmetic; analytic convergence, a
  completed-source realization, and any source-to-RH handoff remain absent.
- `SoninSemilocalDampedCovariancePositivity.lean` proves the Gamma-damped prime-log covariance is
  PSD at every finite matrix and has exact critical half-weight decay. Its strictly positive cross
  terms also prove it cannot equal the additive Euler logarithmic derivative. This is a covariance
  carrier plus no-go, not a new route.
- `ConnesConsaniTraceClassReduction.lean` closes generic propagation from trace-class, finite-rank,
  Hilbert--Schmidt-factorized, or nuclear remainders to every positive modulus power. It does not
  prove a literal source decomposition or spectral sign.
- `MobiusLogarithmicJetLiGenerator.lean` proves the Xi/Li logarithmic generator is non-holonomic.
  `MobiusLiGeneratorHypertranscendence.lean` now proves the stronger statement: after the
  anharmonic chart it satisfies no algebraic differential equation over `C(z)`. Li coefficients
  are therefore inaccessible through any finite differential-algebraic closure, not only a
  polynomial-coefficient ODE or `P`-recursive shortcut. This is a firewall, not RH.
- `RegularizedDivisorHarmonicLimit.lean`, the `StieltjesGammaAffine*` modules, and
  `GammaMeixnerAbelCoronaProbe.lean` construct exact Gamma-affine prime lanes and a singular Abel
  corona detector. They expose source coefficients and boundary singularity but have no Xi landing
  or RH endpoint.
- The new archimedean Gamma-field chain proves a monomial valuation boundary law, finite Gamma
  product hypertranscendence, and absence of any nontrivial differential relation for zeta jets with
  coefficients in the prime-log shifted Gamma field
  (`ArchimedeanGammaFieldBoundaryLaw.lean`,
  `ArchimedeanGammaProductHypertranscendence.lean`, `ZetaPrimeLogGammaField.lean`). This is a strong
  firewall against finite differential-algebraic prime--Gamma closure. It narrows finite-germ
  variants adjacent to E/G/AF. The multiple-elliptic-Gamma chain strengthens the same rigidity:
  with at least three surviving rationally independent structural periods, a translation defect is
  differentially algebraic exactly for integer shifts
  (`MultipleEllipticGammaGenericSpectrum.lean`).
  `MultipleGammaCyclotomicDeletionMultiplicity.lean` further computes the exact
  differential-algebraic/hypertranscendental multiplicities after cyclotomic period deletion.
  None of these results orients a completed source or yields an RH endpoint.
- `ArchimedeanGammaModule.lean` adds the source-side operator interpretation: the Gamma place is a
  rank-one shift--differential module with multiplier `s/(2*pi)` and digamma connection; tensoring
  with zeta gives the completed Euler-half-plane module and functional equation. Unlike finite
  prime shifts, its connection is nonconstant. `BinetLogGamma.lean` and
  `LerchHurwitzDerivative.lean` supply the matching determinant/derivative identities. Any L/G/C1
  comparison must preserve this prime--archimedean connection mismatch; these modules do not
  supply the comparison.
- The critical-horizon Schur chain now supplies integral sheet lifts, the unique ramified prime,
  corank-one singular-sheet conormal geometry, exact sheet degree, and one common reduced-fibre
  point supporting every collision. Full symmetric monodromy then follows once that fibre is at
  most two-to-one and the actual action is primitive. It also shows the resulting source extension
  has no intermediate field under full monodromy (`CriticalSchurUniqueRamifiedPrime.lean`,
  `CriticalSheetSingularity.lean`, `CriticalSheetFixedConormal.lean`,
  `CriticalSchurUniqueCollisionPoint.lean`, `CriticalSchurCollisionSupportFibre.lean`,
  `CriticalGeometricDegreeExact.lean`, `CriticalGeometricFieldPrimitivity.lean`). This is a genuine
  non-classical internal-dynamics mechanism that could feed PPM/IRK/HJ. It is not yet an RH route:
  corpus has neither the remaining two-to-one fibre bound with unconditional arithmetic
  primitivity/source occurrence nor a coefficient-faithful Xi-divisor handoff.
- Differential horizon modules identify every finite positive-jet gauge with the constant
  translation stabilizer, prove depth-independent rigidity when the locus is translation-rigid and
  the field has no primitive of one, and now reconstruct the entire differential field from any
  positive derivative horizon on a translation-rigid locus. On an additive cylinder, each lost jet layer is
  exactly a vector-group torsor; for a commutative `D`-group the horizon stabilizer is its sharp
  subgroup (`JetHorizonReconstruction.lean`, `JetHorizonAdditiveTorsorLaw.lean`,
  `DGroupHorizonStabilizer.lean`). The Manin-horizon reconstruction theorem still takes the
  nonorthogonality-to-isogeny direction as a named Hrushovski-dichotomy premise
  (`ManinHorizonIsogenyReconstruction.lean`). No arithmetic `D`-group, unconditional dichotomy
  specialization, or Xi landing exists, so this is a pre-route mechanism, not a live/candidate
  route. Working-tree `CassidyAdditiveEvaluated.lean` adds the evaluated additive classification:
  every proper differential Hopf ideal yields a nonzero constant-coefficient linear jet relation.
  This sharpens the subgroup firewall but does not instantiate the missing arithmetic group. It
  indicates a possible singular/infinite-action successor to AF.
- `LogDerivRelationSubgroup.lean` transfers constant-coefficient additive differential subgroup
  laws to multiplicative units exactly by logarithmic derivative. It strengthens the differential
  group interface behind the Manin/AF pre-route, but constructs neither a nontrivial arithmetic
  subgroup occurrence nor an Xi reader.
- Difference-Galois infrastructure now extends well beyond existence of a Picard--Vessiot ring:
  companion/Casoratian solution spaces, no-new-constants matrix representations, faithful Galois
  action, tensor-square torsor generation, parameterized sigma--delta constants, and the exact
  operator-factorization/Riccati equivalence are formal. A modified-Bessel order recurrence is
  proved irreducible over `C(X)` (`DifferenceGaloisRepresentation.lean`,
  `DifferenceTensorTorsor.lean`, `ParameterizedDifferenceGalois.lean`,
  `DifferenceOperatorFactorization.lean`). `SigmaIdealConstantCoefficients.lean` adds the
  minimal-support engine producing nonzero constant-coefficient elements in sigma-ideals, the
  algebraic input for a tensor-square torsor correspondence. `NullstellensatzPoint.lean` closes a
  further algebraic gap: every nontrivial finite-type algebra over algebraically closed constants
  has a constant-valued point, and an invertible comparison matrix specializes to an invertible
  matrix over those constants. `SigmaConstantsDisjointness.lean` derives linear disjointness of
  constants from sigma-simplicity and proves a nonzero sigma-ideal meets the constant span
  nontrivially. `DifferenceSpecialization.lean` turns a sigma-compatible tensor-square point into a
  base endomorphism commuting with the difference operator and moving the fundamental matrix by an
  invertible specialized comparison matrix. Thus the formal Galois torsor has actual matrix points and faithful constant
  contraction rather than only an ideal-theoretic avatar.
  `ParameterizedPicardVessiotExistence.lean`, `ParameterizedPicardVessiotQuotient.lean`,
  `TorsorDecomposition.lean`, `TorsorPointSpecialization.lean`, `TensorSquareDerivation.lean`,
  `ParameterizedTensorTorsor.lean`, `ParameterizedSpecialization.lean`, the sigma-jet coordinate
  modules, and working-tree `ParameterizedGaloisRepresentation.lean` now close the parameterized Picard--Vessiot quotient,
  commuting tensor-square derivation, constant comparison matrix, full tensor torsor
  decomposition, point specialization, and faithful matrix representation over differential
  constants. This is a genuine non-classical
  carrier adjacent to AF/AP/IRK, but no literal prime--Gamma difference system, source-selected
  invariant, or critical-line reader exists. It remains pre-route infrastructure rather than a
  additional candidate.
- Finite quantum-channel diamond contraction and Markovian return recovery are now exact, including
  ancilla-assisted information-loss and inverse-word incidence reflection
  (`QuantumChannelDiamond.lean`, `MarkovianReturnRecovery.lean`). Exact return is rigid: every
  intermediate channel is unitary conjugation, the semigroup is periodic, and incidence counts are
  palindromic (`ChannelInverseRigidity.lean`, `MarkovianExactReturn.lean`). Thus genuinely
  dissipative exact-return variants are closed. Approximate-return information loss remains a
  paired, non-scalar mechanism potentially relevant to HC or a successor to J, but no prime--Gamma
  channel, collision quantum comparison, or RH endpoint is instantiated.
- Semidefinite Caratheodory--Fejer data now have exact finite unit-circle atomic factorization,
  active-node support extraction, and corank-one kernel-root control. The Connes--van Suijlekom
  Toeplitz theorem and its real form are formal. Regularized determinants exist at every finite
  order, forget exactly the lower power traces, scale correctly, and extend faithfully to linear
  pencils (`CaratheodoryFejerRankCorankOne.lean`, `ConnesVanSuijlekomToeplitz.lean`,
  `FiniteRegularizedDeterminantOrder.lean`, `RegularizedDeterminantForgetting.lean`,
  `PencilDeterminantCompletion.lean`). These close finite OPUC/C1/O realization and completion
  adapters, not source Toeplitz sections, cofinal convergence, orientation, or ground sign.
  `ConnesVanSuijlekomAppendixB.lean` additionally identifies its three-parameter source cone with
  the exact positive-semidefinite half-space image and preserves and reflects extreme rays under
  that coordinate map. This is finite cone geometry, not a source-selected Xi extremal ray.
  `ConnesVanSuijlekomAppendixA.lean` closes the claimed bi-infinite matrix identity as diagonal plus
  rank-four correction. `ConnesVanSuijlekomAppendixBN1.lean` proves the normalized `N=1` extremal
  eigenvector numerator is real-rooted in the valid cases but also gives a literal counterexample
  to Proposition B.1 as printed when the extremal eigenvalue is not simple: the zero source matrix
  makes every nonzero vector extremal while `(1,-1,1)` has a nonreal numerator zero. Any C1/OPUC
  use must retain a simplicity/nondegeneracy hypothesis; finite extremality alone is false.
  `MicroSpectrumMomentAssembly.lean` still warns that lower finite moments can hide in arbitrarily
  small spectral energy.
- Siegel reduction/finiteness and damped quasi-abelian Poincare normal convergence are now formal
  (`SiegelFiniteness.lean`, `QuasiAbelianDampedNormalConvergence.lean`). They supply finite
  identifications and locally normal aggregate carriers, but no completed-zeta source specialization
  or RH reader. They therefore do not revive AP or AF.
- `ArbitraryLabelEndReconstruction.lean` removes the finite-label hypothesis from one-ended
  coherence reconstruction: on an infinite preconnected finite-boundary one-ended graph, any
  arbitrary-type label with finitely many changing edges is constant off a finite vertex set. This
  strengthens a global-coherence receiver, but the corpus supplies no literal completed-arithmetic
  graph whose finite variation or end value yields an RH orientation; it is not a new route.
- Polynomial-matrix quadratic-rate relations now have endpoint-complete extension charts, exact
  six-real-coordinate physical leaf charts, and a shell-global nonflatness/orbit-escape capstone:
  one simple-spectrum witness forces failure inside every nonempty real open set of interaction
  coefficients (`TheoremAExtensionCapstone.lean`, `PhysicalChartCoordinates.lean`,
  `ShellQuadraticRateGlobalisation.lean`, `SpanCoordinateJunction.lean`).
  `AnchorStarAdjugateTransfer.lean` identifies the full-chart adjugate eigenvectors on
  the anchor-star line with the split-family germs and transfers germ endpoint completeness to all
  sufficiently small nonzero couplings. `ChartEndpointGenericIntersection.lean` then proves a
  complete chart point exists and every dense parameter set meets the endpoint-complete locus.
  `GeneralParametricEigenbranch.lean` removes the diagonal-base restriction: any analytic finite
  matrix family at a unitarily diagonalizable simple point has analytic eigenvalue branches and
  analytic canonical adjugate eigenvectors. `GeneralEndpointGenericIntersection.lean` then carries
  endpoint-complete genericity to arbitrary complex Banach parameter spaces. These remain finite
  transversality results, not arithmetic source selection.
  This supplies finite spectral transversality potentially
  useful to HC/SV2/OPUC, but has no arithmetic specialization or Xi endpoint and cannot replace a
  cofinal source law.
- `LocalAnalyticNullPreimage.lean`, `EuclideanAnalyticNullPreimage.lean`, and the multivariate
  analytic-null modules prove that a locally nonconstant real-analytic map on an open finite-real
  parameter domain pulls Lebesgue-null sets back to null sets. This closes generic-measure
  bookkeeping for finite chart arguments; it neither selects the arithmetic parameter nor supplies
  a cofinal Xi law.
- `SphereAnalyticPushforward.lean` proves a ray-constant analytic phase nonconstant on every open
  patch has absolutely continuous spherical pushforward and dephases every bounded angular weight.
  This supplies an infinite angular-cancellation adapter, but no completed prime--Gamma phase or Xi
  landing is instantiated.
- `CompactGroupAlmostPeriodic.lean` proves every continuous compact-group flow observable, including
  finite-measure screen expectations, is Bohr almost periodic; if it tends to zero at infinity it
  is identically zero. `PrimeScreenAlmostPeriodicNoGo.lean` instantiates this on the full infinite
  prime torus `product_p S1`: neither a bounded continuous symbol nor a finite-measure translated
  screen expectation can equal the completed Xi amplitude, because Xi decays vertically but is
  nonzero at the center. Thus prime phases alone cannot perform completion; a successful AF/G/MSC
  screen must retain noncompact archimedean data, be singular/unbounded, or leave this class.
- New sieve mean-value, divisor-moment, exceptional-set, and Halasz--Montgomery modules close exact
  analytic adapters used in long chains (`Sieve/DivisorMomentMeanSquare.lean`,
  `Sieve/HalaszMontgomeryIntegral.lean`, `Sieve/Section4Core.lean`). Their capstones retain explicit
  mean-square/exceptional-set premises; they neither define E's fixed relation nor prove T's pure
  short Möbius-block cancellation.
- `PrimeArchBernsteinMobiusPullback.lean` and
  `PrimeArchBernsteinMobiusPullbackSource.lean` remove finite Bernstein coefficients from the
  prime--arch moment germ, identify the pullback with a two-torus Gutzmer susceptibility, and give
  an exact continued prime--arch trace source formula.
  `BernsteinLegendreDoubleSourceKernel.lean` now proves the full bivariate-moment Bernstein row
  kernel, its Legendre coefficient identity, conjugate-reflection quadratic factorization, positive
  first branch point, and—under non-RH—equality of that pinch radius with the attained prime--arch
  Abel critical radius. This improves the C1/OPUC source interface and precisely locates the
  false-RH singularity, but supplies no unconditional sign, convergence, or RH handoff.
- `EulerSquarefreeDyadicStateFactorization.lean` proves the unique
  squarefree-times-square mass identity, constructs normalized Euler and signed-squarefree pointed
  states, builds the exact Möbius-phase arithmetic unitary, and proves coordinatewise tensor-state
  factorization `U e_sigma = s_sigma tensor e_(2 sigma)`.
  `EulerSquarefreeDyadicLogTransport.lean` transports the logarithmic observable across that same
  unitary with no core-domain premise and proves the convergent pointed-current law
  `b_sigma = a_sigma + 2 b_(2 sigma)`. This is a genuine infinite, signed, paired source
  decomposition adjacent to E/MSC, now preserving its logarithmic current as well as its state, but
  it contains no Xi divisor, completed boundary landing, or RH implication; it does not create
  another route. `EulerSquarefreeDyadicLogMoments.lean` further proves convergence of every
  logarithmic moment, exact summed moment splitting through order two, and exact variance
  additivity `Var_E(sigma)=Var_sq(sigma)+4 Var_E(2 sigma)`.
  `EulerSquarefreeDyadicFisherTangent.lean` realizes the centered Euler and squarefree Fisher
  tangents as honest orthogonal `l2` vectors, identifies their squared norms with those variances,
  and proves the exact vector split
  `U chi_E = chi_sq tensor e_(2 sigma) + s_sigma tensor r`. Thus paired first-order source geometry
  is now closed. `EulerSquarefreeDyadicAnalyticTelescope.lean` and
  `EulerSquarefreeDyadicTower.lean` add the exact squarefree zeta quotient, iterated dyadic zeta/log
  telescopes, and unitary mass tower. `EulerSquarefreeDyadicFisherDefect.lean` computes the exact
  covariance-isometry defect and proves its critical residual energy tends to zero. The unchanged
  missing interface is a completed Xi/divisor boundary landing or orientation law.
- `VivantiPringsheim.lean` proves the full positive-boundary theorem. The completed source
  specialization is no longer missing: `PrimeArchBernsteinPringsheimCollar.lean` proves equality of
  real and complex critical radii, noncontinuation at the positive boundary, and the collar-to-RH
  transfer. This creates candidate BPC above. What remains absent is the source-derived analytic
  continuation through the collar.
- `SegmentAnalyticContinuation.lean` gives a reusable identity-theorem transport along any real
  segment contained in an open analytic domain. It closes continuation bookkeeping but supplies no
  arithmetic initial identity, sign, or Xi landing.
- `PrimeArchMomentPoleResidue.lean` computes the exact reciprocal-square pole fibres and residues of
  the endpoint moment resolvent, including reflection and multiplicity. Positivity of all pole
  locations, unit pole amplitude, and the corresponding pole confinement are exact RH receivers,
  not producers. `XiSquareDescentVerticalModulus*.lean` likewise proves global—and one explicit
  localized—vertical modulus monotonicity of the square descent is exactly RH.
- `XiOuterEulerModulusPrimeSeamAntialignment.lean` proves the outer-Xi modulus defect and prime-clock
  reflection amplitude always have opposite sign; demanding nonnegative alignment forces their
  product to vanish and hence RH. This is a sharp orientation receiver adjacent to G/SEC, not an
  upstream source mechanism.
- `FiniteMomentDivisorReconstruction.lean`, `HermiteBiehlerPairRankCensus.lean`, and
  `XiHedenmalmLocalAlgebraRankCensus.lean` show finite packet moments determine the full finite
  divisor and compute exact multiplication rank/nullity: rank is distinct-zero count and nullity is
  total multiplicity minus that count. The resulting dyadic census is only a receiver: producing
  its required divisibility across all packets carries the same burden exposed by terminal IW.
- `RemotePairEscapeGauge.lean`, `KreinEscapeAnalyticFamily.lean`,
  `KreinEscapePowerFieldInvariance.lean`, `KreinIndexEscapeStratification.lean`, and
  `FaithfulIndexFredholmObstruction.lean` prove arbitrarily many negative-square pairs can escape to
  infinity under compact-open convergence without changing the differential-adjoin class, while
  finite Morse index is norm-locally bounded near a coercive-complement Fredholm operator. Hence no
  norm-continuous index can remain faithful on this escape class. This blocks a continuous finite
  index as the missing secondary orientation for C1/P/PCS; singular, determinant-line, or
  infinity-sensitive data are required.

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
| weighted-Mertens half-unit tower as producer | One exponent gives one zero-free half-plane, but the full tower `0<=alpha<1/2` is exactly RH; it cannot be invoked as an upstream estimate. | Exact causal transform, one-moment transfer, and invariant half-unit prelimit deficit guide MSC/G aperture research. |
| Suzuki v2 entire characteristic wall | Displayed target has an unavoidable pole, so no all-plane locally uniform limit of entire real-zero characteristics exists; finite holomorphic exponential gauges do not remove it. | Actual entire real-zero Suzuki characteristics now exist; live SV2 uses the corrected two-chart spherical wall. |
| Deninger finite quaternionic real descent | Quaternionic anti-linear square `-1` forces even complex multiplicity, but root number `-1` forces odd central order; order-equals-multiplicity real symplectic realization is impossible. | Literal `QuaternionGroup 2` symplectic representation, two irreducible quadratic stages, degree-eight radical certificate, and anti-commuting radical lifts are formal; arithmetic root-number realization and normal/Galois identification remain, but any successor must alter finite real descent or physical comparison. |
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
- bounded scalar differential order `exp(O(1/omega))` at critical Möbius aperture: full retained
  mass forces `omega*log(aperture)` to diverge;
- the complete half-unit weighted-Mertens moment tower as an independent source input: it is
  equivalent to RH, while prelimit continuation remains short by exactly one half;
- ordinary Fredholm index of the prime co-shift boundary complex: divisor kernel and cokernel are
  born together and its index is identically zero;
- norm-continuous finite Krein/Morse index on compact-open remote-pair escape families: arbitrarily
  many negative pairs can disappear at infinity while local differential data stay unchanged;
- square-descent vertical modulus monotonicity and outer-Xi/prime-clock nonnegative alignment as
  upstream estimates: each is already an exact RH receiver;
- finite-packet local-algebra divisibility as an arithmetic producer: moments and rank census are
  exact, but supplying the global divisibility repeats IW's terminal burden;
- completed Xi from a bounded continuous compact prime-torus screen or finite-measure screen
  expectation: its signal is Bohr almost periodic, while Xi decays vertically and is nonzero at the
  center;
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
rather than removing it. MSC proves mass escapes beyond every fixed compact synthesis and that full
retention forces unbounded scaled aperture. SV2 now has a canonical cofinal projective normal family
but still needs global target identification and reciprocal-chart control. Cofinal argument needs
synchronized estimate, not iterated pointwise limits.

### Singular boundary is not removable technicality

L, G, P, U, O, SV2, PCS, SEC, and BPC reach a completion or continuation boundary where smooth
interior misses state. Gamma
sewing beats finite Rees order; Kelvin charts cannot share scalar renormalization; first contact can
be rough; an ordinary index can cancel simultaneous kernel/cokernel birth. Needed objects are
relative, graph-valued, nonlocal, multi-chart, or non-scalar. L's exact lower jets show that even
correct algebraic annihilation still needs bounded topological closure before physical descent.

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

MSC, SV2, PCS, SEC, and BPC form a second non-classical family: infinite paired/operator/graph or
analytic source followed by a singular, meromorphic, or homological boundary landing. MSC has the carrier but lacks pointed
divisor covariance. SV2 now has actual entire real-zero characteristics, a canonical paired
projective family, and local cofinal compactness; it lacks global target identification and the
reciprocal pole chart. PCS has an exact all-prime graph, spectral gap, and divisor boundary
complex but lacks a secondary class capable of seeing homology whose ordinary index is zero. SEC
has an exact end-coherence collapse but lacks a source-fixed graph and finite-variation law. BPC
has the exact positive susceptibility singularity and collar-to-RH transfer but lacks source
continuation through that collar. None can be reduced to one finite positive object or one scalar
response without hitting a proved
firewall.

Critical Schur monodromy, difference Picard--Vessiot, differential/Manin horizons, and quantum
return recovery sit one layer earlier. Lean has constructed their internal dynamics, rigidity, or
reconstruction theorem, but not an arithmetic source occurrence plus critical-line reader. They are
therefore real possible source architectures, not counted RH candidates. Their shared open core is
an arithmetic specialization theorem: build the actual prime--Gamma/Mobius action globally, prove
its nontrivial invariant before choosing a zero, and show that invariant excludes an off-line Xi
divisor. Exact-return unitarity, jet-translation gauge, and finite differential-algebraic spectrum
already specify which naive specializations cannot work.

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
   (CCM-FU, E, O, T, U, SV2).
6. **Source-native internal dynamics:** projective module, corrected Stokes category, monodromy, or
   analytic continuation on the literal completed source
   on actual arithmetic carrier before divisor selection (SC, PPM, IRK, OPUC, HJ, BW, MSC, PCS,
   SEC, BPC).
   Abstract Weyl existence, Arakelov power pullback, all-plane entire Suzuki convergence, and finite
   real quaternionic descent are classified terminal in their stated architectures.

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
5. Can Burnol's top-jet evaluator be made bounded on completed source and can the resulting
   all-prime Green restriction have common kernel exactly arithmetic boundary with target equal to
   existing physical landing?
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
13. Can the concrete Möbius signed-channel feature cross its exact half-unit continuation deficit,
    pointed residue/graph-domain wall, and unbounded-aperture requirement to satisfy a source-derived
    four-unit covariance bound?
14. What source identity forces the canonical Suzuki projective normal-family limit to equal the
    global Xi Livsic/projective target, and how does that identity propagate through the reciprocal
    pole chart?
15. Can critical Schur monodromy, a difference Picard--Vessiot group, a Manin-horizon sharp group, or
    approximate quantum-return loss be instantiated on the literal completed arithmetic source and
    coupled coefficient-faithfully to Xi before divisor selection?
16. What completed reflection-sensitive secondary class detects prime co-shift divisor homology
    despite its identically zero ordinary Fredholm index, and why must that class exclude homology
    throughout `1/2<Re(s)<1`?
17. Which fixed arithmetic graph on primes is one-ended and makes the canonical FE--Schwarz seam
    have finite edge variation for every Xi divisor, without choosing edges from the observed seam?
18. Can the continued prime--Gamma/Mobius expression be analytically continued through the full
    Bernstein susceptibility collar without importing a zero-free region or an equivalent radius
    bound?

Until one is answered, endpoint reformulations, finite real-zero models, seed asymptotics, diagonal
moment inequalities, or scalar transport identities do not move formal RH frontier.
