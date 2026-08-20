# Current Formal Frontier Toward Proving or Disproving the Riemann Hypothesis

## Scope, evidence, and status language

This document states where the `HTGeometry`, `HilbertMetric`, and `RHTower` Lean corpus stands now.
It maps architectures, theorem chains, open cores, and terminal mechanisms. It is not a chronology,
work log, literature survey, or inventory of every RH-equivalent proposition.

**Formal-corpus cutoff:** 20 August 2026, commit
`13cec320a5eedd6b75ac095c8fba107df5a4d913`, plus declaration-index review of current Lean
working-tree additions. Scientific status below comes only from Lean declarations, dependencies,
theorem docstrings, and explicit gap/no-go markers. Pipeline cards and papers are not evidence for
this map. Working-tree declarations are identified and not claimed build-audited in this
documentation-only pass.

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

Formal corpus currently supports fourteen live architectures:
`CCM-FU, C1, D2, E, G, L, O, P, Q, CLG, T, U, HC`, and
**SV2 (Suzuki spherical characteristic convergence)**. Thirteen corpus-born receiver/source-mechanism
candidates remain: `UEB, PSRC, PBM, SC, PPM, IRK, OPUC, HJ, BW, MSC, PCS, SEC, BPC`. Routes R, IW, and AP are terminal as independent
producers. Latest additions close important intermediate premises, but do not close any route's
final open producer and prove neither RH nor its negation.

| Architecture | Proved chain | First open core |
|---|---|---|
| CCM-FU | completed Guinand--Weil third-grade source -> literal triangular prime-minus-polar window -> exact positive-kernel anchored moment -> Xi-screw Green -> RH | For one fixed `b>0`, uniformly bound the explicit triangular source window, equivalently `int_b^H (96-64h/H)h^-4 (E(b)-E(h)) dh`; this is exactly the former linear-Cesaro gate. |
| C1 | corrected theta/prime--Gamma source -> Weil/Connes form or real spectral realization -> RH | Construct a source-derived non-dominating or signed correction before final positivity; raw positive/passive Stokes completion is impossible. |
| D2 | continued prime--arch trace -> one-sided anti-Herglotz/finite ceiling -> RH | Source control of sole positive-frequency tail by a reflected signed/non-dominating law; canonical directed passive limits are impossible. |
| E | squarefree Wold source -> two-sign half-power marker supply -> exact integer-pair incidence -> unit-load Hall transport with moving flux -> RH | Build one Ramaré-supported relation joining proved marker supply to relation-specific subinterval Hall, unit load, co-moving flux, and Gibbs cost. |
| G | Suzuki/Mobius/Gamma source -> marked pre-scalar or signed-channel carrier -> exact Ward landing -> wall orientation -> RH | Independent source law forcing the already-transported Ward coefficient to vanish or have the required signed order; Schur coisometry and causal limit do not supply four-unit orientation. |
| L | completed Green/BV/Big-Witt/co-Poisson source -> bounded completed jet system -> singular Calderon--Witt comparison -> physical reader -> RH | Extend the now-bounded literal first Sonine logarithmic Mellin jet to all required multiplicity jets and completed closure, then identify resolved flatness with the existing physical landing before divisor specialization. |
| O | exact restricted-Weil operator -> canonical true-ground heads -> coherent signed producer -> nonnegative floor -> RH | Sign of cancellation-preserving coherent finite-head producer, equivalently eventual reverse-prime control on canonical actual heads. |
| P | source-horizontal second-Cartier orbit -> Route-N capacity/radial-work bridge -> radial Krein energy -> endpoint moderation -> RH | Produce endpoint order globally before divisor selection; regular reflection-pair extraction, finite circle measure, and literal scalar short are formally ruled out. |
| Q | continued Hurwitz/Cauchy source -> countable Gaussian-rational Euler-pole paired kernel -> orientation zero -> RH | Prove source passivity of every finite matrix of the explicit scalar paired value kernel on Gaussian-rational poles in one absolute-Euler quadrant. |
| CLG | centered completed source -> exact archimedean-minus-von-Mangoldt Loewner generator -> critical Carathéodory kernel PSD -> zero-free right half-plane -> RH | Prove finite critical archimedean Loewner matrices dominate complete prime Loewner matrices directly from Euler--Gamma source; positive-shift generator flow is formally impossible. |
| T | finite Xi-Taylor/theta-tail source -> exact reflection bridge -> raw core-current bound -> RH | Signed short Möbius-block cancellation strong enough to control the combined top-row plus surviving finite-translation remainder. Full GS schedule and uniform smooth/full-series Möbius power savings are now proved. |
| U | shifted hard-edge source -> cofinal shifted Hankel tail or first-contact exclusion -> RH | Non-scalar source mechanism excluding the exact nonintegrable strict-frontier quotient, or uniform cofinal tail order. |
| HC | two-prime/Cayley/Gauss--Hodge source -> quantized horizontal collision charge -> strict sub-two or prime-summability law -> RH | Absolute subquantum estimate or source-first prime-summability for the literal paired Gamma-six determinant current. |
| SV2 | literal Suzuki energy space -> paired self-adjoint characteristics -> bounded projective normal family -> global Xi projective target -> corrected two-chart spherical limit -> RH | Identify the canonical cofinal subsequential limit with the divisor-faithful global target, then extend convergence over the full finite chart and reciprocal pole chart. |

Current formal state adds one live route and one candidate. Live `CLG` proves
that the critical logarithmic-derivative Loewner kernel is PSD exactly under RH, splits it on the
Euler region into an archimedean kernel minus the complete von-Mangoldt phase kernel, and proves
every positively shifted generator is non-PSD. Its viable premise is critical source domination,
not a positive Loewner flow through shifted generators. Candidate `PBM` identifies the continued
grade-one prime current's quantized residue at every right-strip zero, proves this charge escapes
every fixed endpoint chart, and makes absence of charge exactly RH. Entire cumulants and locally
uniform limits of zero-free finite Euler fields cannot create that charge. PBM therefore requires a
singular infinity-sensitive zero-charge law, not finite completion.

Route E now has unconditional unsigned cofactor supply outside its prescribed polylogarithmic prime
band and a complete measurable-set/ladder exceptional-set split. Route T now has all-height twisted
Mertens and damped Ramaré-cofactor bounds with super-polylogarithmic saving, uniformly for
`|tau|<=N`. These close additional unsigned analytic rows but do not supply E's fixed relation or
T's signed short-block current cancellation. Hardy's theorem is formal in dyadic-window and
logarithmic-count form; Levinson's detector has bounded noncritical rectangle edges and exact
phase-to-odd/singleton-fibre charging. Detector zero count remains undetermined, so HC gains a
source-to-census interface but no absolute off-line upper bound. Prime-trace energy now charges a
finite off-line ordinate packet by at least its squared multiplicity, while prime-diagonal energy
has natural double-logarithmic divergence. Without a relative subtraction or absolute finite upper
budget, this is not HC's producer. Random Euler, Fisher, prime-boundary Poisson/Wick, determinant
completion, difference-Galois, and finite-conductor Dirichlet additions are classified below as
pre-route infrastructure or firewalls.

Latest committed delta adds an exact Gaussian smooth AFE with movable reflected edge, certified
fundamental discriminants for all three quadratic CRT families, a positive block Hodge identity on
every surviving multiple-sine face, finite-dimensional closure of finite-pencil trace jets, and
finite paired Super-Poincare packages for existing CCM/reflection operators. Current working tree
adds the all-grade prime-power Marcinkiewicz carrier, `SL_2` elementary factorization, and three
Gamma pole-avoidance/continuity lemmas. These additions change no live or candidate count. The
all-grade carrier is a genuine infinite, multi-grade, nonphysical pre-route adjacent to PBM/PPM:
Lean proves the grade-one embedding is isometric and projection contractive, but does **not yet**
prove the file-level advertised nonlinear Euler-ray tail or equality of all-grade and grade-one
corona classes. No open producer is closed; RH status is unchanged.

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
error; midpoint coefficient `1/2` is forced by the prime jump debt. The Cesaro gate now has an
exact source-side normal form. For `H>b>0`, its kernel

```text
K_H(h) = (96 - 64 h/H) / h^4
```

is strictly positive on `[b,H]`, lies between `32/h^4` and `96/h^4`, and the normalized third-grade
Cesaro primitive is exactly the anchored signed moment

```text
integral_b^H K_H(h) * (E(b) - E(h)) dh.
```

Uniform boundedness of these moments is equivalent to the former linear-Cesaro estimate and implies
RH (`CCMGuinandWeilThirdGradeCesaroAnchoredMoment.lean`). Positivity belongs to kernel, not completed
error difference; theorem preserves cancellation and assumes no pointwise sign. More strongly, the
same anchored moment is exactly

```text
ccmGuinandWeilPrimePolarWeightedWindow b H
  (h ↦ ccmGuinandWeilThirdGradeWeight(h) * (1-h/H)).
```

The moving triangular test is positive on window, vanishes at upper wall, and its negative
derivative is `K_H`. Thus prime and polar channels remain coupled before completed-error
scalarization (`ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_eq_primePolarTriangularWindow`).

Formal sources: `CCMGuinandWeilPrimeEntryThirdJetTransverse.lean`,
`CCMGuinandWeilXiScrewGreenConnection.lean`,
`CCMGuinandWeilThirdGradeCesaroCompleteness.lean`,
`CCMGuinandWeilThirdGradeCesaroAnchoredMoment.lean`,
`CCMUnitRieszCesaroSignedReporterSymbol.lean`,
`CCMUnitRieszCesaroSourceRelativeReporter.lean`,
`CCMPolarPrimeMidpointCodiagonal.lean`.

**Open core.** For some fixed `b>0`, prove uniform boundedness of literal triangular
prime-minus-polar windows, equivalently

```text
| integral_b^H ((96 - 64*h/H)/h^4) * (E(b) - E(h)) dh | <= C
```

for every `H>b`, where `E` is completed third-grade prime-minus-polar cumulative source. This is
exactly equivalent to linear growth of prior Cesaro primitive, and remains broader than pointwise
sign or subcubic control because large signed oscillations are allowed. Window formation and
prime--polar coupling are closed; open datum is cancellation inside that explicit positive test,
not positivity of completed error.

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
one-prime remainder or orient the resulting spectrum. The translated reciprocal-seam norm has its
unique minimum at zero; preservation at one nonzero translation and boundedness of the whole orbit
each imply RH (`XiReciprocalTranslationSeamNormLaw.lean`). The radial Jensen mass gap is exactly
reflection energy and Schur-capacity saturation is equivalent to RH
(`XiRadialJensenSchurCapacity.lean`). These are complete spectral receivers, not corrected source
realizations. The Vivanti--Pringsheim theorem is now instantiated on a completed prime--Gamma
Bernstein susceptibility in candidate BPC below. That gives a distinct continuation-to-RH route,
not C1's missing signed/non-dominating spectral carrier.

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
their producers differ. TSR now supplies an exact canonical theta square-rate coefficient reader,
but its scalar causal reflection is zero/duplicate and therefore cannot furnish C1's missing
signed second orientation.

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
geometric ladder. `Sieve/JointLongRange.lean` installs that free ratio in the actual long designated
prime range: its mesh tends to zero, the top eventually reaches at least one quarter of target,
harmonic mass diverges, base lies below top, and the ladder covers the range. The geometric
block-cardinality, defect-on-parts, Section-4 disc-relative/summed, and annulus-cofactor/summed laws
carry these controls through the remaining analytic decomposition
(`Sieve/GeomBlockCardBound.lean`, `Sieve/LadderDefectOnParts.lean`,
`Sieve/Section4DiscRel.lean`, `Sieve/Section4DiscSum.lean`,
`Sieve/Section4AnnCofactor.lean`, `Sieve/Section4AnnSum.lean`). None chooses adjacency or supplies
the co-moving parity flux. `Sieve/PrimeCosineSumSharp.lean` separately removes the old
zero-free-strip coupling between frequency and prime cutoff: at the standard abscissa, the
three-four-one inequality gives a prime-cosine lower bound with only one-quarter frequency loss,
and hence a Möbius multiplicative-distance lower bound

```text
(log log z - log log |t|)/4 - C
```

with no condition linking `z` and `t`. This enlarges the unconditional phase-separation range but
still supplies neither relation adjacency nor Hall/co-moving flux.
`Sieve/PrimeCosineTailAbel.lean` formalizes the exact Abel step from a uniform linear bound for
unweighted tail-prime cosine partial sums to a reciprocal-weighted tail bound with one logarithmic
loss. The required uniform partial-sum saving remains a hypothesis, so this is an analytic adapter,
not E's producer. `Sieve/PrimeRangeTwistTail.lean` now discharges initial prime-range arithmetic
and Abel summation against Route T's envelope. `Sieve/RouteTEnvelopeRho.lean` and
`Sieve/RouteTTailRho.lean` reduce remaining tail premise to three explicit real inequalities at
every block top: contour decay, Perron-truncation decay, and Chebyshev remainder below `rho`.
`Sieve/RouteTTailSurrogate.lean` replaces remaining internal width/height quantities by closed
functions of block top and frequency. `Sieve/RouteTTailElementary.lean` then bounds these by the
elementary schedule forms

```text
9 C i^(-m/6) (HF + 2 log i) <= rho,
9 C 3^v i^v (1 + (log i)^2 + HF) / |t| <= rho,
24 i^(-1/4) <= rho.
```

Its tail capstone assumes all three inequalities at every intermediate block top; it does not
prove them from the schedule. `Sieve/RouteTSurrogateSize.lean` further majorizes height and
reciprocal width by explicit increasing budgets depending only on `log|t|`.
`Sieve/RouteTTailBudget.lean` substitutes those budgets through contour and truncation terms and
transfers the resulting three fully explicit `log i`/`log|t|` hypotheses to the tail bound. It
still assumes them at every chosen block top. The schedule chain then specializes
`y=ceil(exp((log z)^0.99))` and `rho=1/(9(2+log z))`. Worst-case and threshold modules prove
contour, truncation, Chebyshev, cutoff-growth, inverse-budget, and fixed low-frequency facts
eventually; `GSTailAssembly.lean` gives tail cosine norm at most one and `GSTailMass.lean` retains
`0.01 log log z-O(1)` harmonic prime mass. `MoebiusDistanceHighFreq.lean`,
`MoebiusDistanceUniform.lean`, and `MoebiusDistanceAllFreq.lean` assemble the conditional
all-frequency distance theorem. `Sieve/MoebiusSmoothPolySaving.lean` now composes every threshold
at integer `z`, proves the unconditional eventual distance lower bound uniformly for
`log|t|<=2 log z`, and derives

```text
||sum_{n squarefree and z-smooth} mu(n)n^(-1-it)||
  <= C (log z)^0.99,    |t| <= z^2.
```

`Sieve/MoebiusDistanceSharp.lean` independently gives a hypothesis-free all-scale bound with
explicit `z` and frequency dependence. These close E's GS-tail analytic subgate, but do not define
relation adjacency, prove interval Hall or unit load, or provide co-moving flux.

E's current source layer closes additional **unsigned supply and partition** rows more sharply.
`RouteECofactorBandMass.lean` proves the Mertens mass of a polylogarithmic prime band tends to its
exponent ratio and, at E's fixed exponents, is eventually below `1/8`. Both Möbius parity classes
avoiding that band therefore carry square-root mass `gg sqrt(T)` and harmonic mass `gg log T`, with
no retained band hypothesis. `Sieve/RamareBlockSplitOn.lean` gives the Ramaré bilinear mean-square
split over an arbitrary measurable frequency set. `Sieve/Section4AllBlocksSmall.lean` makes the
Q-side estimate automatic on the all-small set and covers its complement by single-block
exceptional sets; `Section4CofactorSup.lean`, `Section4LadderExceptional.lean`, and
`Section4RelativeThreshold.lean` control the cofactor supremum, whole-ladder exceptional measure,
and relative-threshold moment loss. Working-tree `RamarePartitionedLadder.lean` and
`RamareAnnulusPartitioned.lean` assemble the three-piece disc/annulus/exceptional partition;
`RamareAffinePartitioned.lean` packages resulting affine majorant uniformly below cutoff.
`FibreRamarePartitionedFinal.lean` carries that majorant through Gallagher kernel and fibre bridge to
the Route-E fibre mean square. Its capstone still assumes the ladder defect, pointwise block bounds,
exceptional cofactor bound, and exceptional prime mean square; it is an exact assembly theorem, not
an unconditional final fibre estimate.
These theorems strengthen capacity and cost accounting only: none declares which two opposite-sign
integers are adjacent in one source-fixed relation, so they cannot prove Hall or co-moving flux.

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
`BurnolSoninFiniteJetEvaluation.lean` closes the first nontrivial completion step: the literal first
logarithmic Mellin derivative kernel has exact norm, is square-integrable on every strict right
tail, admits a local `L2` majorant, differentiates under the literal Mellin tail integral, and
defines a bounded continuous linear functional whose value is that derivative integral. This is a
genuine completed first-jet evaluator, not merely a pointwise formula. It does not yet supply every
higher jet required by arbitrary Xi multiplicity, the completed Sonine closure/aperture-complement
classification, or physical descent.

**Open core.** Two completion gates remain in series. First, extend the bounded first-jet theorem to
all finite multiplicity jets required by Xi divisors and prove the higher-jet completed
closure/aperture-complement theorem needed to pass the algebraic lower-jet system to the completed
source space. Second, construct the source-derived singular
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
candidate conjugation lifts anti-commute on the top radical. Eight explicit automorphisms now prove
that legacy radical field Galois over `Q`, and its Galois group is identified with
`QuaternionGroup 2` (`DeningerQ8RootNumberNegOneGalois.lean`,
`DeningerQ8RootNumberNegOneGaloisIdentification.lean`). These algebraic closures still do not
supply a root-number certificate or cohomological landing
(`DeningerQuaternionicMultiplicityParity.lean`, `DeningerArtinCentralParityNoGo.lean`).
The separate Serre witness now has a literal degree-eight radical tower: its top radicand is proved
nonsquare and its normalized generator satisfies exactly
`X^8 - 205 X^6 + 13940 X^4 - 378225 X^2 + 3404025`
(`SerreQ8RootNumberNegOneTopRadicand.lean`, `SerreQ8RootNumberNegOnePolynomial.lean`). Lean now
identifies this Serre top field as Galois `Q8` and pulls the two-dimensional symplectic Artin
representation back over that literal Galois group
(`SerreQ8RootNumberNegOneGalois.lean`,
`SerreQ8RootNumberNegOneGaloisIdentification.lean`,
`SerreQ8ArtinGaloisRealization.lean`).  Its global Artin epsilon factor remains unformalized.
Thus the authenticated root-number-minus-one input, not construction of a degree-eight radical,
the `Q8` group calculation, or the representation realization, is the remaining arithmetic gate in
this terminal detour.

### O — exact restricted-Weil ground and canonical actual heads

**Architecture.** Exact restricted-Weil Friedrichs operator has ground energy `epsilon_a`.
Canonical finite Gamma--Slepian heads are extracted from true ground, converge to it, and carry
literal prime, polar, Gamma, endpoint, and completed-error blocks. Exact cancellation reduces floor
nonnegativity to sign of one coherent signed producer on actual heads.

**Proved.** Exact self-adjoint operator and true Rayleigh floor. `SuzukiTheoremOneOne.lean` now
identifies the literal interval Weil operator as the Friedrichs extension of `D† G_a D`, including
the dense form-core lift; no operator-identification gap remains. Attained nonzero ground
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
Loewner problem; this identifies the boundary geometry but does not prove its sign. The full
square-summable divisor Cauchy transform is holomorphic off the divisor, decays vertically, and is
complete: if its real part vanishes on one regular ball, the transform and every multiplicity-fibre
sum vanish (`XiCauchyTransformCompleteness.lean`). For Schwarz-fixed fibre-constant vectors, real
pairings with all safe Euler-pole Schwarz pairs are already total
(`XiEulerSafePairedCompleteness.lean`). `XiEulerSafePairedClosure.lean` defines the
closed real span of absolute-Euler quadrant pairs and now proves equality with the closed
Schwarz-fixed fibre-constant sector; in particular, orientation vector belongs to it.
`XiEulerSafePairedRationalCriterion.lean` further reduces receiver to countable dense family of
Gaussian-rational poles and proves passivity there equivalent to RH. The scalar entry is explicit:

```text
K(w,u) = 2 Re ((D(w)+conj(D(u)))/(w+conj(u)) - (D(w)+D(u))/(w+u)),
```

where `D=xiEulerLogDeriv`, and every finite packet Weil quadratic is its double sum
(`XiEulerSafePairedValueKernel.lean`). It is doubled conjugation-odd restriction of
Cauchy--Laplace observability kernel. Receiver exhaustion and value evaluation are closed; no
theorem supplies source passivity of these matrices.

Formal sources: `XiHurwitzOrientationSeparatedSourceReconstruction.lean`,
`XiHurwitzOrientationExteriorCauchyClosure.lean`,
`XiHurwitzOrientationPositivePairedSource.lean`,
`XiPositivePairedRealLoewnerSeam.lean`,
`XiCauchyTransformCompleteness.lean`, `XiEulerSafePairedCompleteness.lean`,
`XiEulerSafePairedClosure.lean`, `XiEulerSafePairedRationalCriterion.lean`,
`XiEulerSafePairedValueKernel.lean`,
`XiHurwitzOrientationSharpNonnegativeConeDistance.lean`,
`XiHurwitzOrientationBoundaryMixedIncidence.lean`.

**Open core.** Prove, from continued prime--Gamma source before selecting a divisor, PSD of every
finite matrix of explicit kernel `K` on Gaussian-rational absolute-Euler poles in one open
quadrant. Packet construction, countable exterior exhaustion, orientation membership,
positive-frequency reduction, and scalar evaluation are closed. This restricted passivity is
already equivalent to RH, so it is receiver reduction rather than producer. More diagonal budgets
cannot work: missing datum is mixed polarized incidence. Monotone quantile transport preserves
distribution but remains orientation-blind. Exact finite prime-chamber Pick inertia reads chamber
inclusion and Hamming difference, but supplies neither the completed cofinal chamber nor PSD of
Q's literal kernel.

### CLG — critical Loewner generator

**Architecture.** In centered coordinates `X(W)=xi(1/2+W)`, take twice its logarithmic derivative
and form Carathéodory kernel

```text
C_0(W,V) = (H_0(W) + conj(H_0(V))) / (W + conj(V)).
```

Finite-matrix positivity is tested only on Euler-safe half-plane `Re(W)>1/2`. A
Carathéodory--Nevanlinna--Pick extension carries positive kernel to whole right half-plane; resulting
holomorphic logarithmic derivative solves a first-order ODE and excludes zeros there.

**Proved.** `XiShiftLoewnerCriticalGenerator.lean` proves

```text
RH iff C_0 is a PSD kernel on Re(W)>1/2.
```

RH-to-PSD is translated-Xi Bezoutian after diagonal congruence. PSD-to-RH extends logarithmic
derivative and invokes zero-exclusion. `XiShiftLoewnerEulerSplit.lean` proves exact pre-divisor
source decomposition

```text
H_omega = archimedean generator
          - sum_n 2 Lambda(n)n^(-1/2-W) cosh(omega log n),
```

and finite critical PSD is exactly domination of complete prime Loewner matrix by archimedean
Loewner matrix. `XiShiftLoewnerFlow.lean` gives derivative and congruence-integral laws for shifted
Pick kernel. This literal Euler--Gamma handoff, independent of zero selection, promotes CLG to live.

**Open core and exact obstruction.** Prove critical archimedean-minus-prime kernel PSD directly
from literal Euler--Gamma source. This is source-isogenous to UEB and Q but a different
infinitesimal-shift mechanism. `not_isPSDKernel_shiftGenerator` proves **every** positive shift
`omega>0` has non-PSD generator. Therefore pointwise-positive Loewner flow from safe shifted region
is dead. Viable CLG must establish critical generator directly or introduce signed/integrated
compensation that does not assert positive shifted generators. CLG is infinite, paired, and
nonphysical; its open producer is concrete complete-prime versus archimedean matrix domination.

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
(`MaynardEndpointMobiusConcentration.lean`). `Sieve/RouteTWidthUpper.lean` proves the matching
two-regime upper bound for Route T's twist envelope and an explicit polylogarithmic envelope.
`Sieve/PrimeRangeTwistTail.lean` discharges initial-range prime polynomial and Abel steps, leaving
the scheduled comparison `envelope(blockTop) <= rho*i` at every intermediate endpoint.
`Sieve/RouteTEnvelopeRho.lean` splits this comparison exactly into contour, Perron-truncation, and
Chebyshev inequalities, and `Sieve/RouteTTailRho.lean` transfers those three real hypotheses to the
reciprocal prime-cosine tail. No arithmetic or Abel-summation premise remains inside this tail
subgate. `Sieve/RouteTTailSurrogate.lean` removes final corpus-internal width and height factors:
all three hypotheses are closed real functions of block top and frequency.
`Sieve/RouteTTailElementary.lean` removes the remaining `3i`, `2i`, square-root, and shifted
denominator forms, reducing the subgate to the three elementary schedule inequalities displayed
above. Its final theorem still takes those inequalities as hypotheses.
`Sieve/RouteTSurrogateSize.lean` supplies explicit log-height upper
budgets for the height factor and reciprocal width. `Sieve/RouteTTailBudget.lean` substitutes those
budgets into the tail capstone, leaving only three elementary inequalities in `log i` and
`log|t|`. `RouteTScheduleHats.lean`, `RouteTScheduleRegimes.lean`,
`RouteTScheduleWorstCase.lean`, `RouteTPolyMajorants.lean`, and
`RouteTThresholdLimits.lean` discharge contour and truncation on the GS schedule eventually;
`PolylogRpowDomination.lean` discharges Chebyshev and `GSTailAssembly.lean` discharges cutoff growth.
The tail is then assembled with exact surviving harmonic mass and extended over every
`|t|<=z^2`. `Sieve/MoebiusSmoothPolySaving.lean` proves the two formerly missing eventual facts,
composes all six thresholds on the integer schedule, removes every schedule premise from the
pretentious-distance conclusion, and derives the uniform smooth Möbius power saving
`C*(log z)^0.99`. `Sieve/MoebiusSeriesPolySaving.lean` transfers same saving to full Möbius
Dirichlet series at `1+1/log z`. `Sieve/MoebiusDistanceSharp.lean` supplies a complementary unconditional
all-scale bound. `SmoothAFEZetaChiLeftPowerBound.lean` proves the fixed-left-line archimedean
factor is bounded by `K*(max 1 |t|)^a`, closing that large-scale dual-contour input. None of these
theorems supplies signed short-block cancellation or estimates the depth-invariant combined
top-row/translation current.

`Sieve/RouteTMoebiusTwistAllHeights.lean` and `RouteTMoebiusTwistRate.lean` now remove the old
large-frequency/compact-height split: the four-edge Perron argument gives, uniformly for every
`|tau|<=N`,

```text
|sum_{n<=N} mu(n)n^(-i tau)|
  <= K N exp(-(log N)^(1/20)).
```

`RouteTDampedTwistAllHeights.lean` and `RouteTDampedTwistRate.lean` prove the corresponding bound
for every finite-prime damped Ramaré cofactor, with its explicit correction factor.
`SmoothAFEZetaGeneralEdge.lean` proves finite and infinite two-pole contour identities with movable
reflected edge `Re(w)=-c` and the exact Gaussian smooth AFE whenever `0<c<=1` and
`0<Re(s)<1+c`. This closes contour placement needed to put reflected Dirichlet expansion and the
controlled chi strip on one edge. `SmoothAFETruncation.lean` replaces the direct edge by a finite
Dirichlet polynomial with explicit Gaussian tail. These are long-prefix absolute bounds and exact
decompositions. At T's short window their error scale is larger than the signed block to be
controlled, and differencing two prefix inequalities loses the required joint sign. Thus new
bounds and movable-edge AFE do not close—or reformulate away—the signed short-block producer;
reflected dual-edge estimation and joint signed cancellation remain absent.

Formal sources: `XiCTaylorThetaTailCoreCurrentCapstone.lean`,
`XiCTaylorThetaTailProductFiberHermitianCollapse.lean`, `Sieve/RouteTWidthUpper.lean`,
`Sieve/PrimeRangeTwistTail.lean`, `Sieve/RouteTEnvelopeRho.lean`, `Sieve/RouteTTailRho.lean`,
`Sieve/RouteTTailSurrogate.lean`, `Sieve/RouteTTailElementary.lean`,
`Sieve/RouteTSurrogateSize.lean`, `Sieve/RouteTTailBudget.lean`,
`Sieve/RouteTScheduleHats.lean`, `Sieve/RouteTScheduleRegimes.lean`,
`Sieve/RouteTScheduleWorstCase.lean`, `Sieve/RouteTThresholdLimits.lean`,
`Sieve/GSTailAssembly.lean`, `Sieve/GSTailMass.lean`,
`Sieve/MoebiusDistanceAllFreq.lean`, `Sieve/MoebiusDistanceSharp.lean`,
`Sieve/MoebiusSmoothPolySaving.lean`, `Sieve/MoebiusSeriesPolySaving.lean`,
`SmoothAFEZetaChiLeftPowerBound.lean`, `SmoothAFEZetaGeneralEdge.lean`,
`SmoothAFETruncation.lean`.

**Open core.** Prove joint upper estimate for
`canonicalThetaTailCoreFiniteArithmeticRemainderCurrent` at same cutoff and depth as prefix selector,
retaining cancellation between top-row and translation pieces. More top-row decay is dead work:
survivor conserves exactly what row loses. Separate absolute-value bounds destroy sign.
For current Maynard specialization, this is pure short Möbius-block cancellation strong enough to
discharge joint current estimate. Its preceding GS-tail, all-frequency pretentious-distance,
smooth Möbius power-saving, fixed-left-line Xi-factor, zeta/log endpoint, and initial-range Abel
subgates are closed; same power saving also holds for full Möbius series at moving abscissa.
Scientific open core is now exactly signed short Möbius-block cancellation
preserving the joint top-row/translation current; further threshold bookkeeping or unsigned
smooth-sum bounds do not address it.

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

The Hardy--Levinson chain now supplies a second, independent path into that census.
`HardyDyadicWindowTheorem.lean` proves unconditionally that every sufficiently high dyadic window
contains a critical-line zero and gives a logarithmic lower bound for their number.
`HardySignChainCount.lean`, `LevinsonWindowAdvance.lean`, and
`PhaseAdvanceToSingletonFibre.lean` turn sign or detector-phase advance into exact odd- and
singleton-fibre lower bounds. `LevinsonWindowBound.lean` bounds all three noncritical rectangle
edges; number of zeros of the entire detector inside the rectangle is sole undetermined term.
Even a density-one singleton result would not remove finitely many off-line pairs, so HC still
requires absolute defect control, not normalized proportion.

`PrimeTraceCriticalEnergyBudget.lean` proves a complementary charge law: if a continued
prime-trace source has residues `-m_j` at finitely many distinct ordinates on one abscissa, the
unnormalized critical energy residue is at least `sum_j m_j^2`; extended-energy theorem remains
valid when divergent energy is `top`. `PrimeDiagonalSingularValues.lean` simultaneously proves the
prime diagonal grows on double-logarithmic scale, with ordinary logarithmic Dixmier normalization
zero and double-log normalization one. Hence raw energy can charge every defect but is not finite,
while natural normalization erases a fixed finite quantum. A viable HC energy producer must use a
source-derived relative subtraction or finite absolute budget that preserves integer charge;
neither theorem supplies it.

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
finite source vector is no longer a choice or abstract representative. Literal interval reflection
commutes with covariance and its Riesz inverse, exchanges the two deficiency channels, and turns the
physical Fourier minus channel at `z` into the plus channel at `-z`. Hence the phase pair is generated
by one reflected covariance--resolvent Fourier carrier (`SuzukiTaCovarianceReflection.lean`). The
coalescing even/odd covariance vectors have exact norm-square energies; positive Suzuki covariance
forces the source-faithful position-resolvent tangent nonnegative, and actual covariance realizes
the model-free coalescing tangent with no abstract operator premise
(`SuzukiTaCoalescingCovarianceTangent.lean`).
`SuzukiTheoremOneOne.lean` also closes the ambient operator identification used here: the completed
Weil operator is the Friedrichs extension of the literal Dirichlet screw operator and the source
form-domain lift is dense. This strengthens provenance but does not identify the cofinal
projective characteristic limit.

**Open core.** Prove that the canonical normal-family limit is the global Xi projective target,
not an arbitrary bounded holomorphic subsequential limit, and propagate that identification over a
finite chart containing every Xi zero. Then establish reciprocal-chart convergence and eventual
compact zero-freeness at every target pole. Aperture schedule, phase pair, projective normalization,
upper-half-plane denominator control, and local subsequential compactness are closed. The missing
step is coefficient-faithful global limit identification plus the pole chart, not construction of
real-zero approximants, phase-pair provenance, reflection compatibility, or tangent sign. The old
all-plane entire wall stays terminal and cannot be repaired by finite holomorphic exponential
gauges.

## Corpus-born candidate openings

These are Lean architectures, not literature-shaped suggestions. They are not counted as live until
source handoff is built independently of zero tested.

### UEB — unit-Euler translated Bezoutian

**Architecture.** Translate completed Xi by a real value `c`, recenter at `1/2`, and mark the
correct affine fibre by requiring unit residue after decompletion at the Euler pole. The residue
law forces `c=0`. The Hermitian logarithmic-derivative Bezoutian of that selected even order-one
entire fibre is tested on arbitrary finite packets in the open right half-plane. Global positive
semidefiniteness forces every zero of the selected fibre onto the imaginary axis and hence RH.

**Proved.** `XiUnitEulerPoleAffineSection.lean` proves residue `1-2c` and the necessity direction.
`OrderOneHadamardFactorization.lean`, `CanonicalProductE1LogDeriv.lean`,
`ImaginaryZeroBezoutianPositivity.lean`, and `XiUnitEulerPoleBezoutianSufficiency.lean` close the
converse: every even order-one entire function with imaginary divisor has positive Bezoutian, and
for every complex `c`

```text
all finite translated-Xi Bezoutian matrices are PSD
  iff every point of the value fibre xi(s)=c has Re(s)=1/2.
```

Consequently `riemannHypothesis_iff_unitResidue_and_posSemidef_bezoutian` is an exact marked
top-down RH chain. This is stronger than the previous one-way affine receiver.

**Open core.** Derive global translated-Xi Bezoutian positivity from a literal completed
prime--Gamma source law before selecting a zero or assuming criticality. The present sufficiency
proof starts from the hypothesis that the whole divisor is imaginary; using it forward would be
circular. UEB is therefore a genuine nonphysical infinite-kernel candidate, source-isogenous to
C1/Q/G but not a live producer.

### PSRC — prime-shift residue closability

**Architecture.** Continue the grade-one prime source to strip-point characters and retain its
canonical residue as a linear functional on the span of finite Euler fields and finitely many
right-strip character fields. Equip source fields with logarithmic Marcinkiewicz smallness. Finite
Euler heads are dense, while the residue vanishes on every finite-support field. RH is equivalent
to closability of this singular residue graph: under RH the functional is zero; an off-line zero
creates a source-null sequence whose residues do not tend to zero.

**Proved.** `PrimeShiftResidueClosability.lean` identifies canonical continued residue at a strip
point with minus zeta multiplicity, constructs injective residue domain and linear residue
functional, proves finite-support vanishing and Marcinkiewicz convergence of every domain element
to finite Euler heads, and closes both exact classifiers

```text
RH iff residueFunctional vanishes on residueDomain,
RH iff residueFunctional is closable in logarithmic Marcinkiewicz topology.
```

For every right-strip zeta zero it also constructs an explicit Marcinkiewicz-null prime-field tail
sequence with constant nonzero residue. Thus off-line divisor is not visible in any finite head but
appears as failure of graph closure at infinity.

**Open core.** Prove closability, or a closed-graph estimate implying it, directly from literal
continued prime source before selecting a strip zero. Present closability theorem is exactly RH,
not an upstream producer. PSRC is a genuine infinite, nonphysical, source-native candidate because
its domain, dense finite Euler core, topology, residue, and explicit failure witnesses are all
formal; it is not live until arithmetic source structure independently controls this singular
boundary functional. Its mechanism reinforces L/SEC/MSC: meaningful off-line information may live
in graph closure lost by every finite truncation, rather than in another finite positive object.

### PBM — prime-boundary monodromy escape

**Architecture.** Continue the grade-one prime-log current, read its quantized residue around a
right-strip point, and retain monodromy rather than endpoint jets. Grade--Lambert/Möbius inversion
identifies this current with von-Mangoldt source over infinitely many dilations. At a zeta zero its
residue is positive integer multiplicity. In boundary coordinate `z=log(N)(s-1)`, that charged
branch point escapes every compact chart.

**Proved.** `PrimeBoundaryMonodromyEscape.lean` proves: prime-zeta
derivative equals negative grade-one source on absolute half-plane; continued current has residue
`m>=1` at every right-strip zero; archimedean factor has zero strip monodromy; divisor charge escapes
every fixed endpoint chart; and

```text
RH iff continued prime-log current has no positive integer charge
       in 1/2 < Re(s) < 1.
```

It also proves two exact firewalls. Derivatives of entire finite cumulants have zero contour charge,
and locally uniform limits of zero-free entire finite Euler fields cannot acquire a zero inside a
protected contour. PBM therefore promotes former grade--Lambert pre-route to candidate.

**Open core.** Produce absence/cancellation of quantized monodromy from global continued
prime--Gamma source before selecting a zero. Neither Gamma completion nor any fixed compact
boundary jet can cancel charge: former has zero monodromy and latter loses branch point to
infinity. Any viable producer must be singular, non-locally-uniform, or formulated at infinity
while retaining coefficient provenance. The endpoint `no charge` statement itself is exactly RH,
so PBM is not live.

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

The operator-valued seam formulation removes both the graph-choice and exact-equality bottlenecks.
For each edge, the canonical coboundary corner is seam jump times a positive two-prime Euler Gram
entry. Its essential norm has a quantitative lower bound by the Euler-weighted seam jump, so a
compact edge coboundary forces exact endpoint coherence. On any one-ended graph, compactness on all
but finitely many edges forces the critical line; on the canonical increasing prime ray, eventual
compactness of adjacent-prime coboundaries already suffices
(`XiPrimeSeamSparseEdgeCalkin.lean`).

**Open core.** Prove from the completed prime--Gamma source, before inspecting or selecting a Xi
divisor, eventual compactness of the literal adjacent-prime seam coboundary operators along the
increasing prime ray. Graph construction, one-endedness, finite seam-value hypotheses, and an
independent finite-variation estimate are no longer open in this specialization. Compactness is the
entire missing producer; no Lean theorem derives it from source coefficients. SEC remains a genuine
infinite nonphysical candidate, not live.

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
`PrimeArchBernsteinBranchDecomposition.lean` makes non-RH singularity exact: at critical radius the
susceptibility is one explicit finite maximal-packet square-root kernel plus a remainder whose
coefficients have strictly smaller geometric rate and whose Abel series is holomorphic across that
radius. Thus branch cannot be blamed on uncontrolled infinite tail or mixed-coordinate remainder;
it is carried entirely by finite maximal diagonal packet.

**Open core.** Construct, from the continued prime--Gamma/Mobius source expression and without a
zero-free or radius premise, one analytic function on an open set containing the entire positive
collar `[z0,1)` and prove local equality with the susceptibility germ near `z0`. No Lean theorem
continues the source expression through that collar. Boundedness or summability of the purity on
all `t<1` is already RH-equivalent, so it cannot be used to manufacture the continuation. BPC is a
new candidate, not live: its singularity detector and RH endpoint are complete, but the arithmetic
continuation producer is absent.

## Formal advances that do not change route count

- `XiGlobalMeixnerShapeLandau.lean` constructs a nonnegative Gamma--Meixner shape trace and proves
  that holomorphic continuation of its safe germ to `Re(z)>0` is equivalent to RH. Its safe real
  trace is completely monotone with positive Hankel moment forms. The extension problem is now
  exact in two forms: existence of a finite completely-monotone extension to every positive shape,
  and existence of an all-positive-shape radial Hankel-PSD extension, are each equivalent to RH
  (`XiGammaShapeCompleteMonotonicity.lean`, `XiGammaShapeCompletelyMonotoneExtension.lean`,
  `HTGeometry/CompletelyMonotoneTower.lean`). Generic Dirichlet/Bernstein and atomic Hausdorff
  theorems close the safe-germ convergence and moment-uniqueness engine. This is not a new producer:
  every trace coefficient is `xiSeamDivisorCoefficient`, hence already formed from the complete Xi
  divisor. A new route still needs an equal pre-divisor prime--Gamma trace and an independent source
  extension theorem.
- `PrimeCharacterTailIndependence.lean` proves distinct complex prime characters
  `p |-> p^(-x)` are linearly independent modulo finite prime support. The key source input is
  eventual density of prime logarithms, derived from the corpus's fixed-exponent short-interval
  prime supply. `PrimeOrientationCoronaRank.lean` gives the complementary Boolean classification:
  corona rank is span rank of recurring sign patterns, anchored skeleton already forces maximal
  rank on every finite chamber, and every closed constraint between anchored skeleton and anchor
  half-space is invisible to the entire finitary differential matroid. These are strong positive
  rigidity/opacity laws. They rule out finite character palettes and finite differential rank as
  selectors for E/G/D2/AF, but provide neither completed reflection nor an RH endpoint; no route is
  added.
- `GammaWendelInequality.lean`, `GammaRatioAsymptotic.lean`, `GammaRootAsymptotic.lean`, and
  `GammaVerticalRootAsymptotic.lean` close real and vertical complex Gamma-ratio/root asymptotics
  with explicit comparison. `TrigammaVerticalLowerBound.lean` proves a quantitative vertical
  trigamma bound and the unconditional second-jet law
  `deriv gammaHardyPhaseRate t >= 1/(100t)` for `t>=4`. These strengthen archimedean curvature and
  growth inputs available to D2/HC/SV2, but do not couple them to prime cancellation or orient any
  completed source form. Working-tree `HTGeometry/GammaProductRootLaw.lean` and
  `RHTower/SelbergCuspArchimedeanRoot.lean` further prove exact finite Gamma-product root
  asymptotics and identify the Selberg archimedean root constant with its cusp parameter.
  `SelbergShiftRootLaw.lean` completes full functional-equation assembly: along degree-normalized
  shift lattice, factorially normalized value has root limsup exactly
  `conductor^(1/degree)/(2*pi*degree)` off exceptional sine lattice.
  `SelbergRankOneSineFactor.lean` makes sine hypothesis automatic for every half-rate/rank-one
  presentation by period-four recurrence and a nonvanishing sine/cosine pair. This is a new exact
  cusp--spectrum radius law for extended Selberg class, but it measures gamma/conductor data rather
  than horizontal zero location. It broadens completed-family infrastructure without specializing
  a zeta source order or creating an RH route. Current working-tree
  `ZetaChiVerticalGrowth.lean` proves only that the relevant real-Gamma factors avoid zero/poles on
  stated vertical strips and are continuous there. It does not yet prove its title's global
  polynomial chi majorant, so it closes no further contour or route premise.
- `DirichletCharacterOrthogonality.lean` closes exact finite complex-character orthogonality and
  bilinear diagonalization; `BoundedCoeffPowerSeries.lean` gives holomorphy of bounded-coefficient
  series on the unit disc; `HermitianSubmoduleTraceOrthonormal.lean` gives canonical real
  Hilbert--Schmidt coordinates in finite Hermitian submodules. These are reusable finite adapters.
  `AlternativeHypothesisLemma4.lean` computes only the removable exceptional case `n=1,t=1/2`,
  obtaining Fourier value `1/2`; it explicitly does not formalize the full parameterized lemma.
  `RHTower/DirichletLZeroCount.lean` adds unconditional order-one Jensen `O(r log r)` zero counting
  for completed nonprincipal Dirichlet L-functions. `DirichletLZeroDensityBox.lean`,
  `DirichletLZeroDensityFamily.lean`, `DirichletLZeroDensityRange.lean`, and
  `DirichletLZeroDensityPrimitive.lean` turn it into literal vertical-box counts for one character,
  one finite modulus family, every modulus through a fixed conductor cutoff, and primitive
  subfamilies. Every constant remains character/modulus/cutoff dependent: these are finite
  aggregations, not a conductor-uniform density theorem, GRH, or divisor-exclusion producer.
  Quadratic CRT/primitivity and second-moment modules close exact finite character-family
  diagonalization; `DirichletCharacterQuadraticJacobiIdentity.lean` identifies bundled squarefree
  CRT character with literal Jacobi symbol, while two-adic correlations reach exact gcd majorants.
  `DirichletCharacterFundamentalDiscriminant.lean` now proves the conductor-four and both
  conductor-eight CRT discriminants are fundamental. These remain finite-family inputs toward E/T
  correlation bounds, not conductor-uniform density or their cofinal signed cancellation.
- `PrimeLaplaceGammaJetIncidence.lean` supplies a genuine all-prime, nonphysical source interface:
  every finite raw derivative clock is jointly faithful, each finite jet observation is
  Hilbert--Schmidt, prime translation has an exact Taylor-descent anomaly equal to the omitted
  factorial tail, and adjacent resolutions satisfy a Bianchi law. The coherent factorial/Fock
  column is nevertheless unbounded at every positive shape. Thus finite Gamma jets cannot be
  silently assembled into a bounded infinite observer. No completed Xi landing or RH endpoint is
  present, so this is pre-route infrastructure adjacent to G/L/BPC rather than a candidate.
- `GradeMonodromyInversion.lean` supplies a corpus-born infinite, nonphysical source architecture.
  Locally finite Mobius grade transform and Lambert dilation transform are mutual inverses, and in
  `Re(s)>1` the literal von Mangoldt current is exactly reconstructed as the sum of grade-one prime
  source over all dilations. The inverse analytic formula is also formal:
  grade-one prime source is the Mobius-weighted sum of dilated von Mangoldt `LSeries`, with geometric
  absolute control. Prime provenance therefore survives an invertible infinite grade resolution in
  both directions. `PrimeBoundaryMonodromyEscape.lean` supplies critical-strip
  divisor landing, quantized residue, compact-chart escape, and exact RH endpoint, promoting this
  architecture to PBM. What remains absent is independent source cancellation of monodromy; finite
  entire or locally-uniform zero-free completions are formally incapable of producing it.
- Current working-tree `AllGradePrimePowerCorona.lean` defines the infinite all-prime-power
  Marcinkiewicz layer and proves exact grade-one face control: logarithmically weighted
  grade-one embedding preserves every cutoff mass, while grade-one projection is contractive.
  This is **AGC**, an all-grade, multi-channel, nonphysical pre-route adjacent to PBM/PPM rather
  than a new candidate. No declaration yet proves the nonlinear Euler ray lies in this layer, that
  higher grades form the advertised absolutely summable tail, or that its all-grade corona class
  equals the grade-one class. Without that source theorem and a completed monodromy/collision
  landing, AGC cannot inherit PBM's RH endpoint or produce PPM's collision.
- `PrimeClockEnergyDivergence.lean` proves exact all-prime clock energy diverges for every fixed
  nonzero frequency. Literal source strongly separates distinct vertical heights, but no
  finite-energy scalar clock completion can retain all primes. This sharpens E/G/AF phase
  firewall: successor must renormalize, become distributional, or retain relative mixed channels.
- `HTGeometry/CriticalTraceSpace.lean` identifies exact diagonal trace topology for
  regularized period multiplier: weight `||m||^-1` makes incidence an isometry, and any weight
  making multiplier a topological isomorphism is boundedly equivalent to it. Magnitude is absorbed
  while unimodular phase survives. This is useful topology for L/PCS/PBM boundary descent, but it
  supplies no arithmetic boundedness, monodromy cancellation, or Xi reader by itself.
  `AnalyticDividedDifference.lean` proves critically normalized translation defects are controlled
  by derivative size, converge to derivative as period shrinks, and satisfy iterated collar bounds;
  `PeriodRescalingAutomorphism.lean` shows invertible period rescaling preserves the
  Stanley--Reisner constraint ideal. These close local rescaling calculus, not global source law.
- `FacetHodgeMonomialBlock.lean` proves every surviving monomial block of a finite facet family has
  Hodge operator equal to positive facet multiplicity, and specializes this uniform gap to every
  face of the multiple-sine skeleton. `SuperPoincareSimplex.lean` and
  `RHTower/SuperPoincareApplications.lean` package simplex, CCM clock/reflection, real-corona, and
  truncated-frequency pairs as finite `N=1` or split `N=2` supertranslation sectors; the
  theta-cusp constant state is an unconditional zero-energy BPS state. These are exact paired,
  non-scalar adapters, but they are finite and contain neither completed arithmetic source
  exhaustion nor an Xi-divisor reader. They do not repair L's singular physical landing, O/G's
  whole-ground orientation, or HC's absolute charge budget, and create no new route.
- Current working-tree `HTGeometry/Sl2ElementaryFactorization.lean` proves every determinant-one
  two-by-two matrix over a field is a product of four upper/lower elementary unipotents. Hence an
  `SL_2` cocycle can be reduced to two one-parameter subgroups. This is useful projective descent
  infrastructure for U/Q/UEB/HJ, but no declaration instantiates a literal prime--Gamma cocycle or
  derives a critical-line reader; it is not a route.
- `RandomEulerObservableAbscissa.lean` proves almost-sure convergence of the Steinhaus Euler
  observable exactly for `sigma>1/2` and almost-sure divergence for `sigma<=1/2`.
  `ZetaRealSignature.lean`, `ZetaFisherMetric.lean`,
  `ZetaFisherHorizon.lean`/`ZetaFisherVariance.lean` identify same wall as sign change, Fisher
  blow-up `1/(2 sigma-1)^2`, infinite Fisher distance, and Gibbs variance of `log n`.
  `PrimeBoundaryPoissonJumpField.lean` and `PrimeSuperspaceDecompactification.lean` compute the
  symmetric prime-jump/Dickman and Wick limits: total Lévy mass diverges, scaled radial/vertical
  profiles converge, and limiting characteristic function is strictly positive—there is no real
  interference node. These are exact, infinite, nonphysical source geometries, but wall location is
  universal and no theorem couples an off-line Xi zero to their phase-free law. They are pre-routes
  and a warning against mistaking critical abscissa/metric divergence for divisor exclusion.
- `PrimeHigherMertensRate.lean`, `PrimeEndpointJet*.lean`, and
  `PrimeBoundaryWickExpansion.lean` give all algebraic endpoint-jet coefficients with exponentially
  small prime-number-theorem remainder. They close perturbative prime-boundary expansion used by
  G/MSC/PBM. PBM's escape theorem shows exact limitation: a fixed endpoint chart sees
  these jets while zero-generated monodromy runs to infinity. More jet orders cannot recover that
  charge.
- `XiSuperchargeHarnackDefect.lean` computes finite conjugation-closed Xi-packet defect as one half
  number of nonreal members and proves universal zero defect exactly RH. This is an exact divisor
  recorder formed after packet is selected, not source occurrence or producer. It does not create a
  route and cannot replace HC's upstream absolute charge estimate.
- `HalfLineExponentialGram.lean` gives exact half-line exponential Gram matrix
  `1/(lambda+mu)`, Cauchy determinant, and linear independence at distinct positive rates.
  `HalfLineExponentialDistance.lean` strengthens this to exact Gram--Schmidt squared
  distance as a finite Blaschke-product ratio; `HalfLineExponentialCoDistance.lean` gives exact
  distance of each selected exponential from span of every other rate in a finite prefix.
  `HalfLineExponentialReader.lean` and `HalfLineExponentialResidualLimit.lean` pass to closed span,
  construct unique canonical biorthogonal readers, and identify reader norm with reciprocal
  limiting co-distance. The arithmetic specialization is now exact: for physical theta rates
  `lambda_n=pi(n+1)^2`, punctured sine/sinh products give

  ```text
  ||r_n|| = sqrt(2/pi) sinh(pi(n+1)),
  <exp(-lambda_m y),r_n> = delta_mn.
  ```

  `XiThetaSquareRateReaderNorm.lean` and `XiThetaSquareRateReaderL2.lean` prove norm, canonicity, and
  fixed-index coefficient functional. Existing theta-square Hardy/causal modules provide explicit
  one-sided `L2` source and exact Laplace samples. This is **TSR**, a genuine source-side,
  infinite, nonphysical pre-route. It has no Xi-divisor landing or RH endpoint. Moreover, direct
  action on reflected theta half is zero, while reorientation duplicates positive half
  (`XiThetaSquareRateReflectedAction.lean`); scalar one-channel TSR cannot supply orientation.
  A viable successor needs a distinct completed second channel coupled coefficient-faithfully to Xi.
- `PrimeSupportFlagPathHodge.lean` gives a second non-classical pre-route. Prime-support deformation
  is a sum of rooted path-Laplacian cofactors; a one-edge cycle has the local squarefree Euler factor
  as torsion; finite squarefree Euler products are products of those torsions; and nonempty positive
  prime-power cycle torsion can vanish only at zero centered height. But every finite source
  apartment is acyclic for `Re(s)>0`. Paths carry no phase; cycles are the first phase-bearing
  object, and any RH route must construct a completed/infinite cycle or secondary class from source
  rather than infer it from finite Euler apartments. This sharpens PCS/SEC/HC design without yet
  supplying their missing Xi handoff.
- `PrimeSquareFourierStrata.lean` computes the exact unit, valuation-one, and zero Fourier strata on
  `ZMod(p^2)` and proves the critically normalized reflected coefficient is at least one, with
  equality exactly at zero radial drift. `PrimeSquareDeformedReflectionType.lean` assembles the
  local coefficients: `log beta_p(c)/log p -> |c|`, and the prime product has normalized logarithmic
  type `|c|`. `PrimeSquareSuperessentialScale.lean` proves the reciprocal Wold boundary volume is
  only polylogarithmic and negligible against that product exponent for every nonzero admissible
  drift. Thus an off-neutral drift creates a cofinal superessential signal, not merely a local
  inequality. Corpus still has no theorem identifying `c` coefficient-faithfully with
  `Re(rho)-1/2` on a completed Xi fibre, nor a completed source comparison limiting the same product
  to Wold/Gamma scale. Until that bridge exists this remains a strong pre-route adjacent to
  HC/PPM/IRK/G, not a candidate.
- The former one-way unit-Euler affine receiver is now the bidirectional UEB candidate described
  below. Genus-one factorization and imaginary-divisor Gram assembly prove Bezoutian sufficiency,
  while unit residue still selects only `c=0`. This completes receiver architecture but does not
  produce positivity; C1/Q/G source obstacles therefore remain.
- `HardyFourthMomentSignChange.lean` formalizes the fourth-moment sign-change mechanism and turns
  the three Hardy-Z moment estimates into an actual critical-line zeta zero; it also gives the
  unconditional dyadic `O(T log^4 T)` fourth moment. This proves critical-line zeros, not absence of
  off-line zeros. Separately, the Hardy-disk cyclicity chain proves exact model-space defect equal
  to finite Blaschke degree, but also a decisive blindness law: the same bounded outer carrier can
  be multiplied by an arbitrary finite inner factor while cyclicity and every power-level
  differential-adjoin field fail to determine that inserted zero data
  (`HTGeometry/HardyCyclicityGaugeBlindness.lean`,
  `HTGeometry/HardyCyclicityPowerFieldInvariance.lean`,
  `HTGeometry/HardyCyclicityOrbitFreeness.lean`).
  `HTGeometry/HardyCyclicityCarrierCapstone.lean` realizes all failures simultaneously on one
  concrete bounded outer carrier: a residual family has maximally free parabolic orbit while every
  finite Blaschke defect remains possible with the same power-field data. Hardy cyclicity or
  maximal differential-field genericity alone is therefore not a faithful Xi-divisor producer.
- `ZetaLineFirstMoment.lean` formalizes the exact oscillatory Dirichlet-polynomial integral and
  quantitative Euler--Maclaurin tail and pole-integral bounds on the critical line. It now assembles
  an exact dyadic first moment with explicit errors and, by Cauchy--Schwarz, proves an unconditional
  dyadic lower bound

  ```text
  integral_T^(2T) |HardyZ(t)|^2 dt >= T/4
  ```

  for all sufficiently large `T`. This closes advertised second-moment lower bound. It proves mass
  on critical line, not exclusion of off-line zeros, and changes no route status.
- The Bessel/difference-Galois lane is now sharply delimited. Modified-Bessel order recurrence has
  a meromorphic two-solution system, and every integer order shift lies in the rational span of the
  first two solutions. Its order derivative nevertheless lies outside the rational span of every
  finite shift family, and no rational compatible derivation exists, including the physical
  specialization `c=2/s`
  (`HTGeometry/BesselOrderMeromorphicIsomonodromy.lean`,
  `HTGeometry/BesselOrderShiftSpan.lean`, `HTGeometry/BesselOrderIsomonodromyObstruction.lean`).
  `HTGeometry/BesselOrderJetModule.lean` identifies first order-jet splitting exactly with the
  rational connection equation and proves this Bessel jet extension nonsplit.
  `HTGeometry/IsomonodromyGaugeInvariance.lean` proves rational gauge invariance, so no invertible
  rational gauge enlargement repairs obstruction.
  `HTGeometry/BesselOrderIntrinsicObstruction.lean` closes intrinsic formulation: no gauge-equivalent
  Bessel order system over `C(nu)` admits a connection. Enlarging finite shift span or changing rational
  gauge cannot recover missing differential direction. A viable successor must use non-rational or
  singular differential structure and still construct literal prime--Gamma occurrence plus Xi reader.
- `PrimeFisherSuperspaceBlindness.lean` closes scalar phase geometry as a divisor selector. For
  every unimodular completely multiplicative phase, normalized Dirichlet coherent-state Born laws,
  expectations, and Fisher variance are the same phase-free `n^(-2 sigma)/zeta(2 sigma)` data. For
  every marked point in the open critical strip, Lean constructs phase coefficients whose scalar
  meromorphic Euler projection has a prescribed simple zero there while those Hilbert/Born/Fisher
  data remain unchanged. The massless two-dimensional conformal equation is likewise independent
  of conformal scale. This terminalizes Fisher/Born/conformal scalar superspace variants of G/MSC/AF;
  a survivor must retain a phase-sensitive unbounded/distributional projection or a genuinely
  mixed channel.
- The Higgs/Goldstone/Fabri--Picasso application modules classify where zero modes and broken
  finite observations enter the arithmetic corpus. Exact Gamma--Slepian source operator has no
  invisible zero mode, whereas overcomplete finite codiagonal/source/event observers necessarily
  do. Several literal critical prime boundaries are provably outside `ell^2`, including Burnol,
  Big-Witt, theta, Suzuki-Bianchi, Xi-aperture, and Julia channels
  (`RHTower/GoldstoneFabriPicassoCorpusApplications.lean`). This supports the shared singular-boundary
  diagnosis for O/G/L/U rather than creating a symmetry-breaking route. Generic Abelian,
  non-Abelian, and quaternionic Higgs mechanisms have no completed arithmetic
  specialization or Xi endpoint.
- Generic shell/Noether, Schatten, and Stieltjes modules close reusable adapters, not RH source
  laws. Finite spectral actions are algebraic over symmetric shell coordinates, critical loci lie
  in explicit polynomial hypersurfaces, and source sublevel bounds follow from nonzero shell
  polynomials. Order-`p` spectral determinants converge inside reciprocal spectral radius and
  forget precisely lower traces; corank-one Stieltjes and multiplier-log fields coincide.
  `HTGeometry/StieltjesPowerSumRecovery.lean` derives coefficient recursion, recovers every even
  multiplier-log power sum inside Laurent-coefficient field, proves each multiplier logarithm
  algebraic over that field, and identifies their transcendence degrees.
  `HTGeometry/SchattenDetDerivative.lean` differentiates regularized determinant exponent
  term-by-term inside reciprocal spectral radius, gives exact determinant derivative, and proves
  both derivatives continuous under dominated convergence of power traces.
  `SchattenClassDeterminantIdentification.lean` identifies operator determinant and exponent with
  their spectral products from Schatten-class membership alone; the new Schatten ideal/Hölder and
  power-trace files close the finite ideal calculus. `SpectralDeterminantGraphClosure.lean` then
  closes simultaneous determinant/derivative spectral graph limits. These close determinant-fibre
  infrastructure, not arithmetic parameter selection. `HTGeometry/StieltjesCorankApplications.lean`
  proves explicit one-/two-prime cases and that zeta is not D-finite;
  `StieltjesNoPRecurrence.lean` strengthens this to non-P-recursiveness of the Stieltjes constants
  (`HTGeometry/ShellSublevelCapstone.lean`, `HTGeometry/NoetherCorpusApplications.lean`,
  `HTGeometry/SchattenSpectralDeterminant.lean`, `HTGeometry/StieltjesCorankTrdeg.lean`). None
  selects the arithmetic parameter, proves completed-source sign, or supplies cofinal control.
  `HTGeometry/JointCriticalityEvaluation.lean` identifies the abstract joint polynomial on unit
  shell with the labelled spectral-action criticality value.
  `HTGeometry/SpectralEnsembleEigenvalueBound.lean` bounds every finite Hermitian-ensemble
  eigenvalue and every joint polynomial uniformly on that shell. Sorted-spectrum continuity,
  analytic simple eigenbranches, shell-criticality domination, and a concrete ray-constant
  spectral-action phase with angular dephasing are also formal.
  `HTGeometry/SpectralActionPhaseAnalytic.lean` proves that phase real-analytic on entire
  simple-spectrum cone. `SpectralActionWitness*.lean`, `SpectralEnergyWitnessBridge.lean`,
  `SpectralActionNonconstancy.lean`, `ShellQuadraticRateWitness.lean`, and quantitative
  transversality modules now turn explicit two-point/energy witnesses into nonconstancy on every
  open patch and angular dephasing with power-law tail. `ConcreteTwoHamiltonianSpectralActionWitness.lean`
  supplies literal local two-Hamiltonian witnesses on every recursive physical qubit path, and
  `SpectralActionDephasingCapstone.lean` closes their angular oscillatory integral. These close finite domination and phase
  adapters only; they do not create an arithmetic selector or cofinal route.
- `HTGeometry/ConnesVanSuijlekomProposition21.lean` gives a literal `N=1`
  counterexample to Proposition 2.1(2) as printed: its hypotheses admit the zero kernel vector, for
  which the claimed one-monomial quotient spanning statement is false. Positive survivor is exact:
  under the Toeplitz hypotheses every nonzero real kernel vector has nonzero leading and trailing
  coefficients. Under those endpoint conditions the Laurent quotient is explicitly equivalent to
  the polynomial root quotient, carries the transported power/monomial basis, and the corrected
  clause-one generation statement holds. Source involution/star stability is preserved; source
  polynomial and its monic normalization vanish at quotient Laurent-variable class. At `N=1` the
  corpus also constructs the explicit normalized complex-linear evaluation functional, proves its
  nonnegativity on source squares, and proves uniqueness. These close the corrected finite quotient
  algebra and its smallest positive reader. Any C1/OPUC use must still add source-selected
  nonzero/nondegeneracy data and a completed cofinal landing; finite positivity does not supply the
  missing C1 producer. `ConnesVanSuijlekomTheorem31.lean` gives a fully discharged unit-interval
  rank-one convolution/eigenline/Fourier-zero instance of Theorem 3.1. It proves the analytic
  mechanism is inhabited, not that the completed Xi source realizes it.
- `HTGeometry/PrimeResiduePickInertia.lean` gives an exact finite prime-chamber analytic order:
  relative Pick defect has rank equal to chamber Hamming distance, negative index `#(J\L)`, positive
  index `#(L\J)`, and no negative direction exactly when `J subset L`.
  `HTGeometry/ImaginaryPoleBezoutianGram.lean` separately makes every imaginary-pole Bezoutian a
  rank-one Gram sum. `SchurNevanlinnaPick.lean` constructs the kernel Hilbert space and lurking
  contraction from a Pick identity; working-tree `HTGeometry/TransferFunction.lean` realizes every
  such contraction as a Schur transfer function, and `CaratheodoryNevanlinnaPick.lean` transports
  PSD Caratheodory data to a holomorphic nonnegative-real-part half-plane interpolant.
  `MatsumotoSuzukiScrewKernel.lean` proves the literal
  one-frequency screw kernel is a squared-norm Gram form. These sharpen D2/Q/HC finite receiver geometry, but contain no cofinal
  completed prime--Gamma chamber, Xi occurrence, or source orientation. They are not new routes.
- `HTGeometry/EndpointCompleteMaximalLeafExtension.lean`,
  `PhysicalEndpointCompletePathExtension.lean`, and `PhysicalLeafSpanMembership.lean` construct
  maximally projective endpoint-complete local Hamiltonian leaf extensions inside real generator
  span. `PhysicalEndpointCompletePathWitness.lean` now starts this construction from an explicit
  two-qubit graph-state edge and iterates it to physical nearest-neighbor qubit paths with state
  size `2^(n+2)` and observer size `n+2`. This proves an infinite family of finite physical
  witnesses, but supplies no arithmetic source labels, completed limit, or RH endpoint.
  Polynomial-factor limit modules close bounded-degree sample-to-coefficient passage;
  `ExpPolynomialFactorClosure.lean` gives locally uniform exponential-polynomial closure, while
  `ExpFactorPointwiseClosure.lean` needs only convergence of values and derivatives at finitely many
  nodes to recover coefficient convergence. `FiniteDeterminantGraphClosure.lean` gives simultaneous
  finite determinant and regularized-determinant graph closure.
  Cassidy `sl2` grading/regular diagonalization is now extended to matrix, toral, line-stabilizer,
  differential-solution, and constant-conjugacy classifications; constant-Galois connection,
  base/differential-constant collapse, ring-torsor coinvariance, and torsor-point separation close
  generic group carriers. Working-tree `HTGeometry/BurnsideTwoByTwo.lean` supplies the exact
  irreducible two-dimensional matrix-algebra step. `HTGeometry/DifferenceSemiInvariantSolution.lean`
  proves that a tensor-square semi-invariant line in a sigma-simple Picard--Vessiot ring forces a
  base Riccati solution, sharpening the difference-Galois obstruction to stable lines.
  `HTGeometry/TorsorSpecializationSeparation.lean` proves all algebraic torsor specializations
  jointly separate points and turns specializationwise proportionality into tensor-square
  symmetry, closing the abstract input used by that Riccati reduction. None is specialized to
  completed arithmetic source or connected to an RH reader, so they remain infrastructure rather
  than PPM/IRK/HJ/AF promotions.
- Working-tree `HTGeometry/LSeriesRightLimit.lean` proves a polynomial-growth Dirichlet series tends
  to its first coefficient along every family with real part tending to infinity, without
  controlling imaginary part. `HTGeometry/LimsupPositiveFactor.lean` proves a convergent positive
  factor scales root limsup by its limit. These close far-right normalization and root-growth
  bookkeeping used across completed-source constructions; neither supplies continuation back to
  critical strip, source positivity, or a divisor-exclusion mechanism.
- The radical-differential-ideal, reduced tensor-product, and Ritt prime-reduction files close broad
  algebraic foundations. `HTGeometry/RadicalDifferentialIdealSaturation.lean` adds
  saturation decomposition and finite-subset exhaustion of radical differential-ideal membership.
  `HTGeometry/RittBasisFinishingStep.lean`, `HTGeometry/RadicalDifferentialIdealACC.lean`, and
  `HTGeometry/RittBasisTheorem.lean` now close the one-differential-indeterminate basis theorem,
  including differential-polynomial reduction and finite radical differential generation; the
  Kolchin--Noetherian DCC consequence is formal. These are generic finiteness tools: no arithmetic
  specialization or Xi endpoint occurs, so they do not revive AF/AP or create a route.
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
  route. `CassidyAdditiveEvaluated.lean` adds the evaluated additive classification:
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
  modules, and `ParameterizedGaloisRepresentation.lean` close the parameterized Picard--Vessiot quotient,
  commuting tensor-square derivation, constant comparison matrix, full tensor torsor
  decomposition, point specialization, and faithful matrix representation over differential
  constants. `DifferenceGaloisIrreducibility.lean`, `DifferenceGaloisEndgame.lean`, and
  `DifferenceIsomonodromyEndgame.lean` now close abstract second-order endgame: absence of a base
  Riccati solution removes invariant lines; a differentially constrained scalar stabilizer makes
  Galois monoid constant after one conjugation and yields a rational connection.
  `LogDerivativeSpanDichotomy.lean` and `InnerLogDerivativeConjugation.lean` isolate mechanism:
  irreducible conjugation action forces logarithmic-derivative span either full or derivative-zero,
  and inner logarithmic derivative is removed by one conjugation.
  `BesselOrderFieldObstruction.lean` proves modified-Bessel order module has no such rational
  connection over any base field. Thus any attempted Bessel specialization must violate one of
  abstract rigidity hypotheses; connection cannot be asserted as missing bookkeeping. New
  differential-closure/Kolchin modules make ambient solution and separation steps unconditional,
  and `LinearSystemFundamentalMatrix.lean` gives every finite linear differential
  system an invertible fundamental solution over a differentially closed field, but none selects
  arithmetic system. This is a genuine non-classical
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
- `HTGeometry/DeterminantCompletionLaw.lean` now proves exact infinite-dimensional closure law:
  closure of finite-rank plain-determinant graph in Schatten-`p` topology is precisely order-`p`
  regularized determinant multiplied by exponential of an arbitrary polynomial jet of degree
  below `p` with zero constant term. Necessity, sufficiency, jet uniqueness, naturality, operator
  and multivariable pencil forms are formal. Pencil micro-block, moment realization, and
  sufficiency-law modules prove every admissible homogeneous low-trace defect can be inserted at
  arbitrarily small Schatten cost and assemble finite-rank pencils converging in Schatten norm with
  prescribed lower traces. `PencilJetFiniteDimensional.lean` closes the converse topology: every
  pointwise limit of fixed-order trace jets of finite-rank pencils remains in the finite-dimensional
  span of powers of linear forms. Cofinal finite pencils therefore neither erase the low-jet fibre
  nor create a new nonpolynomial selector.
  Consequence for C1/O/SV2/OPUC is negative as well as positive: determinant convergence does not
  canonically recover missing low traces or orientation. Those jets are genuine completion fibres,
  so an arithmetic source law must select them; generic determinant packaging cannot.
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
| Hedenmalm ordinary-`L2` pre-quasi realization | No nonzero momentum-symmetric theta-null Hilbert--Gram form on full Schwartz source can be a positive embedding of proposed pre-quasi Gelfand pair in ordinary `L2`. | Every closed successor must omit a Schwartz source direction or change realization; singular/indefinite boundary carriers remain unexcluded. |
| TSR scalar causal reflection | Canonical theta square-rate reader exists and samples every physical heat exponential exactly, but direct action on reflected theta half is zero; reorientation only duplicates positive half. | Exact infinite source-side biorthogonal reader survives. Any RH successor needs a distinct completed second channel and Xi-divisor landing. |
| weighted-Mertens half-unit tower as producer | One exponent gives one zero-free half-plane, but the full tower `0<=alpha<1/2` is exactly RH; it cannot be invoked as an upstream estimate. | Exact causal transform, one-moment transfer, and invariant half-unit prelimit deficit guide MSC/G aperture research. |
| Suzuki v2 entire characteristic wall | Displayed target has an unavoidable pole, so no all-plane locally uniform limit of entire real-zero characteristics exists; finite holomorphic exponential gauges do not remove it. | Actual entire real-zero Suzuki characteristics now exist; live SV2 uses the corrected two-chart spherical wall. |
| Deninger finite quaternionic real descent | Quaternionic anti-linear square `-1` forces even complex multiplicity, but root number `-1` forces odd central order; order-equals-multiplicity real symplectic realization is impossible. | Legacy radical field is proved degree eight, Galois, with group `Q8`. The source-authenticated Serre field is also now degree eight, Galois with group `Q8`, and carries the literal pulled-back two-dimensional symplectic Artin representation. Only its global Artin epsilon-factor calculation remains; even if supplied, it certifies the parity obstruction rather than reviving finite real descent. |
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
- pointwise-positive shifted Loewner-generator flow: every positive shift has a non-PSD generator,
  even though critical generator positivity is exactly RH;
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
- bounded coherent infinite observation obtained by stacking all finite factorially normalized
  prime-Laplace Gamma jets: every finite row is Hilbert--Schmidt but the Fock column norms are
  unbounded;
- finite entire prime-boundary cumulants or locally uniform limits of zero-free entire Euler
  fields as carriers of divisor monodromy: former have zero charge and latter cannot acquire a
  protected zero;
- canonical recovery of low trace jets from Schatten determinant convergence: determinant graph
  closure contains every admissible lower polynomial completion jet;
- finite prime-support path/apartment Hodge theory as a right-half divisor detector: paths are
  phase-blind and every finite positive prime apartment is acyclic there; a completed cycle or
  secondary class is indispensable;
- Hardy cyclicity, model-space codimension, or the differential field generated by all power-level
  observations as a faithful zero selector: arbitrary finite Blaschke inner gauges change the zero
  defect while leaving the outer carrier and power-field data admissible;
- Born probabilities, expectations, Fisher variance, or two-dimensional massless conformal
  geometry as phase-sensitive zero selectors: they remain unchanged while a scalar meromorphic
  Euler projection acquires a prescribed off-line zero;
- symmetric random-Euler/Poisson/Wick critical-wall laws as zero selectors: they locate universal
  half-line convergence or Fisher wall, while symmetric limiting characteristic function has no
  real interference zero and carries no Xi-divisor landing;
- rational isomonodromic derivation of the modified-Bessel order recurrence: every finite shift
  family remains in the same rank-two rational span, while the order derivative lies outside every
  such span, first jet extension is nonsplit exactly because rational connection equation has no
  solution, and obstruction survives every invertible rational gauge, including physical
  positive-argument specialization;
- positive ordinary-`L2` Hedenmalm pre-quasi realization on full Schwartz source: source escape is
  unavoidable, so singular/indefinite completion or a smaller source is required;
- finite-energy completion of exact scalar all-prime clock at any nonzero frequency: its source
  energy diverges;
- eventual cancellation by a finite palette of distinct prime characters: tail independence forces
  every coefficient to vanish;
- recovery of a global closed Boolean prime-orientation constraint from finite corona rank or its
  differential shift matroid: anchored constraint opacity makes all such finitary data identical
  across a whole interval of different constraints;
- a second orientation variable from scalar causal theta square-rate reflection: reflected action
  is zero, while reorientation repeats the positive source datum;
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
relative, graph-valued, nonlocal, multi-chart, or non-scalar. L's bounded first jet now shows
completion is possible locally, but arbitrary multiplicity closure and physical descent remain
distinct global gates.

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

UEB, CLG, PSRC, PBM, MSC, SV2, PCS, SEC, and BPC form a second non-classical family: infinite paired/operator/graph or
analytic source followed by a singular, meromorphic, or homological boundary landing. MSC has the carrier but lacks pointed
divisor covariance. UEB has exact affine marking and a complete order-one Bezoutian classifier but
lacks source-produced kernel positivity. CLG turns the same logarithmic-derivative geometry into a
critical Carathéodory generator with literal arch-minus-prime split, while proving positive-shift
flow impossible. PSRC has exact continued prime residue and dense finite Euler core, but closability
of its singular graph is already exactly RH. PBM retains quantized monodromy at infinity and proves
finite/local completion cannot carry it; absence of that charge is again exactly RH. SV2 now has actual entire real-zero characteristics, a canonical paired
projective family, and local cofinal compactness; it lacks global target identification and the
reciprocal pole chart. PCS has an exact all-prime graph, spectral gap, and divisor boundary
complex but lacks a secondary class capable of seeing homology whose ordinary index is zero. SEC
has an exact end-coherence collapse and a canonical prime-ray Calkin endpoint, but lacks a source
law making the adjacent seam coboundaries eventually compact. BPC
has the exact positive susceptibility singularity and collar-to-RH transfer but lacks source
continuation through that collar. None can be reduced to one finite positive object or one scalar
response without hitting a proved
firewall.

Remaining pre-routes reinforce that taxonomy rather than extend route count. Prime-Laplace
Gamma jets are an infinite paired clock with exact translation anomaly/Bianchi curvature, but the
coherent observer is unbounded. Prime-support Hodge theory says phase begins at cycles rather than
paths and finite positive-prime apartments are acyclic. Prime-square Fourier strata now give a
cofinal two-level reflection law with exact type `|c|`; its exponential drift signal dominates the
polylogarithmic Wold boundary scale. Grade--Lambert monodromy inversion has now crossed into PBM's
critical-strip quantized residue, but still lacks independent zero-charge production. AGC adds an
infinite all-grade coefficient topology with an exact grade-one retract, but not yet the nonlinear
Euler-ray tail or a completed landing. Half-line exponential Gram/distance identities supply exact Cauchy
geometry and now specialize to canonical `L2` readers for literal theta square rates. TSR therefore
has arithmetic source occurrence, but causal reflection supplies no second orientation and no Xi
divisor landing exists. Finite prime-chamber Pick inertia exactly converts chamber inclusion and
Hamming difference into analytic signature, but lacks any cofinal completed chamber law. These
mechanisms are genuinely corpus-born and non-classical;
what they lack is not an abstract endpoint but a source-derived completed/infinite assembly carrying
their invariant into an Xi-divisor exclusion. Fisher-superspace blindness supplies the matching
warning: phase-free Hilbert information can remain identical while the unbounded scalar Euler
projection changes its zero divisor. The
Gamma--Meixner Landau trace lies at the opposite end: its global endpoint is exact, but its
coefficients are divisor-built. A viable new architecture could emerge only by joining one of the
source pre-routes to such a complete receiver without importing the divisor in the join.

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
   Möbius object (CCM-FU, D2, E, Q, CLG, T).
2. **Ground-relative coercivity:** control exact state selected by full operator, not one seed or
   generic packet (C1, O, G, U).
3. **Singular boundary descent:** physical comparison across completion boundary without losing
   coefficient, multiplicity, or orientation (G, L, P, U).
4. **Mixed-incidence control:** preserve cross terms diagonal energies erase (E, Q, HC, T).
5. **Cofinal synchronization:** one estimate uniform in moving degree/aperture/height
   (CCM-FU, E, O, T, U, SV2).
6. **Source-native internal dynamics:** projective module, corrected Stokes category, monodromy, or
   analytic continuation on the literal completed source
   on actual arithmetic carrier before divisor selection (UEB, PSRC, PBM, AGC, SC, PPM, IRK,
   OPUC, HJ, BW, MSC, PCS, SEC, BPC).
   Abstract Weyl existence, Arakelov power pullback, all-plane entire Suzuki convergence, and finite
   real quaternionic descent are classified terminal in their stated architectures.

Fundamental remaining obstruction is not another equivalent criterion. Corpus already has many. It
is:

> derive favorable global order or discrete rigidity from literal completed source while retaining
> orientation and mixed incidence erased by scalarization, finite truncation, and post-divisor
> fitting.

## Highest-value questions exposed by Lean

1. Can the literal moving-triangular Guinand--Weil prime-minus-polar window remain uniformly
   bounded without zero-free input?
2. Can positive-frequency prime--arch trace be controlled by a reflected signed/non-dominating
   source law after canonical directed passivity and raw-positive completion have failed?
3. What exact squarefree relation realizes Ramaré incidence with unit all-interval Hall load and
   co-moving flux?
4. What independent nonlinear/distinct-channel source law forces already-transported Ward
   coefficient to vanish or acquire favorable wall order?
5. Can Burnol's now-bounded literal first Mellin jet be extended to every required multiplicity jet
   and completed Sonine closure, and can resulting all-prime Green restriction have common kernel
   exactly arithmetic boundary with target equal to existing physical landing?
6. Is completed CCM symbol nonnegative on every canonical actual-head density?
7. What pre-divisor completed-source law forces moderation of the literal second-Cartier endpoint,
   despite the proved post-selected finite-measure and scalar-short firewalls?
8. Why are finite matrices of the explicit Euler-safe paired value kernel PSD on all
   Gaussian-rational poles in one absolute-Euler quadrant, from source before divisor selection?
9. What signed short Möbius-block estimate controls the depth-invariant top-row/translation
   remainder without splitting cancellation, now that every GS schedule premise, all-frequency
   distance bound, and smooth Möbius power-saving subgate is closed?
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
17. What completed prime--Gamma source theorem makes the literal adjacent-prime FE--Schwarz seam
    coboundaries eventually compact in the Calkin algebra along the canonical increasing prime ray?
18. Can the continued prime--Gamma/Mobius expression be analytically continued through the full
    Bernstein susceptibility collar without importing a zero-free region or an equivalent radius
    bound?
19. Can the finite prime-Laplace Gamma-clock Bianchi system be completed in a graph/domain topology
    that controls its provably unbounded Fock column and lands coefficient-faithfully in an Xi
    receiver?
20. What completed or infinite prime-support cycle/secondary class survives the proved acyclicity
    of every finite positive-prime apartment and couples its Euler torsion to the Xi divisor before
    choosing a zero?
21. Is there a pre-divisor prime--Gamma trace equal to the safe Gamma--Meixner shape germ, with a
    continuation law stronger than the divisor-built Landau criterion rather than another exact RH
    restatement?
22. Can the cofinal prime-square reflection product be identified on every Xi fibre with
   `c=Re(rho)-1/2` and simultaneously bounded by the proved Wold/Gamma scale from the literal
   completed source, so its superessential type forces `c=0`?
23. What singular infinity-sensitive source law cancels or excludes PBM's quantized continued
   prime-current monodromy before a divisor is selected, given that charge escapes every fixed
   endpoint chart and cannot arise from locally uniform zero-free finite fields?
24. Can theta square-rate readers acquire a genuinely distinct completed second channel and a
   coefficient-faithful Xi landing, despite exact zero/duplication of scalar causal reflection?
25. What literal completed prime--Gamma identity makes every finite translated-Xi Bezoutian matrix
   positive after unit-Euler residue selects `c=0`, without assuming the imaginary-divisor
   conclusion that the Bezoutian theorem is meant to prove?
26. What source estimate makes the canonical prime-shift residue functional closable in logarithmic
   Marcinkiewicz topology, without assuming its equivalent conclusion that every right-strip zeta
   multiplicity vanishes?
27. Why is the literal critical archimedean Loewner matrix greater than or equal to complete prime
   Loewner matrix on every finite Euler-safe node packet, given that every positive-shift generator
   is formally non-PSD and therefore cannot supply a positive interpolation path?
28. Does the nonlinear all-grade Euler ray differ from its grade-one face by a uniformly
   summable prime-power tail in the proved Marcinkiewicz topology, and if so can that completed
   all-grade class carry a source-native law excluding PBM monodromy or forcing PPM collision?

Until one is answered, endpoint reformulations, finite real-zero models, seed asymptotics, diagonal
moment inequalities, or scalar transport identities do not move formal RH frontier.
