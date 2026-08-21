# Current Formal Frontier Toward Proving or Disproving the Riemann Hypothesis

## Scope, evidence, and status language

This document states where the `HTGeometry`, `HilbertMetric`, and `RHTower` Lean corpus stands now.
It maps architectures, theorem chains, open cores, and terminal mechanisms. It is not a chronology,
work log, literature survey, or inventory of every RH-equivalent proposition.

**Formal-corpus cutoff:** 21 August 2026, commit
`d321799f4d0937747b68eedf626f2b90ac6a8193`, plus declaration-index review of current Lean
working-tree additions. Scientific status below comes only from Lean declarations, dependencies,
theorem docstrings, and explicit gap/no-go markers. Pipeline cards and papers are not evidence for
this map. Working-tree declarations are identified and not claimed build-audited in this
documentation-only pass. Any transient working file still containing `sorry`, `admit`, or an
equivalent placeholder is excluded from proved evidence and route counts.

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

Formal corpus currently supports sixteen named live producer architectures, distinguished by their
first source premise rather than by pairwise-independent receivers:
`CCM-FU, C1, D2, E, F2, G, L, O, P, Q, CLG/TTF, T1, T2, U, HC`, and
**SV2 (Suzuki spherical characteristic convergence)**. CLG and TTF are now one architecture, not
two: Lean proves their finite-packet order problems equivalent by an invertible Xi diagonal
rescaling. Conversely, the name Route T now covers two independent source mechanisms, recorded
here as `T1` (Xi-Taylor transfer current) and `T2` (Wold--mesh residual continuation). Thirteen corpus-born receiver/source-mechanism
candidates remain: `UEB, PSRC, PBM, SC, PPM, IRK, OPUC, HJ, BW, MSC, PCS, SEC, BPC`. Routes R, IW, and AP are terminal as independent
producers. Current formal corpus closes important intermediate premises, but does not close any route's
final open producer and proves neither RH nor its negation.

| Architecture | Proved chain | First open core |
|---|---|---|
| CCM-FU | completed Guinand--Weil third-grade source -> literal triangular prime-minus-polar window -> exact positive-kernel anchored moment -> Xi-screw Green -> RH | For one fixed `b>0`, uniformly bound the explicit triangular source window, equivalently `int_b^H (96-64h/H)h^-4 (E(b)-E(h)) dh`; this is exactly the former linear-Cesaro gate. |
| C1 | corrected theta/prime--Gamma source -> Weil/Connes form or real spectral realization -> RH | Construct a source-derived non-dominating or signed correction which excludes the now-explicit admissible cofinal two-pole antisymmetric escape before final positivity; raw positive/passive Stokes completion is impossible. |
| D2 | continued prime--arch trace -> one-sided anti-Herglotz/finite ceiling -> RH | Source control of sole positive-frequency tail by a reflected signed/non-dominating law; canonical directed passive limits are impossible. |
| E | squarefree Wold source -> two-sign half-power marker supply -> exact integer-pair incidence -> unit-load Hall transport with moving flux -> RH | Build one Ramaré-supported relation joining proved marker supply to relation-specific subinterval Hall, unit load, co-moving flux, and Gibbs cost. |
| F2 | all-prime principal-relative Sonin residual -> positive trace-class energy -> one intrinsic Hankel moment curve -> continued prime--Gamma moment germ -> RH | Prove one source-derived cofinal aperture section, positive aperture barycenter, or equivalent all-moment weld from the Sonin energy moments to the fixed prime--Gamma moments. |
| G | Suzuki/Mobius/Gamma source -> marked pre-scalar or signed-channel carrier -> exact Ward landing -> wall orientation -> RH | Independent source law forcing the already-transported Ward coefficient to vanish or have the required signed order; Schur coisometry and causal limit do not supply four-unit orientation. |
| L | completed Green/BV/co-Poisson source -> strict resolved Xi boundary with prime/depth/multiplicity provenance -> singular source-to-physical comparison -> coefficient-faithful Burnol/Deninger reader -> RH | Construct one source-derived singular comparison, before divisor specialization, which sends the already resolved boundary to the existing physical landing and makes its physical reader annihilate that boundary. The comparison must preserve the nonzero Xi coefficient and cannot assume the conormal defect vanishes. |
| O | exact restricted-Weil operator -> canonical true-ground heads -> coherent signed producer -> nonnegative floor -> RH | Sign of cancellation-preserving coherent finite-head producer, equivalently eventual reverse-prime control on canonical actual heads. |
| P | source-horizontal second-Cartier orbit -> Route-N capacity/radial-work bridge -> radial Krein energy -> endpoint moderation -> RH | Produce endpoint order globally before divisor selection; regular reflection-pair extraction, finite circle measure, and literal scalar short are formally ruled out. |
| Q | continued Hurwitz/Cauchy source -> countable Gaussian-rational Euler-pole paired kernel -> orientation zero -> RH | Prove source nonnegativity of the explicit exterior paired diagonal, equivalently passivity of every finite paired-value matrix. Lean proves this scalar collapse only through Xi-specific RH capstones, so it is a smaller receiver, not a source proof. |
| CLG/TTF | literal completed theta source -> neutral correlation flux = Xi Bezoutian -> invertible diagonal congruence -> Euler-safe observability deficit = reflection-even minus reflection-odd two-channel Weil energy -> RH | Exclude, directly from the completed source, every admissible cofinal regular two-pole Cauchy sequence with reflection-even energy tending to zero and reflection-odd energy tending to its positive fibre multiplicity. This moving rank-two no-escape law is exact: any off-line fibre produces source energy tending to the negative multiplicity. |
| T1 | finite Xi-Taylor/theta-tail source -> exact reflection bridge -> zero-free full-density channel plus canonical transfer current -> raw core-current bound -> RH | Produce a source-first sublinear bound for the canonical full-density transfer current, concretely by signed short Möbius-block cancellation preserving the combined top-row/finite-translation current. The full normalized Xi zero packet and zero-free aggregate channel are discharged; transfer-current sublinearity is exactly RH. |
| T2 | ordered-prime Wold source -> centered log holonomy -> Wold-minus-log-mesh residual Hardy kernel -> continued prime-zeta/mesh ODE -> RH | Prove one uniform logarithmic scalar tail envelope for the fixed Heath--Brown source aggregate and aggregate the resulting literal large packets over gap shells to obtain critical gap energy; then prove signed/renormalized continuation from `Im z<0` to `Im z<1/2`. Absolute critical graph norm is impossible. |
| U | shifted hard-edge source -> cofinal shifted Hankel tail or first-contact exclusion -> RH | Non-scalar source mechanism excluding the exact nonintegrable strict-frontier quotient, or uniform cofinal tail order. |
| HC | two-prime/Cayley/Gauss--Hodge source -> quantized horizontal collision charge -> strict sub-two or prime-summability law -> RH | Absolute subquantum estimate, source-first prime-summability, or a conductor-uniform bound for the literal not-all-equal weighted six-label cubic correlation after exact diagonal cancellation and affine reduced-residue Poisson summation, with large-height aggregation strong enough for an absolute detector census. |
| SV2 | literal Suzuki energy space -> paired self-adjoint characteristics -> bounded projective normal family -> global Xi projective target -> corrected two-chart spherical limit -> RH | Identify the canonical cofinal subsequential limit with the divisor-faithful global target, then extend convergence over the full finite chart and reciprocal pole chart. |

Among current architectures, live `CLG/TTF` proves
that the critical logarithmic-derivative Loewner kernel is PSD exactly under RH, splits it on the
Euler region into an archimedean kernel minus the complete von-Mangoldt phase kernel, and proves
every positively shifted generator is non-PSD. Its Euler-safe observability model is fully formed:
the positive density, packet amplitude, tail amplitude, and deficit have convergent integrals; the
deficit is offset-independent and equals `pi` times critical kernel energy. Its viable premise is
the resulting source observability inequality, not a positive Loewner flow through shifted
generators. Candidate `PBM` identifies the continued
grade-one prime current's quantized residue at every right-strip zero, proves this charge escapes
every fixed endpoint chart, and makes absence of charge exactly RH. Entire cumulants and locally
uniform limits of zero-free finite Euler fields cannot create that charge. PBM therefore requires a
singular infinity-sensitive zero-charge law, not finite completion.

Route E now has unconditional unsigned cofactor supply outside its prescribed polylogarithmic prime
band, exact two-range Ramaré/rough partitions, and reciprocal-decay Halász--Montgomery row mass of
shape `N log T + |E| sqrt(T) log T`, removing the former `N|E|` loss. Its averaged mean-square gate
still reduces to one relative head bound. The chosen low/high ladders are now proved to cover their
ranges, stay inside their intended tops, have nonempty high cofactor blocks, and incur only
`beta log log x` low-range harmonic mass. T1 has all-height twisted Mertens
and damped Ramaré-cofactor bounds, a movable-edge smooth AFE, and a whole-vertical-line polynomial
majorant for the chi factor. Its two-range system has the actual high-block pointwise bound and
separate normalized vanishing laws for the small-ladder, defect, and rough budget groups, although
their final substitution into the full window inequality is not assembled. The exact multiplicity
Xi Mellin zero series is absolutely summable and the entire normalized common detector packet tends
to zero. The zero-free full-density theta channel contributes only bounded normalized current; all
RH content is concentrated in one canonical transfer current, whose sublinearity is exactly RH.
These results do not supply E's fixed relation or T1's signed short-block producer. Hardy's theorem is formal in
dyadic-window and logarithmic-count form. Levinson's critical-edge hypothesis is now eliminated,
all other edges are bounded, and admissible heights are chosen unconditionally; detector zero count
is the sole remaining term in that branch. HC therefore gains a sharper source-to-census interface
but no absolute off-line upper bound. Prime-trace energy now charges a
finite off-line ordinate packet by at least its squared multiplicity, while prime-diagonal energy
has natural double-logarithmic divergence. Without a relative subtraction or absolute finite upper
budget, this is not HC's producer. Random Euler, Fisher, prime-boundary Poisson/Wick, determinant
completion, difference-Galois, and finite-conductor Dirichlet additions are classified below as
pre-route infrastructure or firewalls.

The corpus also exposes live successor **F2**, distinct from retired Route F. The actual weighted
all-prime Sonin residual is Hilbert--Schmidt; its positive trace-class energy has nonnegative
trace--Hankel tests governed by one moment sequence. A single cofinal aperture sequence matching
that sequence to every fixed continued prime--Gamma moment, or a positive aperture barycenter with
those moments, formally implies RH. New semilocal modules now construct an actual finite cyclic
trace-class prime-power source, complete its trace to the continued prime--archimedean germ, and
identify all resulting centered moments with the Xi reciprocal moments. Independently they
construct a source-free positive trace-class prolate boundary-leakage carrier and identify its trace
with prolate impurity. No theorem identifies either completed trace family with the positive
all-prime Sonin moment curve. F2's frontier is this source-to-source all-moment weld, not another
bounded compact correction, one scalar trace identity, or post-divisor spectral model.

Live **CLG/TTF** now has two exactly equivalent source presentations.
`ThetaCuspTiltFluxSourceWeld.lean` constructs the literal completed theta source and identifies its
bilateral Laplace transform with `xiCent` on all of `C`.
`ThetaCuspTiltFluxObservabilityWeld.lean` proves that coefficient multiplication by the nonzero
factor `xiCent(w_j)` carries every theta-source Bezoutian packet exactly to the Euler-safe deficit,
up to the positive factor `pi`, and proves universal positivity equivalent in both directions.
`ThetaCuspTiltFluxHedenmalmWeld.lean` further identifies every scalar theta flux with the zero-safe
Hedenmalm transverse current and proves rank-one nonnegativity throughout `Re w>=1/2`. Thus only
cross-node coherence carries RH. `ThetaCuspTiltFluxWeilParityWeld.lean` gives its
exact operator meaning: theta flux is total reflection-even two-channel Weil energy minus total
reflection-odd energy, and universal domination is exactly RH.
`ThetaCuspTiltFluxWeilParityEulerRayWeld.lean` then proves the full complex-coefficient two-mode
law on any two ordered positive Euler-ray nodes. The later Cauchy-localization theorem supersedes
that coarse residual classification: positivity on the regular two-pole Cauchy family alone is
already exactly RH. Every off-line fibre produces moving regular poles whose even energy tends to
zero, odd energy tends to exact positive reflected-fibre multiplicity `N`, and actual continued
prime--archimedean rank-two source energy tends to `-N`. The poles can be chosen in the full
continued source domain while avoiding every collision. The open core is therefore one precise
source no-escape theorem for these cofinal reflection-antisymmetric rank-two packets, not generic
positivity on an unspecified high-dimensional packet class. This is a narrowing inside CLG/TTF and
C1/Q's shared Cauchy interface, not a new independent route. Nor does generic
source shape supply a global right-half-plane order theorem: `ThetaSourceStrictLogConcavityFluxNoGo.lean` constructs a positive,
even, faster-than-every-exponential, globally strictly log-concave source with negative one-mode
flux in the open right half-plane.

The Schwarz-pair crossing calculations further separate signal from selector. A canonical paired
fibre is exactly Weil-isotropic, with equal positive even and odd energies. Its tangential
first-crossing coefficient is strictly negative at every Xi divisor, including critical-line
divisors, so tangential crossing or its vanishing is terminal as an RH mechanism. The complementary
source-normal coefficient is the multiplicity-scaled reflected-source entropy, vanishes exactly on
the critical line, and satisfies an exact Lorentz/Pythagorean conservation law with the tangential
rate. This identifies the surviving RH-bearing coordinate but does not produce its vanishing.

The corpus also exposes live **T2**, distinct from the Xi-Taylor branch now called T1. Its ordered
prime Wold current has an unconditional holomorphic residual Hardy kernel on `Im z<0`, an exact
prime-zeta-minus-log-mesh-minus-holonomy normal form, and a continued residual carrying the full
integer multiplicity at every right-strip zero once critical prime-gap energy is available. An ODE
uniqueness theorem makes critical gap energy plus continuation to `Im z<1/2` imply RH. The newest
normal form writes every residual increment as a normalized consecutive Chebyshev-error increment
minus two nonnegative depletions, one trace class and one absorbed by critical gap energy. Lean also
proves that the tempting two-sided absolute critical graph norm is empty. T2 therefore requires a
signed or renormalized subhalf continuation, not absolute boundary variation. The latest source
bridge turns each dyadic consecutive-prime gap-square shell into at most eight times its reserved
width times the literal measure of prime-free short-interval bases in the same physical block.
A second theorem makes the target width proportional to physical base exactly as required by the
already formal fixed-ambient Maynard spatial `L2` packet. Critical gap energy is consequently
reduced to a uniform weighted multiscale composition of two existing source interfaces. New
fixed-source packet theorems work at every fixed Mellin order, turn a proportional prime-free
interval into one literal large finite packet, and collapse every stopped-ladder tail obligation to
one logarithmic scalar envelope. Corpus still does not prove that envelope uniformly for the actual
Heath--Brown aggregate or aggregate the resulting packet lower bounds over physical blocks and gap
shells at critical weight.
**W2C**, the
two-channel Weil resolvent/aperture bridge, proves that CLG's critical logarithmic-derivative kernel
is exactly the sum of canonical even and odd Weil Gram channels, realizes both as truncated
two-sided exponential Fourier sources, transports every negative exact packet to all sufficiently
large finite apertures, and makes nonnegativity at every finite aperture exactly RH.
`XiBezoutianPointedIncidence.lean` trace-clears same kernel to an entire pointed Bezoutian and makes
a source-defined Hilbert Gram factorization the precise sufficient handoff. Because current
finite-aperture form is still the actual Xi-divisor polarization, W2C is a complete receiver and
index-faithful bridge among UEB, CLG, Q, O, and SV2, not an independent producer. The all-grade
prime-power corona is now a **terminal selector in its stated Marcinkiewicz topology**, not an open
pre-route: higher nonlinear Euler grades and higher tangent grades have uniformly bounded mass and
vanish in the quotient, so the all-grade critical class retracts to grade one; positive off-line
shift rays still vanish. `XiEulerSafeCauchyLoss.lean` gives CLG an exact safe-to-critical
factorization and proves its missing condition is genuinely multi-node. Prime-log action
condensation and the Euler-position commutator expose two new infinite, paired, nonphysical
pre-route mechanisms retaining squarefree coefficients, multiplicity residues, and polarized
leakage; neither supplies an independent zero-charge/order law. Universal BPS and Super-Poincare
packages now include concrete projection-phase, Deninger-cochain, and arithmetic `Q8` odd-Clifford
realizations, but do not force saturation. A bare reciprocal-Xi Clifford split is itself exactly RH.
**MEG**, the multiple-elliptic-Gamma coset difference system, has faithful translate labels,
all-proper-face joint independence, an exact two-survivor phase boundary, and a complete all-depth
normal form. Pair-face signatures are complete modulo differential algebraicity; their exact image
is every compatible family of finite class divisors, and one universal multiple-elliptic-Gamma
carrier with translated jets realizes every admissible finite bottom divisor. It still lacks a
completed arithmetic source specialization, functional-equation action, and Xi reader, so remains a
pre-route. **ZGC**, the abelian zeta-gas chirality mechanism, is a second genuine source pre-route:
the convergent all-mode class law has strict directed KL chirality, and an involution exchanging two
formation laws forces equal chemical potentials. No theorem extends that law through completion or
identifies functional-equation reflection with the required class-law involution on an Xi receiver.
**SFP**, split-formation parallax, is a separate nonphysical multi-channel pre-route: exact recovery
maps generate a hidden residual, a resolving family reads it as positive parallax work, bounded
repeated work selects the neutral residual kernel, and a fusion-frame lower bound controls squared
distance to that kernel. In its Poisson model, total Jeffreys work splits exactly into visible
Boolean occupancy and nonnegative hidden-history work; occupancy saturates while hidden history
remains extensive and vanishes only for equal rates. The reflected-prime reserve has sharp scale
`t log(p) p^(-2(1-t))` and is summable over all primes exactly for `t<1/2`; without an Xi reader this
half-aperture transition is not RH. SFP has no completed arithmetic formation, reflection action,
or Xi reader.
`SL_2` cocycle rigidity likewise rules out regular one-entry cocycle shortcuts. No open producer is
closed; RH status is unchanged.

Route-wide position is now sharper. E retains one source-fixed signed relation theorem; its unsigned
exceptional-measure machinery is closed. T1 retains signed short Möbius cancellation for the joint
top-row/translation current. T2 retains one uniform logarithmic envelope for the actual fixed
source, critical-weight packet aggregation, and signed subhalf residual continuation; its absolute
critical graph-norm replacement is dead. HC has complete finite CGL zero alternative,
common-prefix fibres, exact cubic diagonal cancellation, affine reduced-residue Poisson mechanics,
and finite contours, but still needs a large-height conductor-uniform estimate of the remaining
not-all-equal weighted correlation strong enough for an absolute census. F2 has
literal positive and completed trace carriers but no all-power moment weld, and passive Euler polar
corrections cannot compactify the seam. O retains canonical actual-head sign or a controlled exterior
gauge correction. Q retains sign of its assembled Gauss-minus-error current. L retains singular
arithmetic-to-physical specialization. CLG/TTF retains cofinal source no-escape for the exact moving
two-pole antisymmetric sequence forced by every off-line fibre. The
remaining live routes and all thirteen candidates retain the named open cores below; receiver
identifications, source detectors, and RH-equivalent selectors do not supply those producers.

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
`ThetaCuspTiltFluxWeilParityCauchyLocalization.lean` and
`ThetaCuspTiltFluxWeilParityCauchySourceEscape.lean` now identify the exact negative direction that
any corrected C1 carrier must remove. Every off-line conjugate fibre admits collision-free moving
two-pole packets in the full continued source domain with

```text
(even energy, odd energy, continued source energy) -> (0, N, -N),  N>0.
```

The source energy is eventually strictly negative. Thus full-space density is no longer the
scientific issue: a cofinal rank-two reflection-antisymmetric escape already exhausts the RH
obstruction. This does not itself construct a corrected carrier.
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

**Open core.** Derive from fixed theta/prime--Gamma source, before divisor selection, a correction
which excludes every admissible moving two-pole antisymmetric escape, by one of:

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

The Matomäki--Teräväinen adapter is now closed through its complete finite schedule.
`Sieve/MatomakiTeravainenRaisedLemma41Energy.lean` removes the fixed pointwise coefficient ceiling:
raw convolution energy `<= Q A^ell` gives the weighted block mass, and Huxley's cubic term accepts
subpower `Q` under `Q^3<=T^(eps^2)`. `MatomakiTeravainenPowerWindowSchedule.lean` bounds the raising
degree solely from the literal Type-II lower length `T^mu<=M`;
`MatomakiTeravainenCoefficientEnergySchedule.lean` turns every divisor-bounded convolution power
below that fixed cap into the required subpower coefficient-energy budget; and
`MatomakiTeravainenAmplitudeStrip.lean` derives the active amplitude-strip inequalities from the
literal `T2` branch conditions. The scheduled actual-cell theorem therefore no longer lacks an
uncontrolled coefficient norm, raising degree, or amplitude selector. These are finite unsigned
large-value adapters. They do not define E's physical relation, prove relation-specific Hall, or
produce co-moving signed flux, so E's open core is unchanged.

The joint-omega sieve layer is also substantially more complete. Lean now has exact two-range
factorization of the joint weighted polynomial, coefficient-variance and Gallagher spectral
reductions, the omega-ladder budget, and the Section-4 disc/annulus, exceptional-cofactor, Q-side,
and master assemblies. Their capstones correctly retain the normalized joint-budget, short-block,
annular saving, cofactor-mean, and defect estimates as hypotheses
(`Sieve/JointOmegaFactorisation.lean`, `Sieve/JointOmegaSpectral.lean`,
`Sieve/JointOmegaBudgetFromLadder.lean`, `Sieve/Section4Master.lean`). Thus the analytic accounting
needed after a relation is supplied is formal. The divisor repair replaces the fatal
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
and Abel summation against T1's envelope. `Sieve/RouteTEnvelopeRho.lean` and
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
and relative-threshold moment loss. `RamarePartitionedLadder.lean` and
`RamareAnnulusPartitioned.lean` assemble the three-piece disc/annulus/exceptional partition;
`RamareAffinePartitioned.lean` packages resulting affine majorant uniformly below cutoff.
`FibreRamarePartitionedFinal.lean` carries that majorant through Gallagher kernel and fibre bridge to
the Route-E fibre mean square. Its capstone still assumes the ladder defect, pointwise block bounds,
exceptional cofactor bound, and exceptional prime mean square; it is an exact assembly theorem, not
an unconditional final fibre estimate.

The current sieve layer isolates a smaller analytic gate. `MoebiusWindowPartition.lean`,
`DoubleRamareWeight.lean`, `RamareRoughSetSplit.lean`, and `RamareLadderSupMeanSquare.lean` give
exact disc/annulus, two-range Ramaré, rough-set, and prime-sup/cofactor decompositions; the rough
count is paid by its Turán harmonic mass. `RamareLadderHM.lean` supplies the
Halász--Montgomery cofactor bound on measurable exceptional sets. The previous uniform far-kernel
cost is now removed: `Sieve/LogPhaseKernelKuzminLandau.lean` and
`Sieve/PlainKernelRecip.lean` prove reciprocal frequency decay; `Sieve/KernelRowMassRecip.lean`,
`Sieve/PlainKernelMassRecip.lean`, and `Sieve/LogPolyWindowHMRecip.lean` integrate it to the
explicit row/mean-square scale `N log T + |E| sqrt(T) log T` rather than `N|E|`. This closes the
kernel-mass bottleneck inside the exceptional-set estimate. `Sieve/RamareLadderHMRecip.lean`
installs this bound in actual cofactor blocks and the exceptional Ramaré ladder;
`Sieve/LadderAggregates.lean`, `Sieve/LadderGroupBudget.lean`, and
`Sieve/LargeLadderGroup.lean` reduce grouped large-half cost to harmonic mass, maximal block, and
prime count. Pointwise prime-block control and ladder-error/head premises remain, so this does not
produce the physical relation. `Sieve/TwoRangeSchedule.lean` fixes low/high bases, mesh ratios,
relative threshold, polynomial length, Gallagher cut, and head height and proves their elementary
positivity/basic limits; `Sieve/PrimeRangeLogLogMass.lean` supplies a wide-range harmonic upper
bound. `Sieve/TwoRangeScheduleFacts.lean` now discharges the structural callers: both designated
prime ranges lie in their ladders, the low ladder stays below window length, the high ladder stays
below its exponential top, both ladders have a step, the Gallagher cutoff and head height exceed
one, all high cofactor blocks are nonempty, and low-range harmonic mass is at most
`beta * log log x` eventually. `Sieve/TwoRangeLimits.lean` closes the elementary log/log-log and
zero-free exponential absorptions. The schedule's decisive pointwise block, ladder-error, and
relation-specific group/head inequalities are not yet theorems. Meanwhile
`MoebiusTwoRangeWindow.lean` makes the small annulus unconditional and leaves the large annulus's
pointwise high-prime estimate explicit. `AffineFromHead.lean`, `MoebiusHeadGate.lean`,
`MoebiusHeadBudget.lean`, and `MoebiusHeadSmall.lean` reduce the averaged Route-E mean square to one
relative head estimate at height `(M/h) omega`, with total budget at most
`90/h + 60/omega + 9 B/M^2`. This is a real reduction of analytic prerequisites, not the physical
transport theorem: the head estimate remains a premise and none of these declarations defines
adjacency, relation-specific Hall expansion, unit co-degree, or co-moving signed flux. The exact
quadratic character/Ramanujan factorization in `BondarenkoHeapLemmaNine.lean`, including exact
level-4/8 two-adic CRT and conductor normalization, strengthens finite character-correlation input
but likewise does not construct `R_X`.

These theorems strengthen capacity and cost accounting only: none declares which two opposite-sign
integers are adjacent in one source-fixed relation, so they cannot prove Hall or co-moving flux.

`Sieve/ShortExceptionalMeasure.lean` closes the free-threshold, relative-threshold, and
maximum-threshold exceptional-measure bounds and the blockwise annulus-large moment estimate with
no block-cardinality loss. Exceptional measure is therefore no longer a separate scientific axis.
These results are finite unsigned mean-square budgets: they neither define relation adjacency nor
prove interval Hall, unit co-degree, or co-moving signed flux.

The physical Boolean-anchor sign shortcut is now closed negatively.
`PhysicalIntervalAnchorCoarea.lean` proves that every anchored curvature is exactly

```text
nonnegative overlap coarea mass - nonnegative rank-one centering mass / aperture.
```

For the literal two-atom packet at `m=2,3`, Lean computes one transition aperture strictly between
`3 log(4/3)` and `4 log(4/3)` and proves the curvature is negative below it and positive above it.
Hence no aperture-independent physical anchor-sign law can replace E's relation theorem. The
positive survivor is the exact concentration-defect classification: any viable use of anchor
curvature must control overlap versus centering at the selected aperture from the source, not invoke
Boolean inclusion--exclusion or positivity of both masses alone.

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

### F2 — cofinal all-prime Sonin moment weld

**Architecture.** Assemble the literal logarithmically weighted, principal-subtracted Sonin
residuals over every prime power into one Hilbert--Schmidt operator `K_a`. Its energy
`T_a = K_a^* K_a` is positive and trace class. Real-polynomial probes of `T_a` therefore give a
nonnegative trace--Hankel form, and every such form is governed by the single intrinsic sequence

```text
m_r(a) = Tr(T_a^(r+1)).
```

The continued prime--Gamma source has a fixed centered moment sequence `M_r`, unconditionally
equal to the centered Xi reciprocal moments. If one positive aperture sequence makes every fixed
`m_r(a_j)` converge to `M_r`, or if one positive aperture law has `M_r` as the barycenter of the
Sonin moments, positivity passes to every integer-polynomial prime--Gamma Hankel test and forces
RH. This route is infinite, paired, nonphysical, and entirely pre-divisor at its open premise.

**Proved.** `SoninAllPrimeResidualKernel.lean` constructs `K_a`, proves Hilbert--Schmidt
convergence, constructs positive trace-class `T_a`, and proves every real-polynomial trace--Hankel
test is real and nonnegative. `SoninAllPrimeHankelCollapse.lean` reduces the full Gram functional to
the one moment sequence above. `SoninPrimeArchPerTestTransfer.lean`,
`SoninPrimeArchFiniteMomentTransfer.lean`, and `SoninPrimeArchCofinalMomentSection.lean` prove the
successive transfer chain: finite moment-block closure is equivalent to one cofinal all-moment
aperture section, and either the section or a uniform growing-block approximation implies RH.
`SoninPrimeArchMomentBarycenter.lean` gives the parallel positive-aperture-law route.

The latest source modules make the two sides literal without joining them.
`SoninSemilocalCorrectedSource.lean` constructs an actual trace-class finite cyclic prime-power
operator, proves its trace is the finite von--Mangoldt flux, adds the exact continued
prime--archimedean completion remainder, and proves every centered moment of the completed trace
family equals the actual Xi reciprocal moment. `SoninSemilocalProlateFinitePart.lean` independently
constructs the physical/Fourier boundary transition, its positive trace-class carrier, and the
identities

```text
Tr(carrier) = prolate finite part = Re Tr(T_prolate - T_prolate^2),
retained prolate energy + finite part = 4 a^2.
```

These are provenance and positivity theorems on different carriers. The completion carrier in the
corrected-source module realizes the required scalar trace by a normalized rank-one carrier; no
theorem makes it positive or identifies its powers with `T_a`. Conversely, the prolate finite-part
carrier contains no prime, Gamma, Xi, or completed-source coefficient.

The remaining seam cannot be repaired by a passive Euler polar weight.
`SoninEulerInversePolarCorner.lean` proves the one-prime Euler weight is positive and boundedly
invertible, yet its inverse, square root, and inverse-square-root all retain a noncompact Sonin
cross-boundary corner. `SoninSylvesterFactorization.lean` identifies the relative-resolvent corner
as the exact Sylvester transform of that Euler crossing and transports compact/Schatten status
through invertible source maps. This closes operator-algebra factorization and rules out polar
compactification; it does not identify the all-power moment sequence.

**Open core.** Prove, from the literal Sonin/prime--Gamma source and without divisor selection, one
cofinal all-moment identification:

```text
forall r,  m_r(a_j) -> M_r
```

for a common aperture sequence, or the proved barycentric equivalent sufficient for every Hankel
test. A useful stronger form would identify the completed cyclic remainder with the independently
positive prolate/all-prime energy carrier in a way preserving all mixed powers, not merely its
zeroth trace. One scalar trace equality cannot transfer Hankel positivity. Existing bounded or
sublinear compact completions are formally excluded, and the coupled Feshbach/variance upper bound
is itself classified as RH-equivalent. F2 is therefore the positive cofinal-moment successor to
retired Route F, not a reopening of F's passive compact-completion mechanism.

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
a new live route. `GUStructureAdmissionSplit.lean` proves the common G/U structural shortcut
impossible: G-side holomorphic gauge structure cannot force route admission, U-side structural face
does not determine the crossing sign or Christoffel-port orientation, and a structural
correspondence alone transports neither. Missing law must be source admission, not an abstract
G--U equivalence.

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

Local--global quotient packaging is also no longer a missing formal interface. The period-one Tate
exponential is exact modulo the integer lattice; divisorial log sections modulo units are exactly
their finite valuation profiles; global units modulo roots of unity inject into and identify their
realized product-formula currents; finite-place plus archimedean divisors modulo principal graph
divisors are measured by total Arakelov degree; and the all-prime oriented Calderon--Witt cokernel is
the complex orientation line. The rational global-adele additive character is surjective and its
class group modulo character kernel is exactly `R/Z`
(`FieldOneGlobalAdeleCharacterKernelQuotient.lean`, `DeningerTateKummerQuotient.lean`,
`DeningerLogKummerQuotient.lean`, `DeningerKummerReciprocityQuotient.lean`,
`DeningerArithmeticRealArakelovQuotient.lean`,
`DeningerCalderonWittOrientedQuotient.lean`). These exact quotients organize the two sides but do not
identify the singular arithmetic restriction with Burnol/Deninger physical landing.

`DeningerArithmeticGlobalJetExact.lean` closes compact-open analytic Xi cohomology at every
multiplicity simultaneously: all local multiplicity-bounded jets vanish exactly on the global
Xi-multiplication range, every local jet family is globally realized, and global cohomology is
linearly equivalent to the full local-jet family. This is global analytic division and
interpolation, not the missing arithmetic restriction or physical comparison.

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
(`BurnolCoPoissonCosineClosedZeroJetDetection.lean`). They do not prove the required all-prime
arithmetic restriction/Bessel theorem or physical descent.
`BurnolSoninFiniteJetEvaluation.lean` closes the first nontrivial completion step: the literal first
logarithmic Mellin derivative kernel has exact norm, is square-integrable on every strict right
tail, admits a local `L2` majorant, differentiates under the literal Mellin tail integral, and
defines a bounded continuous linear functional whose value is that derivative integral.

`DeningerPrimePacketContinuousRestrictionGreen.lean` closes the general analytic type conversion:
continuous compact-packet restrictions embed faithfully and contractively into Haar `L2`; a
square-summable sup-norm Bessel estimate yields the global Hilbert-valued restriction; and its
nonnegative Green energy has radical exactly the simultaneous kernel of the original continuous
restrictions. Higher-jet Hilbert packaging is therefore not the frontier.

More importantly, the corpus has passed the earlier packet-formation gate.
`CCMRationalAdelicPrimeIsotropyRelativeXiChainMap.lean` constructs the genuine rational-adelic
relative source complex and a strict resolved-Xi chain map: its retained class lands on a target
boundary, the next differential kills it, and prime, depth, divisor, and nonzero leading Xi
coefficient survive. `DeningerGammaSixCofinalMeyerTateXiGreenBoundary.lean` constructs the literal
cofinal Tate naturality differential, proves a top-coordinate left inverse, forms concrete
ordinary-prime chains converging to the completed Xi Green vertical boundary, and proves every
finite chain and its completed limit have the same actual Gamma/Sonin physical value. That value
vanishes exactly on the critical line. Thus strict resolved provenance and a concrete physical
receiver both exist; what is absent is the theorem identifying boundary annihilation on the source
side with annihilation by that fixed physical reader.

**Open core.** Construct, before divisor specialization, a source-derived singular comparison from
the completed Green/BV boundary to the already resolved target whose degree-zero component is
*exactly* the existing Burnol/Deninger physical landing. It must commute with the source and target
differentials, make the physical reader annihilate the relevant target boundary, and preserve
ordinary-prime provenance, multiplicity jets, and the nonzero Xi coefficient. No premise may
assume the conormal defect is zero. At degree six the existing comparison reads a nonzero scalar
multiple of `K_6(rho)`; strict physical boundary annihilation would force `K_6(rho)=0` and hence RH.
Generic continuous-restriction/Bessel packaging is now optional implementation infrastructure, not
the first scientific frontier.

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

The finite/low-height block now has a sharper source normal form. Equal-mass prime--polar quantile
cells are exact cosine-characteristic discrepancies with quadratic contact at zero; the terminal
polar seam joins them into one completed-head phase symbol, including overshoot with its literal
sign (`CCMActualHeadOutgoingQuantileCharacteristicTransport.lean`,
`CCMActualHeadOutgoingQuantileCompletedCharacteristicSeam.lean`). At quadratic-form level every
signed finite cosine measure supported beyond aperture diameter is a null gauge. Therefore a
pointwise nonnegative representative of the corrected symbol in every exterior-measure gauge class
proves RH (`CCMActualHeadExteriorCosineMeasureGauge.lean`). Gamma coercivity reduces each such
global sign test to one compact symmetric frequency interval. Exterior superoscillation proves
qualitative compact-core expressivity, but exact variation—and the total correcting measure
mass—grows exponentially under genuine downshift. Local approximation therefore does not supply a
controlled nonnegative representative (`CCMActualHeadExteriorGaugeCoerciveCompactReduction.lean`,
`CCMActualHeadExteriorCosineSuperoscillation.lean`).

`TwoEdgeBoundaryQuartet.lean` gives a complementary receiver theorem: for any fixed selected
off-line quartet and nonvanishing edge transform, a phase-matched cofinal aperture sequence drives
its two-edge Weil contribution to negative infinity while the critical-line background stays
uniformly bounded. This is not actual-head selection: aperture phase is chosen from the selected
quartet, and no simultaneous source control of the remaining divisor is supplied. It adds no
independent route but confirms why a canonical global boundary selection law would be decisive.

Formal sources: `CCMRestrictedWeilCanonicalGroundHeadEnergy.lean`,
`CCMRestrictedWeilActualHeadCompletedErrorProducer.lean`,
`CCMActualHeadSignedCompletedErrorGammaProducer.lean`,
`CCMActualHeadOutgoingQuantileTransportProducer.lean`,
`CCMActualHeadCoherentCompletedGammaProducer.lean`,
`CCMActualHeadCoherentQuantileGammaProducer.lean`,
`CCMActualHeadOutgoingQuantileCompletedCharacteristicSeam.lean`,
`CCMActualHeadExteriorCosineMeasureGauge.lean`.

**Open core.** At every aperture, prove cofinally on canonical actual heads the literal
reverse-prime bound, equivalently nonnegativity of the cancellation-preserving coherent completed
producer at exact threshold. The sharp constructive sufficient target is now: produce two finite
signed exterior measures, supported beyond aperture diameter and with controlled mass, whose gauge
correction makes the explicit completed-head characteristic symbol nonnegative on the compact
coercive core. Superoscillatory density without mass control is insufficient.

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
`SourceHorizontalStokesCoenergySharpPrimeAsymptotic.lean` closes the fixed-depth local tail:
Stokes-conditioned coenergy has exact decay `p^(-2-2se)` with sharp constant
`(1-s)/(sqrt(2)*(e+1)^2)`, and the coefficient-faithful two-clock majorant has asymptotic ratio
`1/(4*sqrt(2))`. This proves summable local asymptotics, not identification or favorable order of
the completed global coenergy.
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
`XiPositivePairedDiagonalSectorCollapse.lean` makes the receiver smaller still. At the discharged
exterior radius `218/25`, nonnegativity of the single positive-paired source diagonal at every
admissible exterior pole is equivalent both to finite reduced-matrix passivity and to RH. Its
reverse diagonal-to-matrix implication passes through Xi-specific RH capstones; it is not a generic
kernel theorem and supplies no source sign. The frontier may therefore be stated as scalar exterior
diagonal order or finite-matrix order, but neither is upstream of RH.

The absolute-Euler source side is now compressed to one infinite nonphysical current.
`PairedInfiniteApertureCurrent.lean` proves that the aperture boundary term dies using only the
elementary square-root bound for completed critical error; every prime and prime power is absorbed
into the cumulative critical-Mellin source. `PairedCompletedEulerCurrent.lean` then gives the exact
packet identity

```text
paired completed value
  = 8 * (compensated Gauss-resolvent quadratic - critical-error current).
```

`PairedTranslationResolventCalculus.lean` realizes each Cauchy atom by the tail resolvent of the
right-translation semigroup and proves its contact identity. Thus prime summation, aperture passage,
and resolvent formation are closed. Missing datum remains the sign of the coupled Gauss-minus-error
quadratic, not construction or convergence of the paired current.

Formal sources: `XiHurwitzOrientationSeparatedSourceReconstruction.lean`,
`XiHurwitzOrientationExteriorCauchyClosure.lean`,
`XiHurwitzOrientationPositivePairedSource.lean`,
`XiPositivePairedRealLoewnerSeam.lean`,
`XiCauchyTransformCompleteness.lean`, `XiEulerSafePairedCompleteness.lean`,
`XiEulerSafePairedClosure.lean`, `XiEulerSafePairedRationalCriterion.lean`,
`XiEulerSafePairedValueKernel.lean`,
`PairedInfiniteApertureCurrent.lean`, `PairedCompletedEulerCurrent.lean`,
`PairedTranslationResolventCalculus.lean`,
`XiHurwitzOrientationSharpNonnegativeConeDistance.lean`,
`XiHurwitzOrientationBoundaryMixedIncidence.lean`.

**Open core.** Prove directly from continued prime--Gamma source, before selecting a divisor, that
the explicit positive-paired exterior diagonal is nonnegative at every admissible pole. Equivalently
at the Xi endpoint, the compensated Gauss-resolvent quadratic dominates the critical-error current
for every finite packet, or the explicit paired-value kernel `K` is PSD on Gaussian-rational
absolute-Euler poles in one open quadrant. Prime summation, aperture removal, resolvent formation,
packet construction, countable exterior exhaustion, orientation membership, scalar evaluation,
and Xi-specific diagonal collapse are closed. Because both diagonal order and restricted passivity
are already RH-equivalent, a proof must derive the diagonal sign from an independent source law;
the endpoint equivalence cannot be reused as producer.

### CLG/TTF — critical Loewner observability and theta-tilt flux

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
Pick kernel. `CaratheodoryKernelPositive.lean` proves the generic positive-real Carathéodory
kernel theorem. `XiEulerSafeCauchyLoss.lean` then identifies the source-specific missing step more
sharply. On the safe half-plane the shifted kernel `K_a` is PSD, the Cauchy-loss kernel `C_a` is a
Laplace Gram kernel, and their Schur product is PSD, while

```text
K_0 = K_a * (1 - C_a).
```

Consequently RH is equivalent both to PSD of this critical difference and to domination of the
Cauchy-loss energy by safe-kernel energy on every finite node/coefficient system.
`PSDKernelDensity.lean` reduces that test, for continuous Hermitian kernels, to any dense node and
coefficient family. This literal Euler--Gamma handoff, independent of zero selection, promotes CLG
to live.

`XiWeilTwoChannelResolvent.lean` now identifies this same critical kernel entrywise with

```text
q_W(A_W,A_V) + q_W(B_W,B_V),
A_W(z)=W/(W^2+z^2),  B_W(z)=z/(W^2+z^2),
```

equivalently the mean of the two Hardy-orientation Gram kernels, and proves the entry is the
absolutely convergent Euler--Gamma logarithmic-derivative kernel on the safe half-plane.
`XiWeilApertureChannels.lean` realizes `A,B` as Fourier transforms of truncated two-sided
exponentials, proves pointwise finite-packet convergence, and proves two sharp index statements:
every negative limiting packet is negative at all sufficiently large apertures, while
nonnegativity of all nonnegative-aperture packet energies is exactly RH. This **W2C** bridge makes
CLG a literal paired finite-aperture detector and links its receiver to restricted-Weil geometry.
It does not prove source positivity: every aperture energy is still evaluated by
`xiWeilPolarization`, hence already uses the Xi divisor.

The safe-to-critical bridge is explicit. `XiBoundaryPoissonDensity.lean` proves every
safe density is a convergent positive Poisson-kernel divisor sum and that all safe offsets form one
Poisson semigroup orbit. `XiBoundaryCauchyRepresentation.lean` proves integrability and exact
Cauchy evaluation for each individual divisor term against the two-node boundary kernel, controls
the sum of integral norms, and proves the full identity

```text
safe Caratheodory kernel
  = (1/pi) * integral safe-density(t) * boundary-Cauchy-kernel(t) dt.
```

`XiEulerSafeObservability.lean` closes finite-packet formation rather than merely restating the
density transform. For safe offset `a>1/2`, packet amplitude `A` and its one-sided tail `A_t`, the
explicit deficit is

```text
int h_a(t) |A(t)|^2 dt - 2a int h_a(t) int_0^infinity |A_t(u)|^2 du dt.
```

All terms are integrable. The deficit is independent of `a`, equals `pi` times the critical
logarithmic-derivative kernel energy, and its stationary form is the deficit divided by `2*pi`.
Nonnegativity for every complex packet—and separately for every real packet—is exactly RH. Thus
finite-packet convergence, full cross-node summation, and exact safe-to-critical evaluation are
closed. The missing statement is order of this already explicit source functional.
`XiDePoissonizedStationarity.lean` gives the complementary source algebra: exponential packets are
safe-offset tilts, their tail Laplace transforms are the two Cauchy resolvent sums, and inverse
Poisson conjugation changes every prime-power weight

```text
-Lambda(n) n^(-1/2-a) / 2
```

exactly to the offset-free critical weight `-Lambda(n) n^(-1/2) / 2`. This removes artificial safe
offset at each atom. `XiEulerSafeObservability.lean` supplies convergence and exact evaluation of the
corresponding full packet deficit, but not its nonnegativity. Because its evaluated value is exactly
the RH kernel energy, this is a bridge within CLG/Q/W2C, not an independent producer.

The theta presentation is now exactly welded to this same producer.
`ThetaCuspTiltFluxObservabilityWeld.lean` proves entrywise

```text
sourceBezoutian(theta,w,v)
  = xiCent(w) conj(xiCent(v)) criticalLogDerivKernel(w,v),
```

and proves that the coefficient change `c_j -> c_j xiCent(w_j)` is invertible on every safe
half-plane. Under this change the Euler-safe deficit is exactly `pi` times the literal theta-source
flux. Universal theta flux order and universal observability order are therefore equivalent, not
independent proof routes. `ThetaCuspTiltFluxHedenmalmWeld.lean` identifies the diagonal with the
completed-Xi transverse current divided by `2a`, then with the pointed Hedenmalm split Krein value,
and proves every one-node packet nonnegative for `a>=1/2`. Any negative RH-bearing packet must have
at least two nodes. `ThetaSourceHorizontalFluxExtractor.lean` explains the generic scalar
mechanism—an off-axis transform zero forces a negative diagonal somewhere between the imaginary
axis and that zero—but does not locate the witness beyond the critical half-line.

`ThetaCuspTiltFluxWeilParityWeld.lean` closes the final representation square. For
every finite linked packet, the Euler-safe deficit is `pi` times the sum of the canonical two
Weil-channel diagonals, and its real part is

```text
(total reflection-even divisor energy) - (total reflection-odd divisor energy).
```

After same invertible `xiCent` coefficient rescaling, this is exactly the literal theta tilt
derivative. RH is equivalent to contractivity of reflection-odd projection against
reflection-even projection on every linked packet. Parity-energy domination is therefore the
shared open producer, not a third route or an additional receiver gap.
`ThetaCuspTiltFluxWeilParityEulerRayWeld.lean` further identifies the positive real-node critical
kernel with the complete squared-Euler divisor-response kernel and uses its strict two-point
determinant to prove parity domination for every complex two-mode packet on two ordered exterior
Euler-ray nodes. Thus neither scalar packets nor two real-ray modes carry remaining RH burden.

`ThetaCuspTiltFluxWeilParityCauchyLocalization.lean` then makes that residual description exact and
strictly smaller. RH is equivalent to reflection-odd contraction on only the regular two-pole
Cauchy family. Given any off-line Xi fibre, Lean constructs moving regular poles whose normalized
two-Cauchy packet converges to the antisymmetric fibre indicator and proves

```text
even energy -> 0,
odd energy  -> N,
```

where `N>0` is exact cardinality of the fibre and its reflected fibre. The localized packets
eventually leave the parity cone. `ThetaCuspTiltFluxWeilParityCauchySourceEscape.lean` chooses same
poles inside the full continued prime--archimedean source domain, avoids every pole/reflection
collision, and strengthens limit to

```text
continued rank-two source energy -> -N,
```

with eventual strict negativity. This identifies unique asymptotic failure geometry: cofinal
reflection-antisymmetric rank-two Cauchy escape. It also shows that positivity valid only on fixed
compact pole sets, fixed nodes, or nonmoving local source families cannot close route.

The Schwarz-pair branch is now classified separately. `ThetaCuspTiltFluxWeilParitySchwarzPairNullCone.lean`
proves canonical Schwarz-paired fibre packet is exactly Weil-isotropic with equal strictly positive
even and odd energies off line.
`ThetaCuspTiltFluxWeilParitySchwarzPairCrossing.lean` computes its exact multiplicity-sensitive
first crossing, while `ThetaCuspTiltFluxWeilParitySchwarzPairLorentzWeld.lean` decomposes it into
tangential and source-normal rates. Tangential coefficient is strictly negative at every Xi zero,
so it cannot vanish selectively under RH. Source-normal coefficient is the reflected-source
entropy/transverse defect, vanishes exactly on critical line, and the two rates obey exact
Lorentz/Pythagorean conservation. Hence tangential crossing is terminal; normal no-escape is the
surviving RH-bearing channel.

**Open core and exact obstruction.** Prove directly from completed theta/Euler--Gamma source that
no admissible cofinal regular two-pole Cauchy sequence can undergo reflection-antisymmetric escape.
Equivalently, prove source order strongly enough that every such moving packet satisfies

```text
int h_a |A|^2 >= 2a int h_a int_0^infinity |A_t|^2.
```

This moving rank-two statement already implies global source-specific observability, Schur
domination of Cauchy loss by safe kernel, and domination of total reflection-odd channel energy by
total reflection-even energy because regular two-Cauchy passivity is exactly RH. Deficit
construction and evaluation cannot be used as producer: universal nonnegativity is already exactly
RH. A proof must explain no-escape upstream from literal source formation, without divisor
polarization. The earlier phrase "complex nodes or at least three real-ray modes" remains a proved
finite-packet restriction but is no longer the sharp frontier; moving complex two-pole packets
already exhaust every off-line fibre.
This is source-isogenous to UEB and Q but a different infinitesimal-shift mechanism.
`not_isPSDKernel_shiftGenerator` proves **every** positive shift `omega>0` has non-PSD generator,
so positive Loewner flow from the safe region is dead. The two-node model no-go
`not_isPSDKernel_modelLoss` is stronger: a positive-real function may have a PSD shifted kernel and
a strictly subunit diagonal loss factor while the subtracted kernel still has negative determinant.
Thus diagonal contraction, one-node bounds, and generic positive-real theory cannot close CLG.
`ThetaSourceStrictLogConcavityFluxNoGo.lean` independently proves local source shape is insufficient:
an explicit positive, even, superexponentially decaying, globally strictly log-concave theta source
has a right-half-plane zero and a strictly negative one-node neutral flux. Hence log-concavity,
unimodality, positivity, and rapid decay cannot prove the actual theta packet order without using
its arithmetic global structure. Viable proof must use global source-specific cross-node incidence. CLG/TTF is infinite, paired, and
nonphysical; its producer is concrete complete-prime versus archimedean/Cauchy-loss domination.

### T1 — Xi-Taylor/theta-tail finite-arithmetic core current

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
two-regime upper bound for T1's twist envelope and an explicit polylogarithmic envelope.
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
decompositions. At T1's short window their error scale is larger than the signed block to be
controlled, and differencing two prefix inequalities loses the required joint sign. Thus new
bounds and movable-edge AFE do not close—or reformulate away—the signed short-block producer;
reflected dual-edge estimation and joint signed cancellation remain absent.

`ZetaChiVerticalGrowth.lean` now closes the former archimedean title-level gap: for every
`sigma in [-1,1/2]` the chi factor has a polynomial majorant on the whole vertical line, not merely
fixed-line pole avoidance. `MoebiusDiscRate.lean`, `MoebiusWindowPartition.lean`,
`DoubleRamareWeight.lean`, and `RamareRoughSetSplit.lean` feed the all-height Route-T rate into exact
disc/two-range window and rough-set decompositions. The resulting inequalities remain
absolute-value or mean-square statements, and the large-annulus theorem still accepts a pointwise
high-range prime estimate from its caller. They sharpen T/E analytic input and close chi
bookkeeping, but cannot recover cancellation between T1's top row and its finite-translation
survivor.

The two-range contour accounting has a closed elementary shell. `Sieve/TwoRangeMajorant.lean`
bounds all five relative-annulus terms at

```text
D=(log x)^(b+A3+1),
Lx=log 2+(log x)^b,
t0=(log x)^(4b+3A3+3),
```

and proves logarithmic-power decay once the zero-free exponential factor and high-range bottom
factor satisfy their two displayed limit hypotheses. `Sieve/TwoRangeRouteT.lean` fixes the actual
frequency, lower cutoff, contour width, and height cost and proves high-block logarithmic bounds,
unit width, threshold clearance, and disc containment. `Sieve/TwoRangeHighBound.lean` supplies the
actual pointwise high-block estimate and a relative rate beating every admissible logarithmic power.
`Sieve/TwoRangeGroupLimits.lean` proves that the normalized small-ladder, defect, and rough groups
each tend to zero under the stated schedule inequalities. No declaration imports those group limits
and high-block witness into one final specialization of
`integral_Icc_normSq_logPoly_moebius_le_twoRange`; even that positive mean-square assembly would not
imply the signed short-current estimate.

The detector packet itself is closed. The common low- and high-real parts, low-ordinate part, and
exact high tail tend to zero under the buffered schedule. The full exact-multiplicity Xi Mellin zero
series is absolutely summable and its normalized sum tends to zero
(`Sieve/InghamUniformDetectorMellinFullXiSum.lean`). This is kernel-weighted vanishing, not an
absolute off-line zero count, so it does not close HC. The matching source decomposition in
`XiCTaylorThetaTailFullDensityMonotoneCurrent.lean` discharges the zero-free full-density aggregate
current and concentrates all RH content in the canonical transfer current from that channel into
finite odd Xi Taylor sections. Sublinearity for one admissible schedule, and for every schedule, is
exactly RH; no independent sublinear producer is proved.

The Bondarenko--Heap/Chen--Gupta--Li detector is now source-correct through its complete finite
alternative. Lean constructs the exact level-4/8 source factorization, finite detector product,
primitive zero-window rows, natural `K+1` spacing, and the zero-by-zero partition into:

```text
Class I: a normalized dyadic detector tail is large;
Class II: a finite left-line Mellin integral is large.
```

For Class I, the heterogeneous packet is Abel-deweighted to a bounded common-coefficient prefix.
The natural cutoff dominates the tail, its common threshold is positive and attained by one common
polynomial, and natural prefix fibres retain one coefficient vector with correct same-character
ordinate separation. The fibre second moment is exactly diagonal plus a bounded harmonic
off-diagonal correction; the finite large-value problem reduces to explicit divisor-square energy.
For Class II, Lean constructs the local maximizing point and compact left-contour envelope and
reduces the finite large-value problem to a sampled fourth moment. Character-packet second moments,
fourth moments, quartet expansions, and near/far energy subcounts are exact finite identities.

Finite contour formation is also closed: the full smoothed initial-line Mellin identity holds; the
Gamma-origin residue cancels at every certified zero; nonprincipal finite contours have zero charge;
the principal translated pole has its explicit residue and contour charge. Canonical finite
horizontal-edge bounds and smoothed vertical balance exist. What is not proved is a
parameter-uniform passage to large height together with the refined conductor-uniform correlation,
fourth-moment, and zero-density exponent needed for an absolute census. Thus the analytic
zero alternative, common-prefix extraction, source-correct fibre formation, and finite moment
reductions are no longer open. HC still lacks the global uniform estimate that closes the census;
T still lacks a signed short-block estimate preserving its top-row/translation cancellation.

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
`SmoothAFETruncation.lean`, `ZetaChiVerticalGrowth.lean`,
`BondarenkoHeapLemmaNineTwoAdic.lean`, `BondarenkoHeapLemmaTenConductorAggregation.lean`,
`BondarenkoHeapLemmaTenDetectorPolynomial.lean`, `ChenGuptaLiFiniteZeroDetector.lean`,
`ChenGuptaLiCharacterLargeValues.lean`, `ChenGuptaLiAnalyticAnchor.lean`,
`ChenGuptaLiDetectorTail.lean`, `ChenGuptaLiTailCoefficientBounds.lean`,
`ChenGuptaLiFiniteMellinSlice.lean`, `ChenGuptaLiInfiniteMellinDetector.lean`,
`ChenGuptaLiZeroResidue.lean`, `ChenGuptaLiNonprincipalAnalytic.lean`,
`ChenGuptaLiPrincipalResidue.lean`, `ChenGuptaLiPrincipalContour.lean`,
`ChenGuptaLiClassIParameters.lean`, `ChenGuptaLiClassIBlock.lean`,
`ChenGuptaLiPrimitiveZeroRows.lean`, `ChenGuptaLiPrimitiveZeroPartition.lean`,
`ChenGuptaLiPrimitiveClassINaturalRows.lean`, `ChenGuptaLiPrimitiveClassINaturalPartition.lean`,
`ChenGuptaLiClassIMellinAlternative.lean`, `ChenGuptaLiClassINormalizedDyadicWitness.lean`,
`ChenGuptaLiPrimitiveClassINaturalHeterogeneousPacket.lean`,
`ChenGuptaLiPrimitiveClassINaturalCommonPrefixWitness.lean`,
`ChenGuptaLiPrimitiveClassINaturalPrefixFibers.lean`,
`ChenGuptaLiPrimitiveClassINaturalPrefixFiberThreshold.lean`,
`ChenGuptaLiPrimitiveClassINaturalPrefixFiberMatrix.lean`,
`ChenGuptaLiPrimitiveClassINaturalPrefixFiberSeparation.lean`,
`ChenGuptaLiPrimitiveClassINaturalPrefixFiberLargeValues.lean`,
`ChenGuptaLiClassIPrefixFiberSeparation.lean`, `ChenGuptaLiClassIPrefixFiberLargeValues.lean`,
`ChenGuptaLiClassIICriticalLine.lean`, `ChenGuptaLiClassIILocalMaximizer.lean`,
`ChenGuptaLiClassIILeftIntegralEnvelope.lean`,
`ChenGuptaLiCharacterOrthogonality.lean`, `ChenGuptaLiCharacterPacketKernel.lean`,
`ChenGuptaLiCharacterPacketSeparation.lean`, `ChenGuptaLiCharacterPacketOffDiagonal.lean`,
`ChenGuptaLiCharacterPacketAggregate.lean`, `Sieve/TwoRangeMajorant.lean`,
`Sieve/TwoRangeRouteT.lean`, `Sieve/TwoRangeHighBound.lean`, `Sieve/TwoRangeGroupLimits.lean`,
`Sieve/InghamUniformDetectorMellinFullXiSum.lean`,
`XiCTaylorThetaTailFullDensityMonotoneCurrent.lean`.

**Open core.** Prove a source-first sublinear bound for the canonical full-density transfer current.
Its concrete finite-arithmetic form is a joint upper estimate for
`canonicalThetaTailCoreFiniteArithmeticRemainderCurrent` at same cutoff and depth as prefix selector,
retaining cancellation between top-row and translation pieces. More top-row decay is dead work:
survivor conserves exactly what row loses. Separate absolute-value bounds destroy sign.
For current Maynard specialization, this is pure short Möbius-block cancellation strong enough to
discharge joint current estimate. Its preceding GS-tail, all-frequency pretentious-distance,
smooth Möbius power-saving, fixed-left-line Xi-factor, zeta/log endpoint, and initial-range Abel
subgates are closed; same power saving also holds for full Möbius series at moving abscissa.
Scientific open core is signed short Möbius-block cancellation
preserving the joint top-row/translation current; further threshold bookkeeping or unsigned
smooth-sum bounds do not address it. Full zero-packet vanishing is already proved, while universal
transfer-current sublinearity is already RH-equivalent; neither is an upstream source theorem.

Finite-Hermite contour, critical mass/Dirichlet cone, co-moving mass cone, and sharp spacelike
summability are alternative formal receivers/partial decompositions. Current most concrete single
quantity is combined finite-arithmetic remainder.

### T2 — Wold--mesh residual continuation

**Architecture.** Order the primes and compare the literal Wold mass cell with its adjacent
logarithmic prime-mesh cell. After removing the convergent logarithmic holonomy, the cumulative
discrepancy is a coefficient-faithful arithmetic connection. Its complex phase differences form a
Hardy kernel. The rotated kernel is exactly a four-shift prime-zeta derivative minus the physical
log-mesh current and one holonomy atom. Extending this source kernel through the critical
half-height, while controlling the intrinsic quadratic mesh defect, gives a holomorphic first-order
ODE for shifted zeta and excludes every zero right of the critical line.

**Proved source and connector chain.** `XiHeatCassiniWoldConvergentLogHolonomy.lean` proves the
centered Wold primitive tends to zero and isolates its local increment.
`XiHeatCassiniWoldLowerHalfShiftGapSummability.lean`,
`XiHeatCassiniWoldLowerHalfShiftGevreyKernel.lean`, and
`XiHeatCassiniWoldResidualHardyPolarization.lean` prove finite physical variation, all prime-log
moments, absolute convergence, and holomorphy of the residual Hardy kernel throughout `Im z<0`.
`XiHeatCassiniWoldPrimeZetaLaplaceSymbol.lean` gives the exact prime-zeta/mesh/holonomy normal form.
The mesh remainder at the critical wall is neither an artifact nor a loose Taylor loss:
`XiHeatCassiniLogMeshDefectPrimeGapEquivalence.lean` proves

```text
sum_N ||physical mesh defect_N(-1/2)|| < infinity
  iff sum_N gap(p_N)^2 / p_N^(3/2) < infinity.
```

The same energy controls the complete closed mesh half-strip. Under it, the continued residual
agrees with the safe Hardy kernel and retains residue `-m` at every zeta zero of multiplicity `m`
with `Re rho>1/2`; mesh and holonomy have zero residue
(`XiHeatCassiniWoldRelativeOrbitLeakage.lean`). The formal shift orbit carries the same nonzero
multiplicity and therefore requires a nonzero compensator. Finally,
`XiHeatCassiniWoldResidualODEClosure.lean` proves

```text
AnalyticOn(residual Hardy kernel, Im z < 1/2)
and Summable(gap(p_N)^2 / p_N^(3/2))
imply RH.
```

Equivalent receivers use absolute convergence on every sub-half boundary, endpoint half-rate
residual decay plus critical energy, or regularity of the one forced continued residual at all
right-strip zeros. These are endpoints, not source proofs.

**Latest arithmetic normal form.** `XiHeatCassiniWoldResidualFirstOrderGapFluctuation.lean` splits
each residual increment into universal prime-density fluctuation, minus a positive trace-class Euler
depletion, plus a nonnegative log-quadrature error controlled by critical gap energy.
`XiHeatCassiniWoldChebyshevErrorIncrement.lean` sharpens this to

```text
R_(N+1)-R_N
  = normalized consecutive Chebyshev-error increment
    - Euler trace depletion
    - backward log-cell depletion,
```

with both depletions nonnegative; the backward term is also absorbed by critical gap energy. The
finite prefix identity is exact. Thus the unresolved continuation is concentrated in signed
Chebyshev-error accumulation after two completely classified lower-order losses. More estimates of
those losses do not address the remaining sign/cancellation channel.

`Sieve/MaynardOrderedPrimeGapOccupancy.lean` now gives critical energy a literal source-side
formation law. For gaps with endpoints in one physical dyadic block and lengths in `[2h,4h]`, it
reserves a right-edge interval of width `h`, proves the remaining base intervals are pairwise
disjoint and prime-free, computes their exact volume, and proves

```text
sum_(gap in shell) gap^2
  <= 8 h * volume{lambda in block : theta(lambda+h)-theta(lambda)=0}.
```

`Sieve/MaynardOrderedPrimeGapProportionalPrimeFree.lean` then chooses the fixed relative half-width
`h/(4x)`, proves every occupied base is prime-free for the corresponding proportional physical
window, and upgrades the same bound to exactly the bad-base geometry accepted by the existing
fixed-ambient Mellin/spatial-`L2` packet. This closes carrier formation, shellwise coarea, and the
previous geometry mismatch. `Sieve/MaynardFixedAmbientPacketInterval.lean` and
`MaynardFixedAmbientPacketNatOrder.lean` freeze the Heath--Brown aggregate independently of the
physical Mellin base and form the literal packet at every fixed Mellin order.
`MaynardPrimeFreeRangePacketComposition.lean` and
`MaynardPrimeFreeRangePacketNatOrder.lean` prove that a proportional polynomial-width prime-free
interval forces one of those finite packets to be large. Finally,
`MaynardPrimeFreeRangePacketTailEnvelope.lean` proves one logarithmic scalar envelope controls all
stopped comparable-width rungs. Thus adaptive ladder tails, Mellin order, and source-freezing are
not separate open axes.

What is not proved is the scalar envelope for the actual source aggregate uniformly over dyadic
physical blocks and gap scales, nor a global measure/large-value assembly summing the resulting
literal packet lower bounds into
`sum gap(p_N)^2 / p_N^(3/2) < infinity`. Thus first arithmetic premise is this scalar-envelope plus
critical-weight aggregation theorem, not an unstructured prime-gap moment, new local `L2` estimate,
or another packet construction.

**Closed shortcut.** Absolute boundary control is the wrong topology.
`XiHeatCassiniWoldCriticalGraphNoGo.lean` proves critical residual upper variation and critical gap
energy cannot coexist, and consequently the proposed two-sided critical Abel graph norm is
unconditionally false. The positive survivor is a boundary classification: assuming the subcritical
analytic source and critical energy, every critical-line zero forces radial residual Hardy norm to
blow up with its integer residue. A viable continuation must therefore be signed, renormalized,
distributional, or otherwise allow these forced boundary poles; it cannot be absolute at the
critical edge.

**Open core.** Prove from the ordered-prime source, without choosing a zero:

1. the one logarithmic scalar tail-envelope inequality for the actual fixed Heath--Brown source
   aggregate, uniformly over dyadic physical blocks and gap scales, followed by critical-weight
   aggregation of the resulting literal large packets to give critical gap-energy summability; and
2. signed/renormalized continuation of the residual Hardy kernel from `Im z<0` through every
   strict sub-half strip `Im z<a<1/2`, equivalently a source law controlling the Chebyshev-error
   accumulation after the two explicit depletions.

The conditions must be compatible with forced critical-line boundary poles. The exact absolute
critical graph norm, ordinary endpoint continuity, and separately bounded unsigned variations are
dead. T2 is an infinite paired, nonphysical source/mesh architecture and is independent of T1's
finite Xi-Taylor transfer-current cancellation.

Formal sources: `XiHeatCassiniWoldCenteredLogConnection.lean`,
`XiHeatCassiniWoldConvergentLogHolonomy.lean`,
`XiHeatCassiniWoldResidualHardyPolarization.lean`,
`XiHeatCassiniWoldPrimeZetaLaplaceSymbol.lean`,
`XiHeatCassiniLogMeshDefectPrimeGapEquivalence.lean`,
`XiHeatCassiniWoldRelativeOrbitLeakage.lean`,
`XiHeatCassiniWoldResidualODEClosure.lean`,
`XiHeatCassiniWoldCriticalGraphNoGo.lean`,
`XiHeatCassiniWoldResidualFirstOrderGapFluctuation.lean`, and
`XiHeatCassiniWoldChebyshevErrorIncrement.lean`, together with
`Sieve/MaynardOrderedPrimeGapOccupancy.lean` and
`Sieve/MaynardOrderedPrimeGapProportionalPrimeFree.lean`,
`Sieve/MaynardFixedAmbientPacketInterval.lean`,
`Sieve/MaynardPrimeFreeRangePacketComposition.lean`,
`Sieve/MaynardFixedAmbientPacketNatOrder.lean`,
`Sieve/MaynardPrimeFreeRangePacketNatOrder.lean`, and
`Sieve/MaynardPrimeFreeRangePacketTailEnvelope.lean`.

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
(`XiShiftedTerminalFrontierParabolicSynchronization.lean`). Above one universal source threshold
and beyond each block's terminal frontier, the adaptive mixed source has an unconditional
dimensionless cumulative Jacobi-flux floor `1/4`, uniform while mass and degree escape together
(`XiShiftedCanonicalAdmissionAdaptiveMixedSourceParabolicFluxCorridor.lean`). Thus cofinal producer admission and
degree--mass synchronization are closed; favorable sign/exclusion is not.

Formal sources: `XiShiftedReciprocalHankelTailCriterion.lean`,
`XiShiftedCanonicalAdmissionAdaptiveArithmeticSourceDegreeConnection.lean`,
`XiShiftedCanonicalAdmissionCofinalScheduleNoGo.lean`,
`XiShiftedCanonicalAdmissionAdaptiveMixedSourceParabolicFluxCorridor.lean`,
`SuzukiFirstContactBoundaryRoughness.lean`,
`XiShiftedHardEdgePrimeGammaKelvinTwoChartNoGo.lean`.

**Open core.** Prove uniform cofinal tail positivity/order for explicit source Hankel matrices, or
construct a non-scalar source mechanism that annihilates strict-frontier numerator/excludes its
endogenous admission zero before nonintegrable quotient forms. Generic numerator regularity,
arbitrary schedule delay, scalar counterterms, fixed-degree limits, and positivity along a
self-selected recession schedule are closed or insufficient. Fixed structural face data also
cannot determine crossing sign or port orientation (`GUStructureAdmissionSplit.lean`); source-native
admission is indispensable.

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
singleton-fibre lower bounds. `PhaseSignChainAvoid.lean` lets a phase chain avoid any prescribed
finite set once one extra `pi` of phase is available, and `HardySignSubchainCount.lean` shows only
retained sign-flip steps need be consecutive. `EntireMultiplicityFactor.lean` and
`RectangleNodeProductVariation.lean` peel finite detector zeros and account for their exact left-edge
variation. `LevinsonWindowUnconditional.lean` removes the critical-edge nonvanishing hypothesis;
`LevinsonWindowEdgeUnconditional.lean` estimates every edge; and
`LevinsonAdmissibleWindow.lean` chooses admissible heights in arbitrary prescribed intervals with no
hypotheses. The number of entire-detector zeros in the rectangle is now the sole undetermined term.
Even a density-one singleton result would not remove finitely many off-line pairs, so HC still
requires an absolute detector-zero bound or absolute defect control, not normalized proportion.

The Chen--Gupta--Li Mellin layer now supplies the exact finite zero alternative and both finite
large-value reductions. Every certified primitive zero enters the natural Class-I/Class-II
partition. Class I yields one bounded common-coefficient prefix fibre with positive common threshold,
same-character separation, an exact diagonal-plus-harmonic-error second moment, and divisor-square
energy reduction. Class II yields a compact left-contour maximizer/envelope and sampled fourth-moment
reduction. Finite nonprincipal contour charge is zero; principal charge is its explicit translated
pole residue. Therefore packet formation, the zero alternative, common-prefix extraction, finite
contours, fibre separation, and second/fourth-moment expansions are closed. Remaining analytic core
is the large-height, conductor-uniform correlation/fourth-moment estimate and zero-density exponent
strong enough for HC's absolute census, including uniform control of remote contour contributions.
Finite horizontal-edge estimates do not supply that global assembly.

The newest CGL/Bondarenko--Heap layer removes more finite abstraction without closing that global
estimate. `BondarenkoHeapLemmaSevenIntegerLift.lean` identifies equality of inverse-incidence
classes with the literal integer equation `r1*m2-r2*m1=l*q` and expands finite fibre energy in that
form. `BondarenkoHeapLemmaEight.lean` now has premise-free source-scale estimates for the odd,
level-four, and both level-eight fundamental-discriminant families. The literal CGL evaluation
matrix is packaged as a Euclidean operator in `ChenGuptaLiOperatorNormReduction.lean`; the number of
large rows is bounded by its squared operator norm times block length. The nonnegative finite
spectrum's coordinate size is then reduced in `ChenGuptaLiCenteredCubicSpectrum.lean` to its mean
plus the cube root of one centered cubic deviation. On the analytic side,
`Sieve/HuxleyDensityBound.lean` and `Sieve/HuxleyDensityHypothesis.lean` give the coefficient-native
energy form of Huxley's two-term large-value estimate: the cubic off-diagonal cost depends on the
intrinsic vector mass rather than a pointwise divisor bound.
`ChenGuptaLiGramCenteredTrace.lean` identifies mean and centered cubic deviation with the first and
third traces of the literal row Gram, `ChenGuptaLiCharacterGramCenteredTrace.lean` composes the
operator estimate with the character matrix, and `ChenGuptaLiSelectedLargeValuePacket.lean`
extracts a canonical nonempty packet whenever the large-value set is nonempty. Thus finite packet
selection and the exact cardinality inequality are closed.
`ChenGuptaLiWeightedCharacterMatrix.lean` also installs arbitrary complex dyadic weights—including
the literal smooth source weight—and proves weighted Lemma 4.1.
`ChenGuptaLiWeightedCharacterGram.lean` constructs its literal weighted row Gram and closes weighted
Lemma 4.2 and the combined large-value cardinality inequality in terms of centered first/third
traces. `ChenGuptaLiWeightedSelectedLargeValuePacket.lean` further proves that every weighted large
set is empty or contains an internally selected nonempty all-large packet satisfying exactly that
centered-Gram bound. `ChenGuptaLiWeightedHilbertSchmidt.lean` closes the first trace: the weighted
Gram trace is exactly row count times unit-supported squared weight mass.
`ChenGuptaLiWeightedCubicTrace.lean` removes the last matrix abstraction from the third trace: it is
the literal cyclic triple correlation, splits exactly into all-equal and off-diagonal row triples,
and each triple is expanded into its weighted six-label character/phase sum before the three
Poisson transformations. `ChenGuptaLiWeightedCubicDiagonal.lean` now evaluates the all-equal part
exactly and proves it is precisely the centered trace subtraction. The centered cubic trace is
therefore not merely split: it equals the literal not-all-equal weighted correlation sum.
`ChenGuptaLiSmoothBump.lean`, `ChenGuptaLiHZero.lean`, and `ChenGuptaLiHt.lean`
construct the literal compactly supported Schwartz kernels; `ChenGuptaLiSchwartzFourier.lean`
supplies repeated-integration-by-parts Fourier decay; `ChenGuptaLiRamanujanFourier.lean` gives the
exact reduced-residue finite Fourier identity; and `ChenGuptaLiAffinePoisson.lean`
proves affine residue-class Poisson summation, the additive-character form, and justified
finite/infinite interchange for the reduced-residue sum. Thus diagonal cancellation, literal
Schwartz input, and affine/reduced-residue Poisson mechanics are closed.

Remaining finite-to-global burden is an actual conductor-uniform estimate of the transformed
not-all-equal weighted six-label correlation and its large-height aggregation. Corpus does not
prove that estimate, remote contour passage, or absolute zero census.

T1's full exact-multiplicity Mellin zero packet tends to zero after its physical normalization.
This does not bound the unweighted number of detector or off-line zeros in a fixed rectangle: the
kernel and normalization can suppress a finite defect. HC therefore still needs an absolute census
or a subquantum source bound; importing the normalized Route-T limit would be a category error.

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
`HedenmalmExteriorSourceThetaBoundaryGap.lean`,
`ChenGuptaLiWeightedCubicDiagonal.lean`, `ChenGuptaLiAffinePoisson.lean`,
`ChenGuptaLiRamanujanFourier.lean`, and `ChenGuptaLiHt.lean`.

**Open core.** Prove from coefficient-faithful prime--Gamma source, before divisor specialization,
either an absolute strict-subquantum bound for source excess/information loss on all late windows or
prime-summability of the literal paired Gamma-six suspension determinant current; equivalently the
CGL branch needs a conductor-uniform bound for the exact not-all-equal weighted six-label
correlation after affine reduced-residue Poisson transformation, plus large-height aggregation
strong enough to eliminate every off-line fibre.
Normalized
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

### TTF presentation of CLG/TTF

TTF is the literal theta-correlation presentation of the CLG/TTF architecture, not an independent
live route. `ThetaTiltFluxCarrier.lean` identifies neutral tilt derivative with the source
Bezoutian. `ThetaCuspTiltFluxSourceWeld.lean` constructs the completed theta-cusp source and proves
its all-plane bilateral Laplace transform is `xiCent`.
`ThetaCuspTiltFluxObservabilityWeld.lean` then proves universal theta-flux nonnegativity equivalent
to universal Euler-safe observability-deficit nonnegativity by the invertible coefficient rescaling
`c_j -> c_j xiCent(w_j)`. `ThetaCuspTiltFluxHedenmalmWeld.lean` identifies scalar flux with the
Hedenmalm transverse current and proves every one-mode packet nonnegative on `Re w>=1/2`.
`ThetaCuspTiltFluxWeilParityWeld.lean` identifies same flux with reflection-even minus
reflection-odd two-channel energy, and `ThetaCuspTiltFluxWeilParityEulerRayWeld.lean` proves every
complex two-mode packet on two ordered positive Euler-ray nodes nonnegative.
`ThetaCuspTiltFluxWeilParityCauchyLocalization.lean` then proves regular two-Cauchy parity order
already equivalent to RH and localizes every off-line fibre by `(even,odd)->(0,N)`.
`ThetaCuspTiltFluxWeilParityCauchySourceEscape.lean` realizes same sequence in continued source and
proves its source energy tends to `-N`.

The shared open core is therefore arithmetic exclusion of this cofinal reflection-antisymmetric
rank-two source escape. It cannot be
replaced by a generic local-shape theorem: `ThetaSourceStrictLogConcavityFluxNoGo.lean` exhibits a
positive even superexponentially decaying strictly log-concave source with negative one-mode flux in
the open right half-plane.

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
`XiBezoutianPointedIncidence.lean` then closes the centered pointed geometry. The trace-cleared
Bezoutian extends entire across its antidiagonal, equals the `c=0` translated-Xi Bezoutian, is a
diagonal congruence of CLG's critical kernel, and equals W2C's completed even--odd Weil Gram with an
explicit multiplicity-exact divisor expansion. Its finite-packet PSD is exactly RH. Under RH the
two entire divisor-feature channels form a positive Gram sum; conversely, any Hilbert-space Gram
factorization by source-defined vectors proves RH, with finite-packet compatibility automatic.

**Open core.** Construct source-defined Hilbert vectors whose Gram kernel is the pointed entire
Bezoutian, or otherwise derive its global positivity from literal completed prime--Gamma source
before selecting a zero. Existing feature vectors are divisor-indexed and their Gram identity uses
RH; using them forward is circular. UEB is therefore a genuine nonphysical infinite-kernel
candidate, now explicitly source-isogenous to CLG/W2C as well as C1/Q/G, but not a live producer.

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

- **W2C (two-channel Weil resolvent/aperture)** is a cross-route bridge, not a new route.
  `XiWeilTwoChannelResolvent.lean` identifies CLG's exact critical kernel with even plus odd Weil
  resolvent Gram channels and with its safe Euler--Gamma entry. `XiWeilApertureChannels.lean`
  supplies compactly supported two-sided exponential Fourier realizations, dominated convergence,
  finite-packet energy convergence, eventual finite-aperture survival of every negative packet,
  and the exact equivalence `RH iff every nonnegative-aperture packet energy is nonnegative`.
  `XiBezoutianPointedIncidence.lean` clears the Xi trace to an entire antidiagonal-removable
  Bezoutian, proves it is simultaneously UEB's marked-origin kernel, CLG's diagonal congruence, and
  W2C's completed Gram, and reduces a forward proof to a source-defined Hilbert Gram factorization.
  `XiBoundaryPoissonDensity.lean` gives an exact safe-boundary model: for every `a>1/2`, the real
  completed logarithmic derivative is a convergent sum of positive upper-half-plane Poisson
  kernels at the reflected divisor heights, and W2C's even channel is exactly the paired Poisson
  contribution. The densities at every safe offset form one Poisson semigroup orbit.
  `XiBoundaryCauchyRepresentation.lean` evaluates each divisor term against the boundary Cauchy
  product kernel, proves summability of their integral norms, and sums them to the exact boundary
  Cauchy representation of the safe Caratheodory kernel. `XiEulerSafeObservability.lean` separately
  forms every finite-packet amplitude and tail amplitude, proves all integrals converge, and shows
  their observability deficit is offset-independent and exactly `pi` times CLG's critical kernel
  energy. Universal complex or real deficit nonnegativity is exactly RH.
  `XiDePoissonizedStationarity.lean` proves that inverse Poisson conjugation removes offset from
  each von--Mangoldt atom. No source-built deficit inequality is proved. These facts
  explain safe-half-plane positivity but do not
  orient horizontal divisor displacement: off-line zeros still contribute positive kernels there,
  and the density construction is divisor-indexed. Critical limiting domination remains producer.
  This closes receiver matching among UEB/CLG/Q and finite-aperture restricted-Weil branches O/SV2,
  but not the producer: the aperture form is defined using the actual Xi-divisor polarization.
  `XiWeilCarrierBudget.lean` adds the exact rational independence and span dimension
  `dim_Q span{log p:p<N}=pi'(N)`; under a proposed finite-boundary resource inequality, its
  complementary arithmetic module must carry the corresponding prime-rank deficit. It is a
  carrier-size constraint, not a proof that any proposed resource decomposition exists.
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
  completed source form. `HTGeometry/GammaProductRootLaw.lean` and
  `RHTower/SelbergCuspArchimedeanRoot.lean` further prove exact finite Gamma-product root
  asymptotics and identify the Selberg archimedean root constant with its cusp parameter.
  `SelbergShiftRootLaw.lean` completes full functional-equation assembly: along degree-normalized
  shift lattice, factorially normalized value has root limsup exactly
  `conductor^(1/degree)/(2*pi*degree)` off exceptional sine lattice.
  `SelbergRankOneSineFactor.lean` makes sine hypothesis automatic for every half-rate/rank-one
  presentation by period-four recurrence and a nonvanishing sine/cosine pair. This is a new exact
  cusp--spectrum radius law for extended Selberg class, but it measures gamma/conductor data rather
  than horizontal zero location. It broadens completed-family infrastructure without specializing
  a zeta source order or creating an RH route. `ZetaChiVerticalGrowth.lean` now proves the global
  polynomial chi majorant on every whole vertical line with `sigma in [-1,1/2]`; this closes T1's
  corresponding archimedean contour input, but supplies no signed short Möbius-block estimate.
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
  `DirichletCharacterFundamentalDiscriminant.lean` and
  `DirichletCharacterFundamentalDiscriminantKronecker.lean` prove the conductor-four and both
  conductor-eight CRT discriminants are fundamental and identify their characters with the literal
  Kronecker symbol. Bondarenko--Heap Lemmas 4, 7, 8, and the expanding Lemma-9 layer now formalize
  finite Fourier completion, inverse-incidence fibre energy, source-scale discriminant-window
  estimates, exact local Jacobi/Ramanujan factorization with square-root residual-core control, and
  premise-free source-scale summation of the literal exceptional additive-Ramanujan mass.
  These remain finite/cofinal correlation inputs toward E/T, not conductor-uniform density or their
  signed critical cancellation.
- `EulerCharacterGroupCompletion.lean` completes the positive Euler Dirichlet monoid to the
  positive rationals. Functional-equation reflection is group inversion; same-half modes are
  isotropic for the constant-term scale-residue pairing, while every nontrivial mode pairs
  nondegenerately with its reflected inverse. This is a literal infinite, paired, nonphysical Euler
  seam, but it has neither a completed Xi-divisor landing nor a source law forcing a critical-line
  invariant. It is pre-route infrastructure for G/L/C1, not a new route.
- `StokesChamberGermReconstruction.lean` proves the reflected Poisson--Boolean boundary rate pair
  recovers the full Stokes parameter and its sharp prime-valuation coenergy asymptotic. Thus this
  boundary germ is coefficient-faithful, not information-depleted. It still detects every chamber
  rather than selecting the centre. `ShiftedEulerQuotientCocycleFlatness.lean` proves the opposite
  limitation: the uncompressed full-shift Euler quotient is an exact positive twisted coboundary
  with identically zero associativity curvature. Any C1 successor must retain compressed Schur or
  boundary curvature; the flat quotient itself cannot supply it.
- `ThetaCarrierHassePacket.lean`, `FermiMellinObserver.lean`,
  `FermiMellinPhaseProperness.lean`, `HasseSondowRowMellin.lean`, and
  `EulerValuationLorentzLog.lean` add three exact nonphysical detector interfaces. The literal theta
  tilt law lifts through its Hasse recovery isometrically; reflected work vanishes exactly at the
  centre, but information neutrality itself selects nothing. The positive Fermi--Mellin observer has
  completed eta quotient as characteristic exponent, so every nontrivial zeta zero gives exact
  phase orthogonality and a variance lower bound. The completed local Euler valuation tower is a
  Lorentz logarithm whose odd coordinate vanishes exactly on the critical line, but the logarithm
  exists at every strip point. These are source/detector and rigidity bridges, not new routes: none
  gives a global pre-divisor law excluding the off-line orthogonality or forcing the odd coordinate
  to vanish on every Xi divisor.
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
- `PrimeLogActionCondensation.lean` opens **PLAC**, an infinite prime-log action-condensation
  pre-route. Depth reciprocal zeta is exactly `1/zeta(ms)`; squarefree action increments retain
  every coefficient; diagonal blow-up converges to the normalized Euler logarithmic connection;
  completed blow-up gives `-u xi'/xi`; and its residue at a divisor of multiplicity `d` is `-d`.
  Every squarefree action coefficient is asymptotically recoverable. This supplies PBM/G/L/T with a
  coefficient-faithful depth connection and multiplicity charge, but not an upstream global law
  forcing that charge to vanish or orienting it before divisor selection. PLAC is therefore a
  genuinely new corpus-born mechanism, not yet a candidate or live route.
- `WeightedLaplaceShift.lean` and `EulerPositionCommutator.lean` open **EPC**, an operator
  pre-route. Weighted Laplace shifts have exact norm scale, prime monomials have norm `n^(-1/2)`,
  aperture cutoffs are literal orthogonality, and accretivity is the CLG critical
  logarithmic-derivative kernel after the half shift. The Euler-position commutator produces the
  Hermitian prime contribution with orbital lengths, while projection compression splits exactly
  into internal anomaly plus polarized boundary leakage. EPC explains why diagonal/scalar
  compression loses the missing mixed incidence and connects CLG to CCM-FU/G/L. It has no
  independent completed source order or RH endpoint beyond those routes, so it is a pre-route, not
  an additional live architecture.
- `AllGradePrimePowerCorona.lean` closes **AGC** negatively as an independent selector in the
  logarithmic Marcinkiewicz topology. Grade-one embedding is isometric and projection contractive;
  higher nonlinear Euler grades have uniformly bounded mass and vanish in the quotient; the unit
  all-grade ray has quotient one; every positive off-line shift ray has quotient zero even with all
  grades retained. The tangent version is equally rigid: all tangent grades are controlled by the
  grade-one mass and the higher tangent tail vanishes. Thus nonlinear completion does not restore
  orientation or monodromy erased by grade-one passage. Positive survivor is an exact
  grade-one-retract/classification theorem. Any successor must change topology or retain a singular
  graph, boundary, or infinity-sensitive invariant; it is not unfinished AGC.
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
  Hodge operator equal to positive facet multiplicity. Super-Poincare and BPS modules now extend
  far beyond that finite example: they package reflection, differentiation, cofinal prolongation,
  Deninger inversion/Hodge, Gamma--Stokes, chiral blocks, holonomy, spectral gaps, and many literal
  Xi energies into exact paired first-order decompositions. `SuperPoincareProjectionPhase.lean`
  and `SuperPoincareProjectionFamily.lean` give a concrete Pauli projection, differentiable
  oblique-idempotent shear, nilpotent normal corner, and exact BRST Hodge--Dirac/Hamiltonian.
  `SuperPoincareCochain.lean` packages the actual Deninger total differential and parity as a closed
  `D=1,N=2` split; `SuperPoincareQ8OddClifford.lean` constructs a nontrivial arithmetic quaternionic
  `N=2` algebra on the odd central sector. These are exact algebraic realizations, not the missing
  semilocal source or singular landing. In particular
  `xiRadialJensenBPSSaturation_iff_rh` and `wardGreenProjectionBPSSaturation_iff_rh` show that RH is
  BPS saturation for two existing receivers. This is a useful unification and exposes the common
  positive defect, but does not force saturation. Generic block factorization can package any ring
  factorization into a closed chiral sector, so Super-Poincare structure alone is not a producer.
  `SuperPoincareXiCliffordEndpoint.lean` makes the terminal point exact: existence of the bare
  reciprocal-Xi Clifford splitting is equivalent to RH. No route is added.
- `HTGeometry/Sl2ElementaryFactorization.lean` reduces every determinant-one two-by-two matrix to
  four elementary unipotents. `Sl2CocycleUpperEntry.lean` then proves a derivation-like cocycle's
  regular lower-left entry vanishes on the upper unipotent subgroup over an algebraically closed
  characteristic-zero field. This is both projective adapter and rigidity firewall for U/Q/UEB/HJ:
  a viable cocycle invariant must be singular, global, or boundary-valued, not a regular one-entry
  certificate.
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
  mixed channel. `EulerFisherPoincareBoundary.lean` now gives this phase-free
  geometry an exact source-side normal form: Euler moments determine a globally negative conformal
  curvature with Poincare limit `-2` as `beta -> 1+`. This sharpens the universal boundary geometry
  but remains blind to completed reflection and horizontal Xi divisors, so it is not a route.
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
  contraction from a Pick identity; `HTGeometry/TransferFunction.lean` realizes every
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
  generic group carriers. `HTGeometry/BurnsideTwoByTwo.lean` supplies the exact
  irreducible two-dimensional matrix-algebra step. `HTGeometry/DifferenceSemiInvariantSolution.lean`
  proves that a tensor-square semi-invariant line in a sigma-simple Picard--Vessiot ring forces a
  base Riccati solution, sharpening the difference-Galois obstruction to stable lines.
  `HTGeometry/TorsorSpecializationSeparation.lean` proves all algebraic torsor specializations
  jointly separate points and turns specializationwise proportionality into tensor-square
  symmetry, closing the abstract input used by that Riccati reduction. None is specialized to
  completed arithmetic source or connected to an RH reader, so they remain infrastructure rather
  than PPM/IRK/HJ/AF promotions.
- `HTGeometry/LSeriesRightLimit.lean` proves a polynomial-growth Dirichlet series tends
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
  `MultipleGammaCyclotomicDeletionMultiplicity.lean` computes exact
  differential-algebraic/hypertranscendental multiplicities after cyclotomic period deletion.
  The labelled coset-face system now adds disjoint packets, faithful translate parametrization,
  structural translation automorphisms, descending layer gluing, no simultaneous telescoper,
  joint independence of every proper face packet, arbitrary-translate deep-span reduction modulo
  differential-algebraic error, and the complete differential matroid with exact two-survivor
  algebraic/hypertranscendental boundary (`MultipleEllipticGammaCoset*.lean`). The all-depth
  extension is complete internally. Pair-face signature vanishes exactly on differential-algebraic
  members (`AllDepthCompleteness.lean`). `AllDepthUniversalCarrier.lean` supplies the actual
  multiple-elliptic-Gamma carrier and identifies its bottom witness with a translated theta
  logarithmic derivative. Its translated jets realize every finite bounded-order bottom divisor
  (`AllDepthCarrierJets.lean`), simultaneous lifts preserve complete prescribed data, and every
  class member has a cyclic normal form modulo differential-algebraic error in the span of those
  jets (`AllDepthCarrierSpan.lean`, `AllDepthNormalForm.lean`). `AllDepthExactImage.lean` closes the
  internal image problem: every compatible family of finite class divisors is realized by a class
  member. Thus neither local divisor pattern, admissible bottom charge, compatible finite-depth
  signature, nor more depth can select the arithmetic carrier; only global mixed compatibility can.
  This defines pre-route **MEG**. Its internal elliptic-Gamma classification is
  closed under integral period independence and coset separation. Open core is external: instantiate this system on literal
  completed prime--Gamma/Möbius source and provide a coefficient-faithful Xi reader whose selected
  invariant excludes off-line divisor. No present theorem supplies either handoff or an RH endpoint.
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
- Place-peel and shear-degree modules now prove a genuine valuation-theoretic border law: the newest
  logarithmic-factor column retains polynomial degree while every lower border entry vanishes, and
  a fixed shear bounds twisted matrix-chain degree by its spread.
  `ShiftedTopMatrix.lean` further makes shifted leading matrices multiplicative and proves exact
  linear chain growth whenever their accumulated leading product is nonzero (`PlacePeelColumn.lean`,
  `PlaceShiftIterate.lean`, `ShiftedMatrixDegree.lean`). `RationalMapComposition.lean` supplies
  degree-controlled rational iteration and preserves noncriticality/deck descent through every
  iterate. These are source-independent
  differential/formation laws; no theorem specializes the place, shift, or border residue to the
  completed prime--Gamma source or reads an Xi divisor. They strengthen MEG/difference-Galois
  formation infrastructure but do not create a route.
- `HTGeometry/MarkedWordRealization.lean`, `CommonTimeCircuitHardness.lean`,
  `GateWordCommonTimeHardness.lean`, `RationalCommonTimeWitness.lean`, and
  `CapacityIncubationInstantiation.lean` give exact finite marked-presentation uniqueness,
  common-time hardness against every bounded gate-word dictionary, positive-mass rational-time and
  rational-coefficient witnesses, and a fully instantiated delayed-capacity law.
  `GateWordDictionary.lean` makes the word/gate interpretation literal, and
  `GaussianIntegerPauliModel.lean` further descends every rational-coefficient finite Pauli
  Hamiltonian to one rational scalar times a Gaussian-integer matrix.
  `ExponentialFactorialRemainder.lean` supplies an exact Banach-algebra truncation certificate:
  beyond twice the norm bound, the exponential remainder is at most `2 b^N/N!`.
  `RationalOrbitCertificate.lean` constructs the exact rational truncated Pauli orbit, a decidable
  rational `HardCertificate`, and the certified flow-to-truncation error; it proves both soundness
  into the abstract hard-circuit event and finite-precision completeness for every genuine strict
  hard witness. Their target action and spectral dictionary are
  abstract and finite; no prime--Gamma occurrence or Xi reader exists. They are nonclassical
  action/rigidity mechanisms, not RH candidates.
- Finite quantum-channel diamond contraction and Markovian return recovery are now exact, including
  ancilla-assisted information-loss and inverse-word incidence reflection
  (`QuantumChannelDiamond.lean`, `MarkovianReturnRecovery.lean`). Exact return is rigid: every
  intermediate channel is unitary conjugation, the semigroup is periodic, and incidence counts are
  palindromic (`ChannelInverseRigidity.lean`, `MarkovianExactReturn.lean`). Thus genuinely
  dissipative exact-return variants are closed. `StaticChoiPhaseTargetEntropy.lean` and the static
  Choi first-return modules add basis-free phase-target entropy, finite circuit-dictionary union
  bounds, Gaussian crowding bounds, and return-excised hard-gap laws. They still assume an abstract
  spectral target/action and contain no prime--Gamma specialization. Approximate-return information loss remains a
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
  and full several-variable pencil forms are formal. `PencilDeterminantCompletion.lean` identifies
  the multivariable graph set exactly as regularized determinant times every admissible low-degree
  polynomial jet, while `DeterminantGraphLocallyUniform.lean` turns locally uniform graph
  convergence into coefficient convergence. Pencil micro-block, moment realization, and
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
  or RH reader. `HTGeometry/AppellHumbertAutomorphicFactor.lean`,
  `HTGeometry/AppellHumbertGaussianBound.lean`, `HTGeometry/PoincareTermAppellHumbertDecay.lean`,
  and `HTGeometry/PoincareTermJetGrowth.lean` add the exact automorphic factor and inverse Gaussian
  bounds. The latest decay theorem corrects the complement-translation interface: a seed automorphic
  only under the smaller period group cannot be pulled back along a complement translate. The
  valid global hypothesis is bounded normalized modulus
  `|seed(y)| exp(-(pi/2) Re H_l(y,y))`, from which the Gaussian term and jet bounds follow.
  `HTGeometry/AbePositiveGaussianMajorant.lean` proves the coercive bridge: coordinate Abe
  positivity is a positive-definite real Gram condition and makes the form Gaussian dominate a
  coordinatewise lattice Gaussian, including jet damping. `HTGeometry/AbePoincareLocalNormal.lean`
  uses this majorant to prove local normal convergence of the literal complement Poincare series,
  while `HTGeometry/AbeDampingBoundBridge.lean` proves the packet-jet damping bound and exact
  Appell--Humbert factor compatibility under that normalized-modulus hypothesis.
  `HTGeometry/AppellHumbertNormalisedModulus.lean` proves normalized modulus is invariant under the
  actual period group and globalizes any bound from an orbit-meeting set;
  `PoincareTermPolynomialSeed.lean` proves Gaussian decay absorbs every polynomial seed loss; and
  `AppellHumbertJetAmple.lean` closes the former finite-vanishing seed gap by proving one fixed
  positive Appell--Humbert factor interpolates every finite mixed-jet packet. Positive
  Appell--Humbert normal convergence, damping, and all-order finite jet interpolation are therefore
  no longer open. This strengthens quasi-abelian/MEG carrier formation, but still supplies no
  completed arithmetic occurrence, functional-equation action, or Xi reader. It creates no RH
  route and does not revive AP or AF; their terminal obstruction is arithmetic
  specialization/receiver action, not finite jet ampleness.
- `ArbitraryLabelEndReconstruction.lean` removes the finite-label hypothesis from one-ended
  coherence reconstruction: on an infinite preconnected finite-boundary one-ended graph, any
  arbitrary-type label with finitely many changing edges is constant off a finite vertex set. This
  strengthens a global-coherence receiver, but the corpus supplies no literal completed-arithmetic
  graph whose finite variation or end value yields an RH orientation; it is not a new route.
- `HTGeometry/ClosedRangeTransgression.lean` identifies closedness of a composite with closed range
  plus closed kernel and with closedness of its transgression. For a finite history, global
  properness is equivalent to closedness of every prefix transgression; terminal closedness alone
  does not imply it. `ClosedRangeTransgressionCountermodel.lean` realizes failure
  explicitly on an `ell^2` decaying diagonal: two closed subspaces have nonclosed sum, while adding
  a terminal zero map restores closed final range. `LawHistoryTransgressionPages.lean` identifies
  exact kernel and cokernel pages and finite-dimensional alternating-sum conservation.
  `FiniteLawHistoryMachine.lean` now assembles every finite history into exact page differentials,
  reconstructs total kernel and cokernel from stable survivor filtrations, and proves total
  transport is bijective exactly when every stable kernel and cokernel survivor vanishes. This is a precise warning for L/G/P: an endpoint landing or closed terminal
  range cannot replace the missing source-derived singular comparison across every relevant
  prefix. `HTGeometry/AbelianRepairLeastAction.lean` separately proves reduced-Laplacian
  positivity, minimum principle, least action, termination, positive Green inverse, and exact work
  recurrence for finite sink-connected repair systems. It supplies a nontrivial SFP/IRK-style
  action mechanism, but no prime--Gamma source, Xi receiver, or cofinal infinite law; no route is
  added.
- Working-tree `CompleteHistoryInvariantMetricCone.lean` classifies every positive invariant metric
  for a finite transport history as a fixed invariant metric multiplied by a positive
  self-adjoint commutant factor; scalar-ray uniqueness is exactly absence of nonscalar such factors.
  This sharpens metric-selection language for G/L/P but supplies neither arithmetic transport
  occurrence nor orientation of its commutant cone. It is not a new RH route.
- Working-tree `GoldenRuleKernel.lean` and `GoldenRuleSincIntegral.lean` close the continuum
  first-order resonance kernel: it is nonnegative, integrable, exactly a squared transition
  amplitude, and has total mass `2*pi*t`. Without a literal prime--Gamma spectral measure and an Xi
  collision/position reader this is universal analytic infrastructure, not an HC producer or a new
  route.
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
  nonzero at the center. `CompactConnectedAbelianGenerators.lean` proves compact
  connected abelian groups are divisible and almost every element is a topological generator.
  `CompactGroupCoveringVolume.lean` adds the exact Haar-volume/covering-number sandwich, making the
  associated quantitative return scale explicit. `CompactGroupMinimaxReturn.lean` combines it with
  dense-generator avoidance: universal return deadline is controlled by covering number, while
  some dense generator avoids the target through every time allowed by its Haar-volume budget.
  Abundant dense or quantitatively recurrent orbits
  therefore do not repair the screen obstruction. Thus prime phases alone cannot perform completion; a successful AF/G/MSC
  screen must retain noncompact archimedean data, be singular/unbounded, or leave this class.
- Sieve mean-value, divisor-moment, exceptional-set, and Halasz--Montgomery modules close exact
  analytic adapters used in long chains (`Sieve/DivisorMomentMeanSquare.lean`,
  `Sieve/HalaszMontgomeryIntegral.lean`, `Sieve/Section4Core.lean`). The reciprocal Kuzmin--Landau
  chain now replaces the fatal uniform `N|E|` kernel cost by explicit
  `N log T + |E| sqrt(T) log T` row mass (`Sieve/LogPhaseKernelKuzminLandau.lean`,
  `Sieve/PlainKernelRecip.lean`, `Sieve/KernelRowMassRecip.lean`,
  `Sieve/PlainKernelMassRecip.lean`, `Sieve/LogPolyWindowHMRecip.lean`).
  `Sieve/RamareLadderHMRecip.lean` and the ladder aggregate/group modules carry it through actual
  Ramaré blocks and express group cost using harmonic mass, maximal block, and prime count. This is
  a real closure of E/T exceptional-set machinery. Capstones still retain pointwise block,
  ladder-error, relation-specific head, and signed-current
  premises; they neither define E's fixed relation nor prove T1's short Möbius-block cancellation.
  `Sieve/ShortExceptionalMeasure.lean` additionally removes block-cardinality loss from the
  free/relative/maximum-threshold exceptional-measure budget; this closes exceptional measure as an
  independent E axis, not the fixed-relation theorem.
  The level-4/8 Bondarenko--Heap source factorization and finite Chen--Gupta--Li detector product
  now extend through the exact primitive Class-I/Class-II zero alternative, natural common-prefix
  fibres, source-correct separation, exact second/fourth-moment expansions, and finite large-value
  reductions to divisor-square energy or a sampled fourth moment. Finite nonprincipal charge is
  zero and principal translated-pole charge is explicit. Missing input is no longer the analytic
  alternative or packet formation; it is the refined large-height conductor-uniform correlation,
  fourth-moment, and zero-density estimate needed for HC's absolute census.
  `Sieve/TwoRangeSchedule.lean` fixes the intended low/high
  parameters and basic limits, while `Sieve/PrimeRangeLogLogMass.lean` gives the wide-range
  harmonic upper bound. `Sieve/TwoRangeLimits.lean` closes the elementary asymptotic absorption of
  fixed log-log powers by negative log powers and of log-log factors by the zero-free-region
  exponential. `Sieve/TwoRangeScheduleFacts.lean` additionally closes range coverage, ladder tops,
  nonempty high cofactors, and low harmonic mass. `Sieve/TwoRangeMajorant.lean` proves the complete
  five-term relative majorant decays after logarithmic scaling under two explicit zero-free/high-base
  limits. `Sieve/TwoRangeRouteT.lean` installs the concrete contour parameters and closes the
  block-top, width, threshold, and disc-containment conditions. None proves E's relation-specific
  group/head law, T1's signed current, or HC's global detector inequality.
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
- The ABHN files now supply Brauer-quotient/scalar-extension/tensor-product foundations,
  algebraically closed local invariant triviality, place carriers, and an exactness specification;
  `ABHN/CentralSimpleAzumaya.lean` and `ABHN/AzumayaBaseChange.lean` add
  central-simple-to-Azumaya, enveloping-action, and Azumaya base-change laws. Local scalar
  extension is injective, finite-dimensional, simple, and central for the proved central-simple
  input. `ABHN/AzumayaTensorProduct.lean` proves tensor closure of Azumaya/central-simple carriers
  and commutative associative tensor addition with split identity on the Brauer quotient;
  `ABHN/BrauerGroupStructure.lean` adds opposite-algebra inverses and the full commutative group
  structure. `ABHN/ScalarExtensionBrauer.lean` proves represented scalar extension is well-defined
  on that quotient, and `ABHN/ScalarExtensionTensorProduct.lean` makes it an additive homomorphism.
  Local scalar extension is additive placewise. `ABHN/RestrictedBrauerGroup.lean` equips the
  finite-nonsplit-support local families for number fields and rational function fields with their
  commutative group structures. Complex infinite completions are proved split and absent from
  nonsplit support; their local invariant is zero. `ABHN/RestrictedInvariantSum.lean` supplies the
  exact restricted-sum interfaces once local invariants and localization are available. It does not
  prove finite ramification, the real-place or nonarchimedean `Br(K_v)=Q/Z` invariants, or global
  number-field ABHN exactness. `ABHN/RationalFiniteLocalField.lean` now packages every finite
  completion of `Q` as a nonarchimedean local field, closing that type-level local-field bridge but
  not its Brauer invariant isomorphism. `ABHN/LaurentSeriesFiniteLocalField.lean` and
  `ABHN/RationalFunctionFiniteLocalField.lean` likewise prove `F((X))` and every finite completion
  of `F(t)` are nonarchimedean local fields with finite residue fields and Henselian valuation
  rings. `ABHN/RationalFunctionInversion.lean` constructs the algebra automorphism `t |-> t^(-1)`
  and proves its action on both coordinates. `ABHN/RationalFunctionInfinityValuation.lean` further
  proves inversion identifies the infinity valuation with the `X`-adic valuation up to valuation
  equivalence. `ABHN/ValuationCoordinateTransport.lean` upgrades transported valuation
  equality to uniform equivalence; `ABHN/RationalFunctionInfinityUniform.lean` applies it after
  coordinate inversion; and `ABHN/RationalFunctionInfinityCompletion.lean` uniformly identifies
  the infinity completion with Laurent series and packages it as a nonarchimedean local field.
  Thus algebraic, valuation, uniform, and completion-level finite/infinite-place comparison are
  closed. `ABHN/HasseMatrixRanks.lean`, `HasseMatrixNilpotence.lean`,
  `HasseMatrixCharpolySeparable.lean`, `HasseMatrixTriangular.lean`, and
  `HasseMatrixIsometries.lean` add local detection of rank, nilpotence, separable characteristic
  polynomial, triangular form, and form-preserving/infinitesimal isometries over every completion.
  `HasseClassicalMatrixGroups.lean` extends this to orthogonal, special-orthogonal, and symplectic
  group membership; working-tree `HassePolynomialCoprime.lean` adds coprimality of polynomial pairs.
  These close function-field local-field and elementary matrix-detection bridges, not finite
  ramification, local Brauer invariant isomorphisms, or global ABHN exactness.
  `ABHN/RealQuaternionCSA.lean` constructs the real Hamilton
  quaternions as a finite-dimensional central simple algebra and proves their Brauer class is
  self-opposite and two-torsion; it does not classify the entire real Brauer group.
  `ABHN/HasseAlgebraCommutativity.lean` proves commutativity is reflected by scalar extension,
  hence a number-field or rational-function-field central simple algebra is commutative exactly
  when all its completions are; in the same-universe case, a nonsplit class yields an explicit
  noncommuting pair at some place. `ABHN/HasseMatrixNilpotence.lean` similarly proves nilpotence of
  a square matrix is reflected by coefficientwise field extension. These are local detection theorems strictly weaker than local
  Brauer invariant isomorphisms or ABHN exactness.
  `ABHN/RestrictedInvariantSurjectivity.lean` constructs one-place
  sections for number fields and rational function fields, proves that restricted invariant summation
  recovers the selected local invariant, and transfers one local surjectivity hypothesis to the
  restricted global sum. This closes the formal one-place section/sum calculation, not those missing
  local invariant isomorphisms or ABHN global exactness.
  Separately, `MilnorPolynomialTotalResidue.lean` and
  `MilnorPolynomialGlobalReciprocity.lean` prove the finite-place short exact sequence for `F(t)`,
  the finite-plus-infinity reciprocity law, and the projective-line Hasse exact sequence.
  `MilnorPolynomialGlobalReciprocityQuotient.lean` identifies Milnor classes modulo constants with
  all finite-plus-infinity residue profiles satisfying the global norm-sum-zero law. No
  RHTower theorem identifies these Milnor/ABHN carriers with completed Xi source or the Route-L
  physical reader. `DeningerKummerReciprocityQuotient.lean` identifies global units modulo roots
  of unity with their realized product-formula-current range, not the whole abstract kernel. These are local-global infrastructure, not C1/L route
  closure. HLS Fock, kinematic, physical-assumption, and finite-scattering modules likewise
  construct unconditional algebraic interfaces and examples but explicitly prove no interacting
  QFT model, classification, prime--Gamma occurrence, or Xi landing. They are general foundations,
  not RH routes.
- `EulerSupportEnergyUncertainty.lean` proves a weighted Holder law for logarithmic Euler
  discrepancies: an `ell^q` energy abscissa `sigma_q` and prime-support exponent `delta` force
  absolute convergence beyond `sigma_q + delta/q'`. Reflection then bounds any divisor's transverse
  position by same budget. With uniformly bounded prime-power traces, every depth at least two is
  already absolutely convergent for `Re(s)>1/2`; only ordinary-prime traces can obstruct critical
  line. This is a useful cross-route constraint for D2, T2, F2, and HC: a proposed energy route must
  pay for prime support and cannot hide critical obstruction in deep prime powers. It is not a new
  route because corpus does not identify a literal completed Xi discrepancy whose independently
  proved energy/support budget reaches `1/2`; the position clause alone is a generic reflection
  inequality, not a source-to-RH chain.
- `EulerFisherPoincareBoundary.lean` identifies the literal zeta Euler Fisher metric on `beta>1`:
  scalar curvature is strictly negative and tends to `-2` at pole, so temperature-clock surface is
  asymptotically Poincare. This closes Fisher boundary geometry but retains only positive
  prime-power moments and no horizontal phase, completed reflection orientation, or Xi-divisor
  reader. It is therefore geometric infrastructure, not a new route and not a revival of AF.
- `ReductionPencilKPositivity.lean` and `AmplifiedAdmissionGauge.lean` prove finite-level complete
  positivity calculus, data processing, exact reduction-pencil gauge `min(k,n)`, complete gauge
  `n`, and migrating-depth/false-promotion laws. `AllDepthMixedConstraintClass.lean` defines the
  iterated mixed-difference germ class, identifies its two-parameter case with the triptic class,
  and proves one difference lowers depth. `AllDepthMeroClass.lean` realizes the meromorphic germ
  class and transports translations/periodicity. `AllDepthPairFaceSignature.lean` and
  `AllDepthBottomCharge.lean` add a depth-two face obstruction and finite-support elliptic-quotient
  charge whose orbit sum is that obstruction; vanishing charge gives descent.
  `AllDepthTelescope.lean`, `AllDepthSignatureDescent.lean`, and `AllDepthAtomRealization.lean`
  close finite difference-cube reconstruction, one-depth signature descent, and arbitrary local
  differentially-algebraic atom realization. `AllDepthBottomRealization.lean` strengthens this to
  every finite-order elliptic-quotient bottom charge satisfying transverse line-sum zero: one finite
  multi-order differentially-algebraic atom sum realizes the complete prescribed charge. The
  converse is closed by `AllDepthCompleteness.lean`: vanishing pair-face signatures characterize
  differential algebraicity. `AllDepthUniversalCarrier.lean`, `AllDepthCarrierJets.lean`,
  `AllDepthCarrierSpan.lean`, and `AllDepthNormalForm.lean` provide the universal
  multiple-elliptic-Gamma carrier, theta bottom witness, arbitrary bottom-divisor jet realization,
  and cyclic normal form modulo differential-algebraic error. `AllDepthExactImage.lean` proves its
  exact image is every compatible family of finite class divisors. Consequently neither more depth,
  one local principal-part pattern, an admissible bottom charge, nor a compatible finite-depth family can select the arithmetic
  carrier; only global mixed compatibility can. These close MEG's internal classification but remain universal obstruction/selection mechanics;
  absent a literal prime--Gamma/Möbius occurrence and Xi reader they change no RH route.
- `HalfPlanePoissonKernel.lean` closes normalized half-plane Poisson mass, shifted products, odd
  primitive, and boundary limits. `XiBoundaryPoissonDensity.lean` specializes it to the exact safe
  completed log-derivative density and W2C's paired even channel. Positivity is automatic there but
  divisor-indexed and insensitive to horizontal orientation, so it is a W2C/CLG bridge rather than
  a producer. `KLFactorizationSufficiency.lean` proves exact data processing
  and scalar sufficiency for factored likelihood ratios and Esscher families. These are clean
  analytic/information-geometric adapters. `EsscherFormationChirality.lean`,
  `ExponentialFormationResponse.lean`, `PositiveJumpFormationChirality.lean`, and
  `GeometricModeChirality.lean` compute exact oriented higher response laws.
  `AbelianZetaGasModeChirality.lean` sums them over every prime-depth mode, proves strict source
  chirality, and reconstructs complete order of admitted chemical potentials.
  `AbelianZetaGasDirectedEntropy.lean` identifies that commutator with KL asymmetry and proves any
  measurable involution exchanging two class laws forces equality of their parameters. This is
  pre-route **ZGC**: actual infinite zeta source and pairwise orientation exist, but only in
  convergent chamber. No completed functional-equation involution, Xi landing, or RH endpoint is
  formal. `GaussianQuadraticCumulantCharacterization.lean` closes a relevant generic rigidity
  statement: a real probability law whose MGF is finite near zero and has a quadratic cumulant
  generator there is exactly Gaussian, with the converse also formal. This does not by itself
  connect the zeta-gas class law to completion; it prevents a quadratic-cumulant replacement from
  being treated as a neutral approximation.
  `ConstitutiveSplitFormationParallax.lean` and
  `SplitFormationParallaxDistanceBound.lean` define pre-route **SFP**. A finite family of split
  linear formations into one carrier has exact recovery; ternary interference reads the hidden
  residual, fusion-frame parallax is positive and jointly reconstructive, uniformly bounded
  repeated work is equivalent to vanishing hidden residual, and a lower bound on the orthogonal
  complement gives quantitative squared distance to the neutral overlap.
  `PoissonOccupancyHistorySplit.lean` proves exact decomposition of Poisson Jeffreys work into
  Boolean occupancy and nonnegative hidden history, with hidden work zero exactly for equal rates.
  `PoissonSuperpositionSaturationProperness.lean` proves visible occupancy work tends to zero under
  superposition while hidden history grows linearly and the induced orbit action is bounded exactly
  on the diagonal. `ReflectedPrimeHistoryReserve.lean` computes the reflected-prime reserve, its
  sharp asymptotic `t log(p) p^(-2(1-t))`, and exact all-prime summability threshold `t<1/2`.
  This is arithmetic half-aperture structure but has no Xi landing. No RHTower module
  instantiates these formations on the completed prime--Gamma/Möbius source or supplies an Xi
  endpoint, so SFP is not a candidate or live route.
  `PureReplicaCollectiveEnergyLaw.lean` separately proves centered replica energy is linear
  rather than quadratic, and `EulerianCrossingPolymerFreeEnergyLaw.lean` proves cubic crossing cost
  cannot erase a linear action gap. These prevent false amplification/crossing heuristics but do
  not define E's relation or change G/D2/MSC.
- `PrimeSamplingMicrolocalization.lean` proves a bounded critical-prime Bessel sampler with a fixed
  coherence floor must shrink its logarithmic coherence radius at least on scale `1/x` (and
  `1/log N` at prime cutoff), while local de Branges phase regularity supplies a competing floor and
  forces phase speed to grow. Thus broad coherent finite-window prime sampling cannot be an
  unbounded receiver. No completed arithmetic sampling carrier or RH landing is constructed.
- `LocalExponentialSignConeConverse.lean` proves positivity of a local exponential density exactly
  when every finite block-Hankel section is nonnegative; every failure has a finite witness.
  `CentralizerResidualReplicaEnergyLaw.lean` and `PureReplicaCollectiveEnergyLaw.lean` show
  centralizer subtraction preserves the commutator residual and replication scales its energy
  linearly. These are exact selection/amplification firewalls, not RH routes.

## Terminal and retired mechanisms

Closure applies to named mechanism, not every future use of similar objects.

| Route/mechanism | Terminal statement | Positive survivor |
|---|---|---|
| A | Source-faithful fixed physical-phase transport is identity; nonidentity has connection defect. Positive Markov feasibility is source sign; universal feasibility is RH. | Phase-natural rigidity and barycentric completeness. |
| B | Scaling/grading and distinct prolate parameters cannot share required unitary transport; finite real-zero receiver lacks source orientation. | Relative graph/boundary deformation only. |
| C2/I | Finite theta/dyadic width saturates coordinate; missing width is RH-bearing. | Cauchy/Hurwitz interfaces survive in Q. |
| D1 | Finite/local moment positivity does not orient completed all-degree source. | D2 continued tail and Q exterior kernel. |
| F | Bounded/sublinear compact Sonin completion has wrong asymptotic order, loses its floor, or collapses source. | F2 survives by replacing passive completion with a cofinal all-prime trace-moment weld; Route F itself stays retired. |
| G2 | Required relative-Volterra germ is RH-equivalent. | G marked boundary problem survives. |
| H | Even Taylor factorization loses orientation. | Relation-valued indefinite primitive only. |
| J | For `L_m=6 log m`, `m>=25`, bad energy is at least `log(m)/20` at every Julia scale; uniform budget impossible; diagonal subtraction breaks one-node capacity. | Principal-relative current defined before projection; not Route J. |
| K | Quadratic spectral mechanism cannot retain marked source. | Nonlinear incidence in P/HC. |
| M | Gamma--Jacobi reader complete; anchored cofinal flatness is RH. | Receiver only. |
| N | Response equality, endpoint contractivity, or bounded polar work is RH-equivalent; bilateral capacity excess is now exactly P's reflected translation/radial-work excess. | Shared receiver for L/P/G, not an independent producer. |
| R | Intrinsic producer category empty; every surviving external interface is RH-equivalent. The explicit reflected level-two squarefull Stokes boundary is summable exactly on the critical line, so global divisorwise normality is again exactly RH rather than an upstream law. | Quartic amplitude, singular cap, physical landing, and the explicit primewise squarefull Stokes coefficient remain reusable receivers/classifiers. |
| IW internal SEM Weyl model | Model existence is exactly `2^k` divisibility of actual hole count, depends only on dimension, and universal/cofinal existence is exactly RH. | Exact cyclic clock--shift realization and source-blind divisibility classification; useful certificate, not producer. |
| AP Big-Witt/Scaling-Site power orbit | Big-Witt reporter law holds, but Arakelov square lift has a pole at `1/2`, so no global entire-source pullback exists; actual Scaling-Site covers act differently; fixed-receiver stability/preperiodicity are RH-equivalent. | Source-first Big-Witt Frobenius reporter and valid changed-receiver cross-fibre scaling law. |
| TD/C1 raw positive completion | Four raw reflected critical Stokes atoms already exceed completed zeroth mass; no finite positive supercarrier dominating them can equal completed seam germ. | Any representing carrier must delete/reweight raw atoms or introduce signed negative correction before final positivity. |
| AF class-law scale-orbit | Convergent abelian class-law certificate exists iff centered rate is zero; global certificates on all Xi copies exist iff RH. | Terminal rigidity/selection theorem; successor must change interface to singular/infinite-action or genuinely global aggregate law. |
| formation-potential/Kummer/inertia selectors | Local formation charge is the analytic order of zeta. Holomorphic formation potential, Mackey flatness, pro-Kummer boundedness/summability, global-inertia compact/Schatten/determinant class, ind-formation, and cofinal group-like landing all select exactly charge zero; their universal strict-right forms are RH or imply RH. | Exact common integer-charge classification. A successor needs an independently constructed literal arithmetic formation law, not another representation of vanishing charge. |
| AGC all-grade Marcinkiewicz selector | Higher nonlinear Euler and tangent grades have bounded mass and vanish in the quotient; all-grade critical/off-line classification is already grade-one classification. | Exact grade-one retract and tail bounds; successor must change topology or use singular boundary/graph data. |
| reciprocal-Xi Clifford split | Bare Super-Poincare/Clifford splitting exists exactly under RH; algebraic `N=2` packaging is not an upstream source construction. | Concrete projection-phase, Deninger-cochain, and `Q8` odd-sector realizations remain reusable algebraic models. |
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
proves quadratic comparison no-go. `RouteRSquarefullStokesSummabilityProducer.lean` gives the
strongest current scalar survivor: one explicit reflected level-two primewise Stokes boundary is
summable exactly when `Re(rho)=1/2`, and arithmetic-corona globalization is equivalent to its
normality at every Xi divisor. It does not prove that global normality; the universal assertion is
again RH-equivalent. R contributed novel architecture/invariants, but no intrinsic
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
- any fixed finite functional-equation/Schwarz/order-one passport as a critical-line selector:
  arbitrary finite off-line quartet packets, with independently prescribed finite jet depths, are
  realized by entire order-one functions; a positive-real-axis polynomial gauge can implant a
  finite quartet packet while preserving functional equation, Schwarz reality, real-segment
  nonvanishing, and order-one growth;
- generic shifted-quotient symmetry, critical-line unimodularity, cocycle flatness, and contractive
  boundary compression as a uniform curvature bound: one self-dual off-line quartet has all these
  properties while its anti-causal leakage curvature exceeds `8` and is unbounded
  (`SelfDualQuartetShiftCurvature.lean`);
- replacing the unweighted off-line Cauchy energy by a positive power weight: weight zero is the
  unique power whose every cross entry stays positive, whereas every positive weight has a packet
  with a negative cross entry; Hankel Hilbert--Schmidt energy uses the wrong first-moment weight
  (`WeightedAntiCausalCauchyTrace.lean`);
- an unweighted closed scalar codiagonal erasing infinitely many orthogonal labels: a weighted
  codiagonal is closable exactly in the square-summable case, and the unweighted row has an explicit
  graph-null sequence with constant nonzero response (`WeightedCodiagonalDichotomy.lean`);
- exact simultaneous compact support, an open Fourier gap for nonzero bounded-support data, or zero
  spectral tail with nonzero interior band signal (`FourierIndeterminacyNoGo.lean`);
- Schatten membership as a selector of a half-line Jacobi boundary condition: each parity block has
  deficiency indices `(0,0)` or `(1,1)`, while the resulting finite-rank boundary ambiguity is
  invisible to every Schatten ideal (`JacobiDeficiencyRankTwoAmbiguity.lean`);
- finite-rank repair invisible on boundary-map kernel and zero-fed Uvarov tautology;
- fixed finite Hankel rank, fixed-degree reciprocal blocks, and one-sided quadratic bounds;
- unrestricted nonnegative source weights for nonzero fixed Loewner budget;
- pointwise-positive shifted Loewner-generator flow: every positive shift has a non-PSD generator,
  even though critical generator positivity is exactly RH;
- positivity, evenness, faster-than-every-exponential decay, global strict log-concavity, or
  unimodality of a theta-like source as a substitute for unrestricted right-half-plane flux order:
  one explicit
  source with all these properties has a right-half-plane transform zero and negative one-node
  flux (`ThetaSourceStrictLogConcavityFluxNoGo.lean`);
- vanishing or sign selection of the canonical Schwarz-pair tangential crossing: its
  multiplicity-weighted coefficient is strictly negative at every Xi divisor, including those on
  critical line. Only complementary source-normal coefficient has RH zero set
  (`ThetaCuspTiltFluxWeilParitySchwarzPairLorentzWeld.lean`);
- diagonal/subunit Cauchy-loss control from generic positive-real theory: an explicit two-node model
  has positive safe kernel and subunit diagonal factor but negative critical determinant;
- scalar real-axis inverse-kernel positivity for off-curve Hermitian positivity;
- positive Euler coefficients for PF2/variation-diminishing transfer;
- coefficientwise-positive Li-to-shifted-moment transfer;
- bare `ell^2` closure of finite coefficient summation;
- linear reflection cancellation as substitute for quadratic reflection incidence;
- fixed-degree positive limits as control of degree-matched cofinal diagonal;
- an aperture-independent sign law for Route E's literal Boolean physical anchor: its curvature is
  exactly overlap coarea minus rank-one centering mass, and the two-atom anchor changes sign at a
  unique aperture (`PhysicalIntervalAnchorCoarea.lean`); any viable use must control concentration
  defect at the selected source aperture;
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
- absolute two-sided critical graph variation for T2: critical gap energy and that absolute
  residual norm are mutually incompatible. Critical-line divisor multiplicity instead forces
  boundary Hardy-norm blow-up, so only signed or renormalized subhalf continuation can survive
  (`XiHeatCassiniWoldCriticalGraphNoGo.lean`);
- terminal closed range as a substitute for historical/singular descent: global properness of a
  finite transgression history requires every prefix transgression closed, and does not follow from
  terminal closedness alone (`HTGeometry/ClosedRangeTransgression.lean`);
- ordinary Fredholm index of the prime co-shift boundary complex: divisor kernel and cokernel are
  born together and its index is identically zero;
- BPS or Super-Poincare packaging by itself: exact first-order factorization exposes residual defect
  but does not prove source-specific zero-defect saturation;
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
  closure contains every admissible lower polynomial completion jet
  (`DeterminantGraphLocallyUniform.lean`);
- a nonconstant polynomial invariant under one nonzero univariate translation or under a spanning
  family of multivariate translations (`PolynomialShiftInvariant.lean`,
  `MvPolynomialTranslationSpan.lean`);
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
circularity boundary. W2C is the sharpest current example: exact even--odd finite-aperture index
retention is proved, yet universal aperture positivity is already RH because form still reads the
Xi divisor.

### Local exactness can sharpen rather than solve the global obstruction

Several branches have complete local algebra with no global producer. CLG has the full explicit
Euler-safe observability deficit, including convergence, offset independence, and exact critical
evaluation, while its theta-flux presentation is exactly the same packet order problem under an
invertible diagonal rescaling. Regular two-pole Cauchy localization now proves every off-line fibre
appears as one admissible moving antisymmetric escape with exact source limit `-N`; neither
presentation supplies source-side no-escape. T2 has
an exact Chebyshev-error increment normal form and residue-preserving ODE receiver, but its absolute
critical graph topology is formally inconsistent with the needed gap energy. CGL has the finite
Class-I/Class-II zero alternative, literal inverse-incidence fibres, and exact weighted
large-value reduction to centered first/third Gram traces. Diagonal cubic cancellation and affine
reduced-residue Poisson summation are now exact, but no conductor-uniform estimate controls the
remaining literal not-all-equal six-label correlation or its large-height census.
MEG has complete all-depth normal
form and realizes every compatible finite class-divisor family by universal-carrier jets, so finite
depth data cannot select the global arithmetic carrier. F2 identifies completed scalar traces but still
needs compatibility of all operator powers. These are not unfinished calculations of same kind: each theorem proves
that remaining information lives in global cross-term compatibility, cofinal uniformity, or
completed source occurrence.

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
gives explicit countermodel and actual escape schedules. T1 shows refinement transfers current
rather than removing it; T2 shows absolute critical control is the wrong topology because true
critical-line residues force boundary blow-up. CLG/TTF now shows an off-line fibre can hide from
every fixed local packet regime while a moving two-pole sequence converges to exact negative
antisymmetric source charge. MSC proves mass escapes beyond every fixed compact synthesis and that full
retention forces unbounded scaled aperture. SV2 now has a canonical cofinal projective normal family
but still needs global target identification and reciprocal-chart control. Cofinal argument needs
synchronized estimate, not iterated pointwise limits.

### Singular boundary is not removable technicality

L, G, P, U, O, SV2, PCS, SEC, and BPC reach a completion or continuation boundary where smooth
interior misses state. Gamma
sewing beats finite Rees order; Kelvin charts cannot share scalar renormalization; first contact can
be rough; an ordinary index can cancel simultaneous kernel/cokernel birth. Needed objects are
relative, graph-valued, nonlocal, multi-chart, or non-scalar. L's analytic completion, all-jet
compact-open exactness, strict resolved chain provenance, concrete cofinal arithmetic boundary,
and actual Gamma/Sonin receiver are closed. Its sole scientific gate is now the singular
source-to-fixed-physical comparison which makes that genuine boundary invisible to the existing
coefficient-faithful reader. Closed terminal range alone cannot replace prefix transgression
control.

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

F2, UEB, CLG/TTF, T2, PSRC, PBM, MSC, SV2, PCS, SEC, and BPC form a second non-classical family: infinite paired/operator/graph or
analytic source followed by a singular, meromorphic, or homological boundary landing. MSC has the carrier but lacks pointed
divisor covariance. UEB has exact affine marking and a complete order-one Bezoutian classifier but
lacks source-produced kernel positivity. CLG/TTF turns the same logarithmic-derivative geometry into
exactly equivalent Euler-observability and literal theta-correlation-flux order problems, while
proving positive-shift flow and generic strict-log-concavity shortcuts impossible. Its entire
off-line obstruction is now localized by moving regular two-pole Cauchy packets with exact negative
source limit; missing law is cofinal source no-escape. W2C identifies that detector with canonical even--odd finite-aperture Weil
channels and retains every negative packet, but supplies no pre-divisor positivity. PSRC has exact
continued prime residue and dense finite Euler core, but closability
of its singular graph is already exactly RH. PBM retains quantized monodromy at infinity and proves
finite/local completion cannot carry it; absence of that charge is again exactly RH. SV2 now has actual entire real-zero characteristics, a canonical paired
projective family, and local cofinal compactness; it lacks global target identification and the
reciprocal pole chart. PCS has an exact all-prime graph, spectral gap, and divisor boundary
complex but lacks a secondary class capable of seeing homology whose ordinary index is zero. SEC
has an exact end-coherence collapse and a canonical prime-ray Calkin endpoint, but lacks a source
law making the adjacent seam coboundaries eventually compact. BPC
has the exact positive susceptibility singularity and collar-to-RH transfer but lacks source
continuation through that collar. T2 has an unconditional ordered-prime Wold residual, exact
prime-zeta/log-mesh/Chebyshev-error normal forms, and a residue-faithful continuation receiver; it
lacks one uniform logarithmic tail envelope for the actual fixed Heath--Brown aggregate and the
critical-weight aggregation turning resulting literal proportional-gap packets into critical
energy, together with signed or renormalized continuation through every
strict subhalf strip. None can be reduced to one finite positive object or one scalar
response without hitting a proved
firewall.

F2 is the cleanest source-to-source member of this family. Its open premise names neither a Xi zero
nor a divisor-built Gram: one literal positive all-prime operator moment curve must approach one
literal continued prime--Gamma moment germ. Corpus separately supplies the completed
trace-class source and positive prolate carrier, but trace realization is weaker than positivity of
all powers. This isolates a new recurring wall: matching scalar traces or first moments does not
place an entire target sequence inside a positive Hankel moment cone.

Remaining pre-routes reinforce that taxonomy rather than extend route count. Prime-Laplace
Gamma jets are an infinite paired clock with exact translation anomaly/Bianchi curvature, but the
coherent observer is unbounded. Prime-support Hodge theory says phase begins at cycles rather than
paths and finite positive-prime apartments are acyclic. Prime-square Fourier strata now give a
cofinal two-level reflection law with exact type `|c|`; its exponential drift signal dominates the
polylogarithmic Wold boundary scale. Grade--Lambert monodromy inversion has now crossed into PBM's
critical-strip quantized residue, but still lacks independent zero-charge production. AGC adds an
infinite all-grade coefficient topology only to prove that nonlinear and tangent higher grades
collapse back to grade one in this topology; this is a firewall, not an opening. PLAC instead keeps
the whole depth action through a singular blow-up and recovers both coefficients and multiplicity
residue, but has no pre-divisor zero-charge law. EPC keeps the polarized projection leakage that
scalar compression discards, but has no independent source domination. MEG has a complete
all-depth cyclic normal form and realizes every compatible finite class-divisor family by
universal-carrier jets, so only global mixed compatibility can select the intended carrier. MEG has neither completed arithmetic occurrence nor
Xi landing. ZGC has an actual convergent infinite zeta source and strict KL orientation, but no
completed functional-equation involution or Xi landing. SFP has positive multi-formation parallax,
global properness under repeated work, distance-to-neutral control, and an exact Poisson
occupancy/history split showing visible saturation with hidden extensive action, but no literal
arithmetic formation or RH receiver. The de-Poissonized CLG/W2C bridge has a full explicit
observability deficit and atomwise removal of safe offset, but no source proof of its order.
Half-line exponential Gram/distance identities supply exact Cauchy
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

Expanded BPS/Super-Poincare layer exposes another common wall. Many apparently different energies
are now exact `energy = charge + defect` systems, and several RH endpoints are literally zero-defect
saturation. Concrete projection-phase, Deninger-cochain, and `Q8` odd-Clifford models prove this is
not merely abstract notation. This does not merge routes into one proof: source-specific mathematics
must still prove saturation. Extra supersymmetric packaging, first-order factorization, or
positivity of total energy cannot substitute for control of residual defect; bare reciprocal-Xi
Clifford splitting is already RH-equivalent.

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
   Möbius/theta object (CCM-FU, D2, E, Q, CLG/TTF, T1, T2).
2. **Ground-relative coercivity:** control exact state selected by full operator, not one seed or
   generic packet (C1, O, G, U).
3. **Singular boundary descent:** physical comparison across completion boundary without losing
   coefficient, multiplicity, or orientation; for L this is the source-to-fixed-physical
   specialization of its already strict resolved boundary (G, L, P, U).
4. **Mixed-incidence control:** preserve cross terms diagonal energies erase (E, Q, HC, T1,
   CLG/TTF).
5. **Cofinal synchronization:** one estimate uniform in moving pole/degree/aperture/height;
   CLG/TTF's exact two-pole escape and T2's stopped-ladder scalar envelope make diagonal escape the
   obstruction rather than bookkeeping (CCM-FU, C1, CLG/TTF, E, F2, O, T1, T2, U, SV2).
6. **Source-native internal dynamics:** projective module, corrected Stokes category, monodromy,
   singular depth action, operator leakage, or analytic continuation on literal completed source
   before divisor selection (UEB, PSRC, PBM, SC, PPM, IRK, OPUC, HJ, BW, MSC, PCS, SEC, BPC;
   pre-routes PLAC, EPC, MEG, ZGC, and SFP; W2C/de-Poissonization is a receiver/source bridge).
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
5. What source-derived singular comparison makes the already constructed resolved Xi boundary land
   in the existing Burnol/Deninger physical reader, commutes with the strict chain differentials,
   preserves prime/depth/multiplicity and the nonzero leading Xi coefficient, and annihilates the
   boundary without assuming `K_6(rho)=0`?
6. Is completed CCM symbol nonnegative on every canonical actual-head density?
7. What pre-divisor completed-source law forces moderation of the literal second-Cartier endpoint,
   despite the proved post-selected finite-measure and scalar-short firewalls?
8. Why is the explicit positive-paired exterior source diagonal nonnegative at every admissible
   pole, from source before divisor selection? At the Xi endpoint this is equivalent to domination
   of critical-error current by compensated Gauss-resolvent quadratic and to PSD of every finite
   Gaussian-rational paired kernel, but Lean's diagonal-to-matrix collapse passes through RH.
9. What signed short Möbius-block estimate controls the depth-invariant top-row/translation
   remainder—and hence the canonical full-density transfer current—without splitting cancellation,
   given that full normalized zero-packet vanishing and zero-free aggregate current are closed but
   transfer-current sublinearity is exactly RH?
10. What source mechanism excludes exact nonintegrable strict-frontier Christoffel quotient or
    proves shifted reciprocal Hankel tail positivity inside proved parabolic horizon?
11. Can two-prime source excess be bounded absolutely below collision quantum two, can literal
    paired Gamma-six determinant current be proved prime-summable upstream, or can the CGL literal
    not-all-equal weighted six-label correlation—after exact diagonal cancellation and affine
    reduced-residue Poisson transformation—be given a conductor-uniform bound and large-height
    aggregation strong enough for an absolute detector census?
12. Can source globalize Coxeter, prime-power collision, irrational-rotation `K_0`, paraorthogonal
    phase, or Hurwitz projective reflection before divisor selection without collapsing to another
    RH-equivalent certificate?
13. Can the concrete Möbius signed-channel feature cross its exact half-unit continuation deficit,
    pointed residue/graph-domain wall, and unbounded-aperture requirement to satisfy a source-derived
    four-unit covariance bound?
14. What source identity forces the canonical Suzuki projective normal-family limit to equal the
    global Xi Livsic/projective target, and how does that identity propagate through the reciprocal
    pole chart?
15. Can critical Schur monodromy, a difference Picard--Vessiot group, MEG's complete all-depth
    universal-carrier normal form, a Manin-horizon sharp group, or approximate quantum-return loss be
    instantiated on literal completed arithmetic source and coupled coefficient-faithfully to Xi
    before divisor selection? For MEG the invariant must use global mixed compatibility, since
    every compatible family of finite class divisors has a universal-carrier realization.
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
27. What literal completed theta/prime--Gamma source law excludes every admissible cofinal
    two-pole Cauchy escape with `(even,odd,source)->(0,N,-N)`? This must control moving poles before
    divisor selection; fixed-node positivity, two real-ray order, generic log-concavity, tangential
    Schwarz crossing, and the RH-equivalent evaluated deficit cannot supply it.
28. What topology or singular invariant escapes the proved AGC collapse of every nonlinear and
   tangent higher-grade tail to grade one while still retaining coefficient-faithful Euler source?
29. Can PLAC's recovered squarefree action and multiplicity residue, or EPC's polarized boundary
    leakage, be coupled to a completed pre-divisor source law that forces zero charge/order without
    importing CLG, PBM, G, or L's RH-equivalent endpoint premise?
30. Can one source-derived cofinal Sonin aperture section or positive aperture barycenter identify
    every moment of the positive all-prime residual energy with the continued prime--Gamma moment
    germ, preserving all mixed Hankel powers rather than only the completed scalar trace?
31. Can ZGC's convergent all-mode KL chirality be continued through Gamma completion so
    functional-equation reflection becomes a measurable class-law exchange and forces the centered
    chemical-potential difference to vanish on an Xi receiver?
32. Can SFP be instantiated by three or more coefficient-faithful completed arithmetic formations
    whose hidden residual is the horizontal Xi defect, with source-derived fusion-frame coercivity
    and bounded repeated parallax work before divisor selection?
33. Can the one logarithmic tail-envelope inequality be proved uniformly for the actual fixed
    Heath--Brown aggregate and used to sum the resulting literal proportional-gap packets at
    critical weight to prove prime-gap energy from ordered-prime source, and can T2's exact
    Chebyshev-error-minus-depletions recurrence be summed in a signed or renormalized topology to
    continue the residual kernel through every strict subhalf strip while allowing the boundary
    poles that critical-line zeros force?

Until one is answered, endpoint reformulations, finite real-zero models, seed asymptotics, diagonal
moment inequalities, or scalar transport identities do not move formal RH frontier.
