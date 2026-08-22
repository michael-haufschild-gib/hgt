# Current Formal Frontier Toward Proving or Disproving the Riemann Hypothesis

## Scope, evidence, and status language

This document states where the `HTGeometry`, `HilbertMetric`, and `RHTower` Lean corpus stands now. It
maps architectures, theorem chains, open cores, and terminal mechanisms—not chronology or work log.

**Formal-corpus cutoff:** 22 August 2026, commit `75a8054775696097d44d207f48beb96a578d4238`, plus
declaration-index review of the current working tree. Scientific status comes only from Lean
declarations, dependencies, theorem docstrings, and
explicit gap/no-go markers. Pipeline cards and papers are not evidence. This was documentation-only,
not a rebuild. Incomplete or placeholder-bearing declarations are excluded from proved evidence and
route counts; uncommitted declarations are identified as working-tree evidence where material.

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

## Executive map

Formal corpus supports nineteen live producer architectures, distinguished by first source premise
rather than pairwise-independent receivers:
`CCM-FU, C1, D2, E, F2, G, G-CE, L, O, P, Q, CLG/TTF, SP-E, SCE, T1, T2, U, HC`, and
**SV2 (Suzuki spherical characteristic convergence)**. CLG and TTF are now one architecture, not
two: Lean proves their finite-packet order problems equivalent by invertible Xi diagonal rescaling.
Route T covers two independent source mechanisms: `T1` (Xi-Taylor transfer current) and `T2`
(Wold--mesh residual continuation). Sixteen
corpus-born candidates remain: `TK, BSH, UEB, PSRC, PBM, SC, PPM, IRK, OPUC, HJ, BW, MSC, EWQ-V, PCS, SEC, BPC`.
R, IW, AP, scalar EWQ, DQPT, and fractional-part extraction are terminal as independent producers. RH and its negation remain unproved.

| Architecture | Proved chain | First open core |
|---|---|---|
| CCM-FU | completed Guinand--Weil source -> marked rectangular current -> Suzuki checkpoint current -> signed event curvature -> coherent prime--polar--Gamma/unit-Riesz boundary -> Xi-screw Green -> RH | Uniformly bound one fixed-`b` affine checkpoint average. Exact critical-chord measure, completed Riesz graph energy, adaptive cofinal Suzuki landing, and signed second-grade cancellation now close the source geometry and cofinal normalization; they do not bound the moving affine current. Negative cells remain exactly odd-prime-power endpoints, so only cross-event/critical-remainder cancellation is open. |
| C1 | completed theta/prime--Gamma source -> finite adelic band and trace formula -> global class-space quotient -> positive Weil distribution or real spectral realization -> RH | Instantiate the abstract Connes positivity limit from the literal global arithmetic source and exclude the cofinal two-pole antisymmetric escape. Finite-stage adelic bands, support/Fourier intersection, rapid trace error, finite trace formula, and abstract positivity-from-positive-cutoff convergence are exact; the source-derived global positive cutoff/correction and its convergence to the Weil distribution are not. |
| D2 | continued prime--arch trace -> one-sided anti-Herglotz/finite ceiling -> RH | Source control of sole positive-frequency tail by a reflected signed/non-dominating law; canonical directed passive limits are impossible. |
| E | squarefree Wold source -> two-sign half-power marker supply -> exact integer-pair incidence -> unit-load Hall transport with moving flux -> RH | Build one Ramaré-supported relation joining proved marker supply to relation-specific subinterval Hall, unit load, co-moving flux, and Gibbs cost. Finite unsigned Type-II, character-mean-value, and Bohr dense-model adapters are exact; none defines this relation. |
| F2 | all-prime principal-relative Sonin residual -> positive trace-class energy -> one intrinsic Hankel moment curve -> continued prime--Gamma moment germ -> RH | Prove one source-derived cofinal aperture section, positive aperture barycenter, or equivalent all-moment weld from the Sonin energy moments to the fixed prime--Gamma moments. |
| G | Suzuki/Mobius/Gamma source -> marked pre-scalar or signed-channel carrier -> exact Ward landing -> wall orientation -> RH | Independently prove eventual four-unit Ward scalar control on canonical prime-log samples, or an equivalent signed order. Their detection-cover condition is now discharged internally, but the resulting scalar/matrix tail laws are exactly RH, not producers. |
| G-CE | prime-free divisor defect -> signed Mobius floor-dilation action -> half-order Abel moment -> coherent unit-Riesz/Green/Chebyshev boundary -> RH | Prove a uniform bound for the normalized signed Mobius--divisor half-order Abel moment. The prime-free defect is unconditionally `O(sqrt N)`, and the coefficient-faithful weld to the coherent Selberg moment is exact; absolute channel estimates destroy the dilation cancellation. |
| L | completed Green/BV/co-Poisson source -> strict resolved Xi boundary with prime/depth/multiplicity provenance -> singular source-to-physical comparison -> coefficient-faithful Burnol/Deninger reader -> RH | Construct one source-derived singular comparison, before divisor specialization, which sends the already resolved boundary to the existing physical landing and makes its physical reader annihilate that boundary. The comparison must preserve the nonzero Xi coefficient and cannot assume the conormal defect vanishes. |
| O | exact restricted-Weil operator -> canonical true-ground heads -> rank-two PSD/chiral carrier -> complex Dirac plane -> source-self-polarized determinant -> restricted-Weil landing -> nonnegative floor -> RH | Self-polarization now makes every nonempty prime-power packet determinant strictly negative off center and zero only at center. Prove this quadratic source-selected scalar lands coefficient-faithfully in the linear actual-head matched block/restricted-Weil floor, including spectral integration and physical collar; the sign law itself is closed. |
| P | primitive Gamma/Julia Stokes wall -> source-horizontal second-Cartier orbit -> Route-N capacity/radial-work bridge -> radial Krein energy -> endpoint moderation -> RH | The exponential wall has exact source-native signed Fredholm quadratic jet `-16/35`, but Lean proves it is not the canonical completed-theta/Xi quadratic jet. Produce endpoint order globally before divisor selection through a separately source-derived rescaling/correction or another singular landing; fixed canonical matching, regular reflection-pair extraction, finite circle measure, and literal scalar short are ruled out. |
| Q | continued Hurwitz/Cauchy source -> countable Gaussian-rational Euler-pole paired kernel -> orientation zero -> RH | Prove source nonnegativity of the explicit exterior paired diagonal, equivalently passivity of every finite paired-value matrix. Lean proves this scalar collapse only through Xi-specific RH capstones, so it is a smaller receiver, not a source proof. |
| CLG/TTF | literal completed theta source -> neutral correlation flux = Xi Bezoutian -> invertible diagonal congruence -> Euler-safe observability deficit = reflection-even minus reflection-odd two-channel Weil energy -> RH | Exclude, directly from the completed source, every admissible cofinal regular two-pole Cauchy sequence with reflection-even energy tending to zero and reflection-odd energy tending to its positive fibre multiplicity. This moving rank-two no-escape law is exact: any off-line fibre produces source energy tending to the negative multiplicity. |
| SP-E | natural Suzuki reporter -> coherent prime outgoing amplitude minus regular-screw continuum -> completed Green/Ward wall -> RH; prime increments equal quarter-dilation gain minus debt | Compare this exact signed prime dilation flux with the continuum increment and deduce a uniform amplitude imbalance. Separate positive estimates lose the required cross-scale cancellation; raw Cauchy energy diverges. |
| SCE | Mangoldt event history plus archimedean reservoir -> unique strict-convex checkpoint -> restricted Legendre conjugate -> nonnegative checkpoint floors -> RH | Prove source-first `suzukiCheckpointConjugate N <= suzukiCheckpointMoment N` for every `N>=2`, or an event-recursion law forcing it. Bregman drawdown controls displacement from the minimum, not its absolute sign; universal checkpoint nonnegativity is already exactly RH. |
| T1 | finite Xi-Taylor/theta-tail source -> exact reflection bridge -> zero-free full-density channel plus canonical transfer current -> raw core-current bound -> RH | Produce a source-first sublinear bound for the canonical full-density transfer current, concretely by signed short Möbius-block cancellation preserving the combined top-row/finite-translation current. The normalized Xi packet and literal differentiated primal square-AFE source-field `L2` law are discharged; transfer-current sublinearity is exactly RH. |
| T2 | ordered-prime Wold source -> inverse-log adjacent defect -> literal physical von-Mangoldt slice -> forced second Maynard count -> critical gap energy -> residual Hardy continuation/ODE -> RH | Arbitrary-order localization now sends an inverse-log defect to the second alternative on every strict base-phase margin; shell cap and exact base-or-second dichotomy are closed. Prove that actual ordered-prime shells supply this defect and remaining scale envelope, sum at critical weight, and separately prove signed/renormalized subhalf continuation. |
| U | shifted hard-edge source -> cofinal shifted Hankel tail or first-contact exclusion -> RH | Non-scalar source mechanism excluding the exact nonintegrable strict-frontier quotient, or uniform cofinal tail order. |
| HC | two-prime/Cayley/Gauss--Hodge source -> quantized horizontal collision charge -> strict sub-two or prime-summability law -> RH | Certified-packet Proposition 4.6, full `S1`, arbitrary-order far-left decay, both time-regime `I2` tails, and the complete small-time reflected finite-critical/tail truncation have source-faithful `X^-200` control. Construct actual selected rows, control `S2/S3` and remaining non-tail terms, and aggregate globally; or prove the absolute subquantum producer. |
| SV2 | literal Suzuki energy space -> paired self-adjoint characteristics -> bounded projective normal family -> global Xi projective target -> corrected two-chart spherical limit -> RH | Canonical actual Livsic and projective characteristics now admit compatible cofinal locally uniform limits on the entire upper half-plane, with every holomorphic jet retained. Identify that limit with the divisor-faithful global target, propagate it to a finite chart containing all Xi zeros, then prove reciprocal pole-chart convergence and eventual pole-neighborhood zero-freeness. |

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
rate. `ThetaCuspTiltFluxWeilParitySchwarzPairNormalRenewalWeld.lean` gives that
coordinate two literal phases. Fixed abelian class-law scale-orbit certificates exist exactly at
zero normal charge; away from zero, every finite degree admits a positive nonlinear Weyl renewal.
The later parabolic weld synchronizes those degrees, but the universality no-go proves its
normalized increment is exactly an arbitrary external aperture height, not an invariant extracted
from the shifted-Xi source. SNR is therefore terminal. Its surviving normal-coordinate reader does
not provide a source producer.

The corpus instead exposes live **SP-E** at amplitude level. The natural Suzuki reporter amplitude
is exactly coherent prime outgoing charge; subtracting the regular-screw continuum yields the
completed Green/Ward-wall amplitude, whose uniform boundedness is exactly RH. Lean simultaneously
proves why this cancellation must precede energy formation: the exact nonnegative transition core
diverges and dominates the squared prime charge even after all favorable secant pairs are removed.
SP-E's source problem is bounded atomic--continuous imbalance, not another positive Gram budget.

The corpus also exposes live **T2**, distinct from the Xi-Taylor branch now called T1. Its ordered
prime Wold current has an unconditional holomorphic residual Hardy kernel on `Im z<0`, an exact
prime-zeta-minus-log-mesh-minus-holonomy normal form, and a continued residual carrying the full
integer multiplicity at every right-strip zero once critical prime-gap energy is available. An ODE
uniqueness theorem makes critical gap energy plus continuation to `Im z<1/2` imply RH. The newest
normal form writes every residual increment as a normalized consecutive Chebyshev-error increment
minus two nonnegative depletions, one trace class and one absorbed by critical gap energy. Lean also
proves that the tempting two-sided absolute critical graph norm is empty. T2 therefore requires a
signed or renormalized subhalf continuation, not absolute boundary variation. Gap-square shells are
bounded by literal prime-free base measure in the same physical block. The physical-slice chain now
turns any inverse-log adjacent defect, on every strict base-phase margin, into an exact base-or-
forced-second alternative after its explicit envelope is paid. Shell cap, band coverage, parity,
and bad-base `L2` conversion retaining the pole-cancelled cube are closed. What remains arithmetically
is to prove that actual ordered-prime shells supply that defect and envelope, then sum at critical
shell weight; signed/renormalized subhalf continuation remains a separate open core.

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

Many exact source criteria below are formal equivalences with RH. Rewriting RH as positivity,
boundedness, passivity, flatness, or collision absence advances nothing unless corpus also supplies an
independent producer. Most remaining problems are constitutive source laws, not formal packaging.

## Live architectures

### CCM-FU — four-unit source-codiagonal incidence

**Architecture.** Literal completed Guinand--Weil source is differentiated to its first noncentral
incidence, transported through a marked rectangular/Suzuki current, and reduced at floor-selected
checkpoints to signed event curvature. Coherent boundary transport identifies that curvature with
the prime--polar--Gamma, unit-Riesz, Selberg, completed-Chebyshev, and Xi-screw Green interfaces.
A bounded fixed-lower-wall affine current implies RH.

**Proved chain.**

1. The centered cubic source jet is the Loewner incidence and the affine-normalized Xi-screw Green
   curvature. Its second Abel/Cesaro primitive yields RH under a linear-growth bound; non-RH forces
   superlinear escape.
2. For fixed `H>b>0`, the Cesaro quantity is exactly the anchored signed moment with positive
   kernel `K_H(h)=(96-64h/H)/h^4`, exactly the prime--polar triangular window, exactly the completed
   quantile transport up to bounded incoming/lower-wall terms, and exactly a positive marked mixture
   of causal rectangular currents. These are equality-of-interface theorems, not sign estimates.
3. Suzuki reduction splits every checkpoint into an affine event jet plus nonnegative within-cell
   Bregman curvature with uniformly bounded total correction. The affine mixture is therefore the
   sole unbounded term.
4. The discrete cell is exact:
   `slope(N+1)-slope(N)=signedCell(N)`; it is negative exactly when `N+1` is an odd prime power
   and positive otherwise. Smooth cell curvature, endpoint reset, Gamma/Binet correction, and the
   full event-weighted Gamma prefix are controlled.
5. Coherent boundary transport proves outgoing unit-Riesz charge minus prime--polar--Gamma
   curvature, after explicit vanishing archimedean and endpoint corrections, is the normalized
   completed Chebyshev error. The same current is the weighted Selberg `psi-id` increment.
6. `CCMFUSuzukiCompletedRieszGraphEnergy.lean` proves finite singular graph energy for the actual
   completed prime--polar--Gamma Riesz producer on every cofinal aperture edge.
   `CCMFUSuzukiAdaptiveCofinalLanding.lean` gives coefficient-faithful finite-aperture landing to
   that literal source.
7. `CCMFUSuzukiCriticalChordMeasure.lean` retains positive atomic and positive polar chord
   measures as a signed pair and proves the completed critical jet equals atomic Riesz mass minus
   polar Riesz mass plus the Gamma boundary. Möbius fibre cancellation removes the apparent
   `1/omega` singularity before scalarization.
8. `CCMFUSuzukiSecondGradeAsymptotic.lean` constructs a positive cofinal schedule
   `omega_N -> 0` on which the normalized completed Suzuki jet converges to the exact signed
   second-grade arithmetic-minus-polar functional; after inverse-square-root mesh normalization its
   source quotient tends to zero. This closes the landing and normalization, not boundedness of the
   moving target current.

The half-order Abel weld exposed by the same source is recorded separately as live Route G-CE,
because its first unproved producer is a different arithmetic cancellation theorem.

**Open core.** For one fixed `b>0`, prove

```text
exists C, forall H >= b,
  |ccmFUSuzukiCheckpointAffineMixture b H| <= C.
```

Equivalently, bound the completed quantile transport, triangular prime--polar window, anchored
completed-error moment, marked Suzuki average, or normalized coherent boundary current. Every local
term and every source handoff is explicit. Missing content is global cancellation between sparse
negative odd-prime-power events and positive complementary events under the critical Green
accumulation. Finite graph energy and cofinal normalized cancellation do not give this uniform
moving-current bound.

**Closed detours.** First and second centered jets are blind. Fixed finite quotients, scalar
dressing, positive first-clock Markov transport, midpoint-square positivity, separate absolute
estimates of positive/negative cells, vertical cancellation, and quadratically damped actual-head
lifts cannot supply the bound. The midpoint codiagonal is `E^2/2`, not an upper estimate for
`E`; the matched quadratic actual-head lift is absolutely summable and therefore erases the
cofinal Green growth. The surviving channel must remain signed, source-coupled, and pre-damping.

Formal sources include `CCMGuinandWeilThirdGrade*.lean`,
`CCMGuinandWeilThirdGradeRectangular*.lean`, `CCMFUCentralRectangularAffineWeld.lean`,
`CCMFUSuzukiCheckpointAffine*.lean`, `CCMFUSuzukiSignedCurvature*.lean`,
`CCMFUSuzuki{PrimePowerSignClassification,SelbergRemainderBridge,CoherentBoundaryTransport}.lean`,
`CCMFUSuzukiCompletedRieszGraphEnergy.lean`, `CCMFUSuzukiAdaptiveCofinalLanding.lean`,
`CCMFUSuzukiCriticalChordMeasure.lean`, and `CCMFUSuzukiSecondGradeAsymptotic.lean`.

### C1 — Weil/Connes positive spectral realization

**Architecture.** Completed theta/prime--Gamma data are placed on an adelic scaling quotient.
Finite cutoff bands produce trace distributions; a source-derived positive global cutoff limit
would make the Weil distribution positive type, or equivalently produce a real spectral
realization. Either endpoint forces every Xi divisor onto the critical line.

**Proved chain.**

- The complete square-summable Xi Weil form, its finite Laurent/Galerkin floors and Schur
  reductions, regular two-Cauchy packet exhaustion, prime--arch reflection Gram, endpoint
  saturation, and self-adjoint vacuum endpoints are exact. Positivity of the completed form is
  equivalent to RH.
- Local ramified and unramified Tate integrals, the finite-place product, archimedean Weil term,
  prime-power contribution, Mellin continuation, finite Tate tensor stages, countable Euler-product
  limit, abstract orbit unfolding, scaling-flow change of variables, and kernel trace identities
  are formal.
- `ConnesAdelicBand.lean` constructs the actual finite-stage class space `X_S`, cutoff
  `P_Lambda`, semilocal Fourier transform, closed band
  `B_Lambda = range(P_Lambda) ∩ range(F P_Lambda F⁻¹)`, and its orthogonal projection
  `Q_Lambda), with literal support and Fourier-support vanishing.
- `ConnesTraceFormulaAssembly.lean`, `ConnesTraceFormulaStatement.lean`, and
  `ConnesTraceErrorRapidDecay.lean` close the finite summed trace asymptotic with error
  `O(Lambda^(-N))` for every `N), under the explicit finite chart/lift hypotheses. Cutoff,
  Besov, shell, periodization, and rapid-decay mechanics are no longer the frontier.
- `ConnesTheorem5Positivity.lean` proves the abstract terminal step: positive finite conjugation
  traces converging to the Weil distribution make the limit positive type. Lean does not derive
  those global positivity/convergence hypotheses from the literal arithmetic quotient, and the
  quoted positive-Weil-to-RH criterion is not itself formalized there.
- `ConnesEntireSpectralMultiplicity.lean` classifies the local entire multiplier receiver: at a
  zero of order `m`, solutions are exactly the finite delta-jet span of dimension `m`.
  `HedenmalmSpectralInterpretationCompletion.lean` similarly gives the exact theta boundary
  solution and spectral receiver. Neither supplies the global positive source form.
- Every off-line conjugate fibre produces collision-free moving two-pole packets in the continued
  source domain with reflection-even energy tending to zero, reflection-odd energy tending to its
  positive multiplicity `N`, and source energy tending to `-N`. Thus the obstruction already
  lives in a cofinal rank-two antisymmetric direction; full-space density is not the missing idea.

**Open core.** Construct from the literal normalized adelic/class-space source, before choosing a
Xi divisor, positive cutoff traces and a global correction whose limit is the completed Weil
distribution, while proving that the correction controls the cofinal two-pole antisymmetric escape.
Equivalently, produce a source-dense corrected reflection form or self-adjoint vacuum that is
exhaustive on the entire Weil ground space. Theorem 4's finite analytic scaffold is substantially
closed; Theorem 5's arithmetic instantiation and orientation are RH-bearing.

The correction cannot be an abstract quotient declared positive after the fact. It must retain the
prime, Gamma, ramified, and multiplicity coefficients; identify the normalized restricted-product
limit; control the trace-class remainder; and prove positivity before divisor specialization.

**Closed detours.** The canonical reflected Stokes carrier has excessive zeroth mass, and every
finite positive measure dominating its raw atoms has excessive central mass. Therefore no positive
Hermitian supercarrier retaining those atoms can represent the completed germ; any survivor must
delete/reweight atoms or use a signed negative correction. First-moment excess excludes a constant
counterterm. Bounded/sublinear compact corrections, passive positive completion, bare spectral
saturation, and merely declaring a quotient positive either fail formally or restate RH. The local
spectral-multiplicity theorem is a receiver, not the global producer. Finite-residue Brauer data
also cannot supply the correction: every additive complex residue observable is zero while the
literal local Tate source is nonzero. Any ABHN refinement must retain ramified/boundary data.

Formal sources include `ConnesAdelicBand.lean`, `ConnesTraceFormula{Assembly,Statement}.lean`,
`ConnesTraceErrorRapidDecay.lean`, `ConnesTheorem5Positivity.lean`,
`ConnesEntireSpectralMultiplicity.lean`, `ConnesTate*.lean`,
`Connes{Ramified,Unramified}LocalZeta.lean`, `ConnesWeil*.lean`,
`PrimeArchConnesReflectionMain.lean`, `TwoDilationSpectralRepresentation.lean`,
`HedenmalmSpectralInterpretationCompletion.lean`,
`ThetaCuspTiltFluxWeilParityCauchy{Localization,SourceEscape}.lean`, and
`GammaSewnMobiusApertureStokesPositiveCompletionNoGo.lean`.

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

The remaining finite Type-II branches are now closed as well. Literal divisor-bounded data supplies
every active and selected cell count and the full `T2` power saving
(`Sieve/MatomakiTeravainenTypeIICellCount.lean`,
`Sieve/MatomakiTeravainenTypeIISelectedCellCount.lean`,
`Sieve/MatomakiTeravainenTypeIIT2PowerSaving.lean`). The `T1` large set has cardinality at most
`T^(21 eps)`; its real-finset Halasz--Montgomery energy, two-block tails, unraised factor, and full
fixed-polylog contribution follow with no analytic premise. Pairwise spacing and the same literal
polylog envelopes also discharge `T3`
(`Sieve/MatomakiTeravainenTypeIILargeSetCount.lean`,
`Sieve/MatomakiTeravainenTypeIIT1Energy.lean`,
`Sieve/MatomakiTeravainenTypeIIT1TwoBlockEnergy.lean`,
`Sieve/MatomakiTeravainenTypeIIT3PowerSaving.lean`). No finite unsigned Type-II estimate is E's
frontier. All three branches remain capacity/cost input and create neither signed adjacency nor
co-moving sector flux.

The coefficient-removal substep is also exact rather than implicit.
`Sieve/JutilaCoefficientRemoval.lean` proves the finite complex Gram inequality with exact
coefficient cost and no phase or positivity premise;
`Sieve/JutilaDirichletCoefficientRemoval.lean` identifies the critical Dirichlet kernel with that
Gram form; and `Sieve/JutilaPowerCoefficientRemoval.lean` reduces the complete double `2k`-moment
to the unweighted length-`L^k` critical polynomial at the squared divisor-fibre cost. This leaves
the sampled second-moment estimate and, more importantly for E, the source-fixed signed relation.
It is another unsigned finite adapter, not a producer or a new route.

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

`CharacterSumMeanValue.lean`, `BohrSetExistence.lean`, `DenseModelBohr.lean`,
`DenseModelPointwise.lean`, and `DenseModelArithmetic.lean` close finite character second moments,
large Bohr sets, Fourier/mass/coset and pointwise arithmetic transference. These unsigned adapters
neither define fixed integer relation nor prove interval Hall, unit load, co-moving flux, or Gibbs
cost; E's open core does not move.

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

`SoninForbiddenClosedSum.lean`, `SoninCarrierApertureChain.lean`, and
`SoninCarrierApertureLimits.lean` prove the forbidden-band sum closed, strict-aperture density,
dense union as aperture tends to zero, and trivial intersection as it tends to infinity.
`SoninMellinHalfPlaneExtension.lean` gives bounded holomorphic Mellin evaluation on `Re(s)>0`.
Working-tree `SoninExtendedOrthogonalBand.lean` identifies the extended Sonin space exactly as the even
orthogonal complement of the mean-zero physical band and its cosine image. Working-tree
`SoninBandCodimensionTwo.lean` instantiates full-line Burnol band geometry: the central Sonin carrier
is the intersection of physical and Fourier forbidden orthogonals, both missing band directions are
nonzero, and their sum's orthogonal complement has finrank exactly two. This closes concrete carrier
codimension, not its all-prime moment-curve identification. A separate working-tree semilocal gate
proves archimedean Gamma moment positivity and the exact monic Jacobi coefficient, but not finite-prime
two-sided growth or a Carleman/domain theorem. These are carrier inputs, not the all-power source weld.

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
`XiWardPrimeLogTailEndpoint.lean` removes the last sampling side condition:
eventual scalar control on canonical prime-log samples, eventual finite Gram positivity there, and
RH are equivalent. This sharpens the receiver but supplies no upstream estimate.

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

Actual-head wall-Gram chain sharpens which distinct channel survives. Scalar chord differentiation
recovers odd wall-light orientation, but reflection-even completed producers erase that odd jet.
Pairing it with literal odd polar sine connection gives a reflection-even covariant current, exactly
a positive rate times matched Suzuki current (`CCMActualHeadWallGramLightConeReflectionFiber.lean`,
`CCMActualHeadWallGramLightConeCovariantTransmutation.lean`). Occurrence is closed; G's independent
four-unit/Ward order is not.

### G-CE — Möbius--divisor half-order Abel cancellation

**Architecture.** Start with a prime-free divisor-summatory defect, apply the complete signed
Möbius floor-dilation action before scalarization, and read it through the square-root/half-order
Abel mesh. The resulting source is exactly the coherent Selberg outgoing moment, hence the
unit-Riesz/Green/completed-Chebyshev boundary. Uniform normalized boundedness is equivalent to RH.

**Proved.**

- `CCMFUSuzukiMobiusDivisorAbelProducer.lean` defines
  `primeFreeDivisorDefect` as log-factorial minus the divisor summatory function plus its Euler
  main term and proves the unconditional `O(sqrt N)` bound with explicit constant `24`.
- Möbius floor inversion reconstructs the literal Chebyshev defect with every sign and dilation
  coefficient intact. The pre-scalar
  `mobiusDivisorSquareRootAbelMoment` is therefore an arithmetic producer, not a Xi-divisor
  definition.
- The exact CCM-FU/G-CE weld is

  ```text
  mobiusDivisorSquareRootAbelMoment M
    = coherentSelbergSquareRootAbelMoment M
      + 2 * EulerGamma * (sqrt M - 1).
  ```

  The Euler edge is bounded after the route normalization, so
  `MobiusDivisorSquareRootAbelBounded`,
  `CoherentSelbergSquareRootAbelBounded`, and RH are equivalent.
- `CCMFUSuzukiMobiusDivisorDilationChannels.lean` gives both the coefficient-faithful sum of
  signed dilation channels and the collapsed Möbius-kernel formula. The completed Riesz graph
  modules identify the same moment with the discrete flux of the literal completed Chebyshev prefix
  through the square-root mesh and with the critical chord carrier plus Gamma boundary.
- `CCMFUSuzukiSelbergOutgoingAbelWeld.lean` proves the outgoing completed charge is the normalized
  signed half-order Abel action plus a vanishing source-free lattice defect. Thus the arithmetic,
  Riesz, Suzuki, Selberg, and completed boundary interfaces are all exact.

**Open core.** Prove `MobiusDivisorSquareRootAbelBounded` directly from the prime-free divisor
defect: uniform cancellation in the joint signed Möbius--dilation sum after half-order Abel
readout. The unconditional `O(sqrt N)` estimate on each base defect is not enough after summing
dilations, and taking absolute values channel by channel destroys precisely the cancellation that
the exact floor inversion preserves.

This is distinct from Route G under the map's first-premise convention. G seeks a nonlinear
source law orienting an already transported four-unit Ward coefficient. G-CE seeks an arithmetic
bound for an explicit all-scale signed Möbius--divisor action; it then uses the shared coherent
boundary only as receiver.

**Closed detours.** The coupled-error singular graph completion is positive unconditionally, but
its extra graph debt vanishes exactly under RH
(`MobiusGammaXiCoupledErrorSingularGraphGlobalWall.lean`). Finite source-native self-adjoint
boundary transports converge while retaining that debt. Scalar controller cancellation either is
RH or uses an opposite controller that moves twice the debt to a hidden port
(`MobiusGammaXiCoupledErrorDebtCancellationDichotomy.lean`). Positive completion, scalar erasure,
or post hoc hidden-port cancellation therefore does not prove the G-CE bound.

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
already trivial; in the rational local factor the stronger finite-residue Brauer observable is
identically zero while the Tate source is nonzero. Cofinite unit-normalized packet floor forbids square summability; generic mapping
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

All-prime matched-cell convergence is now closed on every literal aperture head, not only a dense
smooth core. `CCMActualHeadMatchedApertureFiniteSupport.lean` proves the matched radius is at most
one, while beyond twice physical aperture the translation defect is constant. Every sufficiently
remote prime anchor therefore cancels its entire mass-matched polar cell exactly; the asymmetric
Suzuki current and even residual also vanish separately. All three all-prime families are
eventually zero and hence summable without smoothness, Fourier moments, prime-gap estimates, or
spectral approximation. `CCMActualHeadMatchedSymmetricFirstMomentControl.lean` and
`CCMActualHeadMatchedSmoothCoreConvergence.lean` remain valid but are no longer the sharp
convergence frontier. Route O is an exact finite source-to-floor landing problem on each canonical
aperture head.

Finite support does not identify the all-prime matched family with the physically truncated
restricted-Weil source. `CCMActualHeadMatchedBoundaryCoverageSeam.lean` now closes that distinction
exactly. Every post-cutoff contribution is one boundary-overlap collar; all possible nonzero collar
indices lie in an explicit finite prime-power strip of additive width `a+1/2` above `exp(2a)`.
The all-prime `tsum` is the physical finite block plus precisely this collar. In the actual source,
endpoint scalar mass and matched coverage mass cancel to a universal `4‖f‖²` reserve plus the
difference between true and locally matched polar autocorrelations. Thus no remote tail or hidden
partition premise remains, but the finite coverage seam cannot be discarded.

`CCMActualHeadMatchedQuantilePolarCoordinateTransport.lean` then puts matched and monotone-quantile
cells in the mass coordinate `Y(h)=2 exp(h/2)`. They have equal length and differ by one rigid
translation `delta_n` satisfying

```text
-R_n-criticalMellinAtomWeight(n) <= delta_n <= -R_n,
```

where `R_n` is the outgoing completed error. The whole coverage seam is the finite sum of these
cell translations minus one terminal quantile interval. This is a coefficient-faithful reduction
of O's sign problem to completed-error-controlled finite transport. The unconditional
de la Vallee Poussin estimate in `CCMActualHeadMatchedQuantilePolarDLVPRate.lean` proves its
normalized Chebyshev driver is `O(exp(h/2-c*sqrt(h)))` and becomes negligible after division by
the polar mass scale `exp(h/2)`. This controls high-coordinate displacement rate; it does not
orient the finite seam or terminal interval.

Matched cell now has complete local two-channel geometry. Even cosine rebate and odd Suzuki current
form a Hermitian characteristic cocycle; positive-minus-negative light is literal sine coordinate;
scalar chord plus orientation is full anti-diagonal wall Gram. Spectral differentiation recovers
orientation exactly, with positive chord curvature and matched-polar contact both positive dressings
of CCM's cubic prime-entry jet. Direct scalar transport is impossible because completed producer is
reflection-even while this jet is reflection-odd. Odd wall derivative paired with odd polar sine
connection instead gives a reflection-even covariant current, exactly a positive rate times matched
Suzuki current.

`CCMActualHeadMatchedPhaseDiskSchurCompletion.lean` closes atomwise completion problem. Matched cosine and
sine profiles are entries of an integrated PSD `2 x 2` Gram density and satisfy exact disk
`(C_n(xi)-w_n)^2 + S_n(xi)^2 <= w_n^2`. Literal prime-phase rotation gives a pointwise nonnegative
Schur completion of intact prime-minus-polar cell with exact actual-head reserve
`4 w_n ||f||^2 - w_n E_f(log n)`.

Thus neither local sheet selection nor local orientation occurrence is open. Remaining obstruction
is not generic reserve summation. `CCMActualHeadMatchedPhaseDiskCofinalGaugeNoGo.lean` proves fixed
two-channel trace, negative complementary channel after center subtraction, nonsummable prime center
trace, no finite-valued positive linear cutoff extension, and unbounded-below exact extensions.
Scalar positive finite-part assembly is terminal.

`CCMActualHeadMatchedPhaseFockTomography.lean` supplies the first exact survivor. It subtracts the
center before positivity, retaining the trace-free Bloch pair `(C_n-w_n,S_n)`, and adjoins two fixed
coordinate anchors. Their exponential-inner-product Gram packet is PSD. Real logarithms of its two
atom--anchor entries recover both oriented phase coordinates exactly; every atom--atom logarithmic
covariance is forced by those same anchors, so no target-fitted cross-prime completion is inserted.
The finite matched prime--polar block is exactly the spectral integral of this nonlinear reporter.

`CCMActualHeadMatchedPhaseInfiniteFockKernel.lean` and the projective-gauge modules close cofinal
carrier compactness. One source-selected half-density has summable square; two rank-one Gram terms
give a global PSD kernel with summable arithmetic diagonal, realized on `ell2` by a positive
rank-at-most-two Schatten-one operator. Its exterior minor is a rank-at-most-two skew-adjoint
trace-class chiral operator, hence a self-adjoint Hermitian orientation observable after
multiplication by `i`. Nonlinear kernel, matrix-ratio, chiral, and Hermitian reporters all recover
the complete oriented source atom and every finite actual block exactly. Infinite carrier, trace
class, and orientation occurrence are closed. Carrier positivity alone gives no sign to the
nonlinear reporter after spectral integration; self-polarization below supplies a different signed
scalar but still lacks the floor landing. This remains an O subarchitecture because it uses O's
actual-head source and floor endpoint.

The chiral-nodal chain now resolves both source coordinates and also closes one tempting shortcut.
For the real projection, a fixed Hermitian shear evaluates on the canonical `3x3` kernel line as
twice gauge square times the matched source, and its affine determinant is exactly the negative
crossing form. Finite actual blocks are spectral integrals of these determinant-derived reporters.
At every prime-power wall, however, the determinant response has zero first frequency jet,
strictly negative second jet, a local maximum at center, and is locally nonpositive; every nonempty
finite prime-power sum has the same strictly negative curvature. Thus naive positivity of the
one-shear determinant chamber is terminal, not O's missing order law.

`CCMActualHeadMatchedPhaseProjectiveGaugeComplexDiracTwoShear.lean` retains the discarded complex
coordinate. Its Hermitian Dirac block has exactly one kernel line. Two fixed Hermitian shears read
the real and imaginary matched-source coordinates, and their two-parameter determinant is the
corresponding real linear functional. Joint crossing energy is exactly

```text
4 * gauge(n)^4 * normSq(orientedPhaseSymbol(n,xi)).
```

For every prime power, and for every nonempty finite label-preserving packet, this energy is
positive iff `xi != 0` and zero iff `xi=0`; the imaginary shear crosses center transversely.

`CCMActualHeadMatchedPhaseProjectiveGaugeComplexDiracSelfPolarizedShear.lean` then closes the scalar
selection problem without division: the source itself supplies the two shear coefficients. Nodal
form becomes `2*gauge^2*normSq(Z)` and the adaptive Dirac determinant becomes
`-2*t*normSq(Z)`. For every `t>0`, each actual prime-power atom and every nonempty finite labeled
packet has determinant strictly negative exactly off center, zero exactly at center, and center as
global maximum. This is a source-native scalarization of the oriented plane, not an assumed
positivity law.

It remains an O subarchitecture because it uses O's actual-head source and ground-floor endpoint.
Its determinant is quadratic in the matched complex source, whereas the actual matched
prime--polar block and restricted-Weil floor are linear signed spectral integrals. No theorem
identifies the adaptive determinant with that global receiver, preserves coefficients through the
spectral integral, or restores physical boundary collar. Thus source-native scalar sign is closed;
global Weil/Xi landing is open.

`CCMActualHeadMatchedPhaseProjectiveGaugeLinearReadoutNoGo.lean` proves the projective gauge is
square-summable on canonical primes but its reciprocal is not, inverse-gauge costs diverge, and no
square-summable test vector recovers every ratio. Landing must retain nonlinear/projective structure
or use a source-derived singular domain; a bounded linear `L2` inverse-gauge bridge is terminal.

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

Formal sources: `CCMRestrictedWeil{CanonicalGroundHeadEnergy,ActualHeadCompletedErrorProducer}.lean` and the `CCMActualHead{SignedCompletedErrorGammaProducer,OutgoingQuantileTransportProducer,CoherentCompletedGammaProducer,CoherentQuantileGammaProducer,OutgoingQuantileCompletedCharacteristicSeam,MatchedApertureFiniteSupport,MatchedBoundaryCoverageSeam,MatchedQuantilePolarCoordinateTransport,MatchedQuantilePolarDLVPRate,MatchedOrientedCharacteristicCocycle,MatchedOrientedWallLightIncidence,MatchedWallLightQuadraticJet,MatchedWallLightThirdJetTransmutation,WallGramLightConeCircleCompletion,WallGramLightConeJetRecovery,WallGramLightConeJetPairing,WallGramLightConeReflectionFiber,WallGramLightConeCovariantTransmutation,MatchedPhaseDiskSchurCompletion,MatchedPhaseDiskCofinalGaugeNoGo,MatchedPhaseFockTomography,MatchedPhaseInfiniteFockKernel,MatchedPhaseProjectiveFockCocycle,MatchedPhaseProjectiveGaugeSummableKernel,MatchedPhaseProjectiveGaugeTraceClassOperator,MatchedPhaseProjectiveGaugeChiralOperator,MatchedPhaseProjectiveGaugeChiralNodalLine,MatchedPhaseProjectiveGaugeNodalSourceShear,MatchedPhaseProjectiveGaugeNodalCenterCurvature,MatchedPhaseProjectiveGaugeComplexDiracTwoShear,MatchedPhaseProjectiveGaugeComplexDiracSelfPolarizedShear,MatchedPhaseProjectiveGaugeLinearReadoutNoGo}.lean` family.
`CCMActualHeadExteriorCosineMeasureGauge.lean`.

**Open core.** At every aperture, prove cofinally on canonical actual heads the literal
reverse-prime bound, equivalently nonnegativity of the exact finite matched-autocorrelation source
including its boundary coverage seam. First constructive target is a coefficient-faithful landing theorem for the
exact self-adjoint trace-class matrix-ratio/self-polarized reporter: prove its quadratic determinant
law lands in the linear matched-autocorrelation producer after spectral integration on canonical
heads, preserves prime--Gamma labels, and restores physical collar. Controlled signed exterior
gauge is a separate sufficient implementation. Carrier assembly, compactness, trace class,
one-dimensional nodal selection, full complex-coordinate readout, center transversality, and
source-native scalar sign are closed. Positive finite-part assembly and fixed one-shear positivity
are dead; so is bounded linear inverse-gauge recovery. A coefficient-faithful nonlinear or
singular self-polarized-to-Weil landing is first missing theorem.

This supersedes old prolate-seed frontier. Canonical heads are selected from true ground and
converge to it. Remaining problem is transporting proved self-polarized source sign into the exact
linear arithmetic floor on those heads, not constructing/evaluating a seed or classifying all
near-ground profiles. Unsigned Gamma envelopes cannot replace the coefficient-faithful landing.

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

The primitive Gamma/Julia Stokes wall now contributes a concrete source invariant.
`RoutePPrimitiveGammaJuliaStokesWallFirstJetInvariant.lean` proves the exponential-wall
factorial Fredholm coefficients at orders zero, one, and two are exactly `1`, `1`, and `19/70`.
Consequently the quadratic jet of the signed square `D(z)D(-z)` is exactly `-16/35`. This is formed
from the arithmetic wall before any Xi divisor. The comparison is now sharp and negative:
`RoutePPrimitiveGammaJuliaStokesWallThetaJetSeparation.lean` proves the canonical completed-theta
curvature is strictly below the fixed wall calibration, hence this wall product jet is not the
central completed-theta/Xi quadratic jet. The coefficient remains a possible P/SP-E input only
after a separately source-derived rescaling or correction; direct fixed-canonical identification
is closed, and no endpoint moderation follows.

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
without post-selected scalar domination. The fixed exponential-wall-to-theta jet is unavailable;
any use of that wall must first construct its rescaling/correction from source data, not fit it to
Xi. Pre-vacuum annealed invariance does not provide this law: nontrivial invariance on every Xi copy
is exactly RH. Post-vacuum annealing fixes edge grade `1`, not critical grade `0`, and under RH moves
every divisor packet (`SourceHorizontalAnnealedEscortVacuumStaging.lean`). The stronger
`SourceHorizontalAnnealedSecondCartierOrbitFirewall.lean` proves every nonzero annealing exponent
preserves strict-right orbit escape; universal boundedness is `alpha=0 or RH`. Annealing, tempering,
and memory attenuation therefore cannot supply P/G's missing moderation producer.

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

Formal sources: `XiHurwitzOrientation{SeparatedSourceReconstruction,ExteriorCauchyClosure,PositivePairedSource,SharpNonnegativeConeDistance,BoundaryMixedIncidence}.lean`, `XiPositivePairedRealLoewnerSeam.lean`, `XiCauchyTransformCompleteness.lean`, `XiEulerSafePaired{Completeness,Closure,RationalCriterion,ValueKernel}.lean`, and `Paired{InfiniteApertureCurrent,CompletedEulerCurrent,TranslationResolventCalculus}.lean`.

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

The higher theta/Turán calculation sharpens the local obstruction.
`PrimeArchThetaBornWittenSixthJet.lean` computes the fifth and sixth logarithmic jets and proves
strict atomwise positivity of reflected-Hankel sixth curvature.
`ThetaCuspFullReflectionSixthTuran.lean` supplies the summable sixth-order atom majorant.
`ThetaCuspCenterMixedFourPointParityWall.lean` splits the palindromic four-point Toeplitz wall
exactly into even and odd (2\times2) blocks, while
`ThetaCuspCenterMixedFourPointEvenParityCusp.lean` proves the even wall strictly positive near the
coalesced cusp. The remaining local four-point obstruction is therefore reflection-odd. This
narrows CLG/TTF's no-escape channel but does not prove its global order or add a route.

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

### SP-E — Suzuki prime--continuum amplitude balance

**Architecture.** Evaluate the literal natural-aperture Suzuki Cauchy reporter before forming a
quadratic energy. Its lower-Hardy amplitude is exactly the coherent finite-prime outgoing charge.
Subtract the positive regular-screw continuum at amplitude level; the completed amplitude is then
exactly Suzuki Green, and after the fixed polar offset it is the full prime--polar--Gamma Ward-wall
value. Uniform boundedness of this atomic-minus-continuous amplitude is equivalent to RH.

**Proved.** `SuzukiCauchyReporterSecantPrimeChargeBridge.lean` proves

```text
natural reporter lower-Hardy amplitude = coherent prime outgoing charge,
completed amplitude + 2 = Suzuki Green = completed Ward-wall value,
RH iff the completed amplitude is uniformly bounded on natural apertures.
```

The equivalent source criterion in `SuzukiWardAtomicContinuousLightWeld.lean` says RH exactly when
the finite positive von-Mangoldt wall mass and positive regular-screw continuum mass have uniformly
bounded signed imbalance. This is a literal pre-divisor source premise: it uses the complete prime
packet and continuum together, not a selected Xi zero.
`SuzukiWeilFrakP.lean` now constructs the published prime--archimedean reporter and proves its
removable central value is `-g_xi(t)` with corrected Lerch/digamma signs. Independently,
`SuzukiWeilZeroSeries.lean` constructs the multiplicity-exact divisor series and evaluates its
Laplace transform as an Xi relative-resolvent difference. No theorem identifies these two
functions pointwise or derives the required uniform signed amplitude bound.

The order of operations is now rigid. `SuzukiCauchyReporterSecantSharpArithmeticLocalization.lean`
gives the exact secant-sign atlas: transition-separated interactions are nonpositive and the
complementary transition core is termwise nonnegative. Yet
`SuzukiCauchyReporterSecantTransitionCoreEscape.lean` proves that positive core grows at least
linearly and diverges along apertures `8n`; the prime-charge bridge proves it dominates the square
of the coherent outgoing charge. Removing all favorable cross-scale pairs therefore does not
create a bounded positive energy. Atomic and continuum amplitudes must cancel before squaring.

`SuzukiPrimeOutgoingDilationFlux.lean` resolves the prime side dynamically. Passing from `N` to
`N+1` creates no local new-prime term: complete increment is outward dilation gain minus inward
debt, split at `N/4`. Indices through quarter wall contribute nonpositive debt and later indices
nonnegative gain. First source target is therefore a signed one-step comparison with regular-screw
continuum increment; bounding gain and debt separately discards exposed cancellation.

**Open core.** Prove directly from the literal source one constant `C` such that for every natural
aperture `N`,

```text
|prime outgoing charge(N+2) - regular-screw Ward mass(log(N+2))| <= C.
```

Equivalently, compare quarter-dilation gain minus debt with continuum step and telescope without
invoking the RH-equivalent boundedness criterion. Raw positive-energy estimates, separate positive
flux bounds, deletion of nonpositive secant interactions, and squaring prime packet first are
terminal. This live SP-E route is the amplitude-before-energy survivor; legacy
SP-E trace-class, `det2`, fixed-node, and direct Xi spectrum-moving landings remain retired.

### SCE — Suzuki checkpoint event dynamics

**Architecture.** Decompose literal Suzuki source on each integer logarithmic event cell into
smooth archimedean reservoir minus cumulative Mangoldt slope plus its first moment. Strict positive
reservoir curvature selects one unique checkpoint. Restricted Legendre--Mangoldt duality evaluates
that cell minimum. Nonnegativity of every checkpoint then gives pointwise Suzuki nonnegativity and
RH. Mechanism is discrete event-history convex duality, not finite spectral approximation or
classical explicit-formula positivity.

**Proved.** `SuzukiCheckpointEventDynamics.lean` defines cumulative half-weighted Mangoldt mass
and logarithmic moment and proves on `[log N,log(N+1)]` that `suzukiPsi(t) = reservoir(t) -
mass_N*t + moment_N`. Cell potential has second derivative equal to strictly positive regular
Suzuki kernel. Every cell therefore has unique minimizer, with value exactly `moment_N -
suzukiCheckpointConjugate N`,
where conjugate is restricted supremum of `mass_N*t-reservoir(t)`. Endpoint recurrence uses only
reservoir increment, cumulative mass, and logarithmic event displacement. At a stationary
checkpoint, source drawdown is exactly reservoir Bregman divergence. Finally
`riemannHypothesis_iff_suzukiCheckpointNonnegative` proves universal checkpoint-floor
nonnegativity equivalent to RH; unconditional first-gap positivity discharges pre-event interval.

**Open core.** Derive before divisor selection `forall N>=2,
suzukiCheckpointConjugate N <= suzukiCheckpointMoment N`, or a stronger source-native event
recursion/order law implying it. Strict convexity, unique
minimizer, Legendre representation, and Bregman nonnegativity only control relative drawdown; none
orients absolute minimum. Reasserting checkpoint nonnegativity is exactly RH, and finite event
verification cannot close cofinal statement. SCE is live because literal source, connector, and RH
endpoint are formal; it has not yet produced independent inequality.

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

The primal square-AFE source is now differentiable in observation height at theorem level.
`SmoothAFEZetaSquarePrimalHeightDerivative.lean` proves absolute summability uniformly in height
and termwise differentiation. `Sieve/DivisorSquareLogTail.lean` supplies logarithmically weighted
divisor-square tails; `SmoothAFEZetaSquarePrimalHeightDerivativeMass.lean` derives plain and affine
masses `O(log^6 N)` and `O(N log^5 N)`; and
`SmoothAFEZetaSquarePrimalHeightDerivativeAffineMeanSquare.lean` proves the infinite affine mean
square `O(N log^5 N + H log^6 N)`. `SmoothAFEZetaSquarePrimalHeightDerivativeSourceField.lean`
now identifies the rephased derivative `LSeries` exactly with the literal primal source field and
transfers that affine estimate to every centered physical interval. Source-field occurrence and
coordinate translation are closed. The estimate remains unsigned and cannot bound the joint signed
top-row/translation current.

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

Formal sources: `XiCTaylorThetaTail{CoreCurrentCapstone,ProductFiberHermitianCollapse}.lean`; `Sieve/{RouteT*,PrimeRangeTwistTail,GSTailAssembly,GSTailMass,MoebiusDistanceAllFreq,MoebiusDistanceSharp,MoebiusSmoothPolySaving,MoebiusSeriesPolySaving}.lean`; and `SmoothAFE{ZetaChiLeftPowerBound,ZetaGeneralEdge,Truncation,ZetaSquarePrimalHeightDerivative}.lean`, `ZetaChiVerticalGrowth.lean`.
`SmoothAFEZetaSquarePrimalHeightDerivativeMass.lean`,
`SmoothAFEZetaSquarePrimalHeightDerivativeAffineMeanSquare.lean`,
`SmoothAFEZetaSquarePrimalHeightDerivativeSourceField.lean`,
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
interval forces one of those finite packets to be large.
`MaynardPrimeFreeRangePacketCutoffSchedule.lean` and
`MaynardPrimeFreeRangePacketCanonicalCutoff.lean` then absorb the complete fixed-source logarithmic
envelope by every positive power and choose one canonical degree-60 Mobius cutoff with the exact
short-factor packet bound. Thus the former scalar-envelope, adaptive-tail, Mellin-order, and
source-freezing gates are closed for the literal packet.
`MaynardFixedWidthTailMonotonicity.lean` proves a natural-order tail certificate at the smallest
positive fixed width propagates through `1/4`; `MaynardFixedWidthCanonicalCutoff.lean` composes it
with the canonical minimal-width theorem, closing the uniform order-50 cutoff for every fixed
width. `MaynardFixedWidthCanonicalPacket.lean` turns prime-freeness into one canonical large
fixed-ambient packet over every admissible width, and `MaynardFixedWidthRungUniformization.lean`
covers pointwise chosen rungs by one fixed finite union.

The count/measure interface is now closed down to the true trivial-count boundary, bypassing the
syntax-blocked `11/5` branch. `MaynardTransitionStripCount.lean` supplies sub-height extraction,
coloring, and the second receiver throughout the transition strip; its physical companion proves
both parity alternatives for every band there. `MaynardTrivialBoundaryBandCoverage.lean` joins this
to the upper-amplitude theorem, so every positive band above canonical base is receiver-ready.
`MaynardTrivialBoundaryAdaptiveEnvelope.lean` absorbs selector entropy and adaptive amplitude at
that exact boundary, while `MaynardTrivialBoundaryBaseMeasure.lean` gives the base layer the same
critical bad-measure scale. `MaynardAdaptiveParityBadMeasure.lean` remains the amplitude-free
equation-(111) receiver. Amplitude floor, parity choice, finite label entropy, fixed width, and base
layer are therefore closed; no repaired `11/5` theorem is scientifically required.
`MaynardTrivialBoundaryBandSchedule.lean` supplies a canonical logarithmic band count and proves
its terminal band exceeds every literal unit-cell maximum.

First-receiver and integer-selection seams are closed. `MaynardTrivialBoundaryFirstExclusion.lean`
absorbs first-branch and selector costs; `MaynardTrivialBoundaryBandThreshold.lean` puts every
positive band above its exclusion threshold. `MaynardTrivialBoundaryGapSequence.lean` sends a
central adjacent-defect shell to a spaced sequence, dyadic band, mass bound, and Maynard receiver.
The arbitrary-interval theorem chooses adaptive width, retains uniform signed mass, and forces the
second count without endpoint trimming.

The newer physical-slice chain removes the remaining abstract interval packaging.
`MaynardPhysicalSliceCountNormalization.lean` works with the literal floor-truncated von-Mangoldt
Dirichlet polynomial and proves exact central and outer base-or-second alternatives on arbitrary
intervals. `MaynardPhysicalSlicePrimeFreeComposition.lean` upgrades arbitrary-order Mellin
localization: on every strict margin `1 < mu(1-alpha)`, an inverse-log adjacent defect forces the
literal physical slice into the second alternative once its explicit envelope is paid. Central and
outer base layers become strictly smaller than the surviving defect.
`MaynardWeightedSpatialMellinBadMeasure.lean` converts actual-coefficient spatial `L2` into a
restricted bad-base estimate and retains the pole-cancelled low-cell factor `(R/N)^2 K^3`, removing
the old maximum-envelope-times-cardinality loss. Independently,
`MaynardTrivialBoundaryShellCap.lean` absorbs the entire fixed polylog envelope through
`mu<=19/9`; `MaynardTrivialBoundaryShellSecond.lean` discharges the cap on the positive-amplitude
branch; and `MaynardTrivialBoundaryShellDichotomy.lean` gives the complete shell statement: either
the exact trivial-boundary base layer already carries the defect or one positive band satisfies the
second count. Thus cap, base-smallness comparison, cell discretization, parity, and forced count are
receiver theorems. Remaining composition is source-specific: prove actual ordered-prime shells
produce the inverse-log adjacent defect in the permitted phase/scale regime, then sum the resulting
base-or-second bounds at critical weight.

**Closed shortcut.** Absolute boundary control is the wrong topology.
`XiHeatCassiniWoldCriticalGraphNoGo.lean` proves critical residual upper variation and critical gap
energy cannot coexist, and consequently the proposed two-sided critical Abel graph norm is
unconditionally false. The positive survivor is a boundary classification: assuming the subcritical
analytic source and critical energy, every critical-line zero forces radial residual Hardy norm to
blow up with its integer residue. A viable continuation must therefore be signed, renormalized,
distributional, or otherwise allow these forced boundary poles; it cannot be absolute at the
critical edge.

**Open core.** Prove from the ordered-prime source, without choosing a zero:

1. prove actual ordered-prime shells supply the inverse-log adjacent-defect lower bound and explicit
   physical-slice scale envelope in one strict base-phase regime, then sum the already closed
   base-or-second shell output into critical gap-energy summability; and
2. signed/renormalized continuation of the residual Hardy kernel from `Im z<0` through every
   strict sub-half strip `Im z<a<1/2`, equivalently a source law controlling the Chebyshev-error
   accumulation after the two explicit depletions.

The conditions must be compatible with forced critical-line boundary poles. The exact absolute
critical graph norm, ordinary endpoint continuity, and separately bounded unsigned variations are
dead. T2 is an infinite paired, nonphysical source/mesh architecture and is independent of T1's
finite Xi-Taylor transfer-current cancellation.

Formal sources: `XiHeatCassiniWold{CenteredLogConnection,ConvergentLogHolonomy,ResidualHardyPolarization,PrimeZetaLaplaceSymbol,RelativeOrbitLeakage,ResidualODEClosure,CriticalGraphNoGo,ResidualFirstOrderGapFluctuation,ChebyshevErrorIncrement}.lean` and `XiHeatCassiniLogMeshDefectPrimeGapEquivalence.lean`.
Arithmetic receiver chain: `Sieve/MaynardOrderedPrimeGap{Occupancy,ProportionalPrimeFree}.lean`, `Sieve/MaynardFixedAmbientPacket{Interval,NatOrder}.lean`, `Sieve/MaynardPrimeFreeRangePacket{Composition,NatOrder,TailEnvelope,CutoffSchedule,CanonicalCutoff}.lean`, `Sieve/MaynardFixedWidth{CanonicalPacket,RungUniformization}.lean`, `Sieve/MaynardTransitionStrip{Count,PhysicalCount}.lean`, `Sieve/MaynardTrivialBoundary{BandCoverage,AdaptiveEnvelope,BaseMeasure,BandSchedule,FirstExclusion,BandThreshold,GapSequence,ShellCap,ShellSecond,ShellDichotomy}.lean`, `Sieve/MaynardAdaptiveParityBadMeasure.lean`, `Sieve/MaynardWeightedSpatialMellinBadMeasure.lean`, and `Sieve/MaynardPhysicalSlice{CountNormalization,PrimeFreeComposition}.lean`.

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
The terminal SNR normal reader does not prove U's uniform cofinal tail order: its synchronized
renewal value is externally aperture-selected and therefore carries no source vanishing estimate.

Formal sources: `XiShiftedReciprocalHankelTailCriterion.lean`, `XiShiftedCanonicalAdmission{AdaptiveArithmeticSourceDegreeConnection,CofinalScheduleNoGo,AdaptiveMixedSourceParabolicFluxCorridor}.lean`, `SuzukiFirstContactBoundaryRoughness.lean`, and `XiShiftedHardEdgePrimeGammaKelvinTwoChartNoGo.lean`.

**Open core.** Prove uniform cofinal tail positivity/order for explicit source Hankel matrices, or
construct a non-scalar source mechanism that annihilates strict-frontier numerator/excludes its
endogenous admission zero before nonintegrable quotient forms. Generic numerator regularity,
arbitrary schedule delay, scalar counterterms, fixed-degree limits, and positivity along a
self-selected recession schedule are closed or insufficient. Fixed structural face data also
cannot determine crossing sign or port orientation (`GUStructureAdmissionSplit.lean`); source-native
admission is indispensable.

### HC — horizontal-collision quantum

**Architecture.** A coefficient-faithful two-prime/Cayley/Gauss--Hodge source assigns an integer
reflection self-intersection quantum to every off-line Xi fibre. A strict source budget below the
first nonzero quantum, or a prime-summable source census with finite total charge, eliminates all
off-line fibres and proves RH. The Chen--Gupta--Li branch seeks that budget through a selected
large-value packet, cubic Gram trace, Poisson decomposition, and zero-density aggregation.

**Proved collision layer.** The horizontal collision/reflection charge is nonnegative, integral,
multiplicity-sensitive, zero exactly on the critical line, and at least two on an off-line
reflection pair. Finite strict-sub-two source loss therefore implies RH. The prime-energy version
charges finitely many distinct defects by at least the sum of squared multiplicities, but its raw
critical energy may be infinite; ordinary logarithmic normalization erases a fixed charge.
Relative subtraction or an absolute finite source budget remains necessary.

The EWQ completed Fock census now reaches the same receiver: each Xi divisor contributes rank
quantum zero on the line and two off the line, and the finite multiplicity-squared census equals the
canonical HC reflection self-intersection charge. This identifies two receiver descriptions; it
does not provide HC's arithmetic budget.

**Proved CGL reduction.**

1. Weighted selected large-value packets, centered Gram positivity, Hilbert--Schmidt trace, and
   centered cubic trace are exact. The cubic diagonal is precisely the centering subtraction, so
   the remaining term is the literal not-all-equal six-label character/phase correlation.
2. Compactly supported Schwartz kernels, all Mellin/additive phase jets, both all-order Fourier
   decay families, reduced-residue Fourier identity, affine Poisson summation, and all required
   finite/infinite interchanges are formal.
3. The Lemma 4.5 transformation is exact:
   `centered cubic trace = Z + Z' + sum_(m != 0) I_m`.
   Character orthogonality, zero-mode aggregation, height packing, natural/real source scales, and
   arbitrary inverse source-power bounds are formal for a certified packet.
4. `ChenGuptaLiProposition46.lean` closes the certified-packet Proposition 4.6 reduction. It
   leaves only the positive part of the nonzero-frequency sum; it does not prove that actual
   selected rows instantiate the packet.
5. Proposition 5.1's full `S1` stratum is closed, not merely one representative ray.
   `ChenGuptaLiProposition51AxialSourcePower.lean` proves the literal `X^(-10)` saving on one
   complete punctured axis. `ChenGuptaLiProposition51Cyclic.lean` and
   `ChenGuptaLiProposition51CyclicAxes.lean` transport the result by exact cyclic symmetry.
   `ChenGuptaLiProposition51S1Reassembly.lean` proves that `S1` is the disjoint union of the
   three axial rays, establishes absolute convergence and the exact mass split, and proves the
   complete `S1` bound with the closed `3 * X^(-10)` envelope.
6. The Lemma 6.2 chain constructs the actual Mellin kernel and initial identity, proves functional
   equation/reflection, principal and nonprincipal contour shifts, ramified Euler and conductor
   factors, horizontal-edge and truncated-tail bounds, and both source time regimes with literal
   floor cutoffs and windows. `ChenGuptaLiLemma62RootNumberNorm.lean` proves primitive root numbers
   have norm one from exact finite cyclic Parseval. `ChenGuptaLiLemma62TailFunctionalCompact.lean`
   joins high and compact ordinates into an all-ordinate far-left functional-factor estimate, and
   `ChenGuptaLiLemma62TailAllConductorBounds.lean` retains the conductor-sensitive tail at every
   ordinate. `ChenGuptaLiLemma62TailRapidTruncation.lean` strengthens the literal far-left
   integrand to arbitrary polynomial ordinate decay after increasing Mellin order. The large- and
   small-time chains separately carry length, primitive conductor,
   imprimitive Euler quotient, cutoff, and height through cancellation/reassociation, choose a
   certified natural contour depth, and conclude the literal truncated `I2` bound
   `C * X^(-200)` in both regimes. `ChenGuptaLiLemma62ReflectedReassembly.lean` moves the finite
   part to the critical line and gives the entire small-time reflected side an `X^(-200)` error;
   `ChenGuptaLiLemma62NonprincipalReassembly.lean` identifies the physical nonprincipal sum with
   that side. Working-tree `ChenGuptaLiLemma62FiniteWindowBound.lean` bounds the surviving critical
   window by `C N^(1/2)` times the norm integral of the literal inverse-character Dirichlet prefix;
   it isolates but does not bound that prefix integral. Far-left tails and reassembly are closed;
   the prefix window, remaining terms, and all-parameter aggregation are not.
7. The displayed terminal zero-density exponent arithmetic is closed once the analytic two-term
   estimate is supplied.

**Open core.** There are two equivalent-scale producer targets:

- On the CGL branch, instantiate actual selected rows, control `S2/S3`, bound the isolated inverse-
  character Dirichlet-prefix window and any other non-tail Lemma 6.2 terms, then aggregate every
  primitive family into an absolute strict-subquantum census.
- On the energy branch, prove from the pre-divisor prime--Gamma source either an absolute
  strict-two loss or prime-summability of the paired Gamma-six collision current.

A normalized `o(N(T))` statement is insufficient: the first branch must cross the integer quantum
two, and the second must be upstream rather than an RH-equivalent global summability criterion.
The full `S1` frequency analysis, Poisson mechanics, root-number norm, both time-regime far-left
tail bounds, contour-depth choices, and finite exponent algebra are closed and must not be listed
as open.

Formal sources include `XiHorizontalCollision*.lean`,
`XiReflectionSelfIntersectionCharge.lean`, `EulerSquarefreeWickCompletedFockReflectionCensus.lean`,
`HedenmalmCoefficientFaithfulExteriorSourceContour.lean`, `PrimeTraceCriticalEnergyBudget.lean`,
`PrimeDiagonalSingularValues.lean`, and the `ChenGuptaLi*.lean` chain, especially
`ChenGuptaLiProposition46.lean`,
`ChenGuptaLiProposition51{AxialSourcePower,Cyclic,CyclicAxes,S1Reassembly}.lean`, and
`ChenGuptaLiLemma62*.lean`.

HC is nonclassical: its mechanism is source-resolution loss versus quantized reflection incidence,
not positivity of the classical explicit formula. The global strict-two law is itself RH-equivalent;
progress must come from the upstream arithmetic evaluation and absolute aggregation.

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

`SuzukiTaV2UpperHalfPlaneCofinalLimit.lean` removes the remaining compactness limitation on the
finite chart. Canonical actual Livsic coordinates admit a cofinal subsequence converging locally
uniformly on the whole upper half-plane to a Schur function anchored by `theta(i)=0`; every
holomorphic jet converges there. On the same subsequence the literal v2 projective characteristic
converges to the exact Mobius transform of that Livsic limit. Thus neither passage from one compact
ball to the full pole-free upper-half-plane chart nor compatibility between source and projective
coordinates is open. This theorem still selects an unspecified bounded Schur limit; it does not
identify it with the global Xi characteristic.

Three new modules close further moving parts on both sides of the desired limit.
`SuzukiDeBrangesDeficiencyKernel.lean` constructs the global `E=XiC+i XiC'` kernel, evaluates both
deficiency values and norms at `+-i`, proves the full boundary form for every phase, and at phase
`pi` identifies the spectral relation with the exact global quotient `XiC/E` away from its stated
poles. Thus the target deficiency algebra and its phase normalization are no longer open.
`SuzukiInverseNeumannLaplacian.lean` proves the prefix-Gram and explicit Neumann Green forms agree on
mean-zero data, equal the primitive `L2` energy, are nonnegative, satisfy the Neumann inverse
equations, and give Suzuki's generalized Rayleigh quotient. `SuzukiApertureFourierDecay.lean`
computes the finite-aperture exponential-basis transform and proves both `L1` and
integration-by-parts `1/|z|` bounds. `SuzukiCutoffLogWindow.lean` now assembles the head/tail estimate
into a vanishing logarithmic cutoff bound. `SuzukiRemainderFourierTransform.lean` evaluates the
regularized archimedean remainder transform, its symbol, and the required digamma asymptotic. These
close form-domain and archimedean-symbol connectors. None identifies
the canonical finite-aperture projective characteristic with the global de Branges target in the
cofinal limit, so no route count or endpoint changes.

**Open core.** Prove that the canonical normal-family limit is the global Xi projective target,
not an arbitrary bounded holomorphic subsequential limit, and propagate that identification over a
finite chart containing every Xi zero. Then establish reciprocal-chart convergence and eventual
compact zero-freeness at every target pole. Aperture schedule, phase pair, projective normalization,
upper-half-plane denominator control, whole-upper-half-plane subsequential compactness, compatible
Livsic/projective passage, and all finite-chart jets are closed. The missing step is
coefficient-faithful global limit identification plus the pole chart, not construction of
real-zero approximants, phase-pair provenance, reflection compatibility, tangent sign, deficiency
kernel algebra, inverse-Neumann form, or aperture Fourier decay. The old all-plane entire wall
stays terminal and cannot be repaired by finite holomorphic exponential gauges.

## Corpus-born candidate openings

These are Lean architectures, not literature-shaped suggestions. They are not counted as live until
their missing source handoff or completed divisor/RH landing is built independently of the zero tested.

### TK — thermodynamic thermal-Krylov moment limit

`PrimeArchThermalKrylovRH.lean` puts every finite nonnegative even-gap/KMS Wightman sequence in the full
trace-Hankel cone; convergence to normalized prime--archimedean moments implies RH. Strict source
Hankel determinants exclude one fixed finite system. Open core: source-derived growing KMS family.

### BSH — Boolean Sonin full-history adjoint-mate fracture

Working-tree `BooleanSoninFullHistory.lean` proves an infinite paired, nonphysical selector for any reciprocal
contraction section. Binary-history energy is exactly `(||lambda||^2 + ||lambda||^-2)^N ||y_0||^2`;
simultaneous relative smallness of adjoint and algebraic-inverse mate defects forces `||lambda||=1`.
For `lambda=r^(rho-1/2)` at nontrivial scale, this is `Re(rho)=1/2`. Candidate only: no theorem builds
the section from literal Sonin/prime--Gamma source or makes both defects small. Open core: construct it
before divisor fitting, retain the coefficient-faithful Xi dilation ray, and prove two-mate smallness.

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
comparison. `MonicOrthoExtremalComparison.lean` transfers uniform moment-form
comparisons to monic norms and Jacobi coefficients, but supplies no such arithmetic comparison.
Current code is endpoint and generic variational infrastructure, not an approximation theorem.

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

`XiMobiusSchurCalkinAxisSeparation.lean` proves the genuine prime-by-depth Möbius Schur synthesis
is Hilbert--Schmidt and compact, but lifting any nonzero Gram coefficient to an infinite Sonin
corner is noncompact. Compactness of the prime/depth carrier therefore does not imply compactness
of the Sonin/Calkin seam.

**Open core.** Prove for the concrete archimedean feature the graph-domain membership and pointed
residue extension needed by the continuation square, then a nonexpansive pole-to-divisor covariance
or equivalent source estimate reaching the exact four-unit boundary norm through a
coefficient-faithful moving aperture beyond every bounded scalar differential-order scale. These clauses must be
derived before selecting a Xi divisor. A fixed finite/compact receiver is now formally impossible
because it sees asymptotically zero channel mass. Generic moving-node transports and the existing
coisometry do not prove this Xi-boundary transfer: they are compatible with the safe half-plane and
explicitly leave all RH-bearing gates untouched. MSC is a genuinely non-scalar source carrier, but
is source-isogenous to G/CCM and is not yet an independent live route. Its compact prime/depth
realization is not a shortcut to SEC or a compact Sonin receiver.

Formal sources: `Mobius{CoupledFeatureIncidence,SignedChannelIncidencePaperCertificate,SignedSchurComplexMultiplier,SquarefreeReciprocalProjectivePaperCertificate,SignedSchurTransferPaper,CenteredSchurBoundary,WeightedMertensVector,CenteredMertensLimit,CausalSourceLimit,ChannelCriticalMassEscapePaperCertificate,CriticalBoundaryLayerQuantiles,CriticalExponentialBoundaryLayerPaperCertificate}.lean`.

### EWQ-V — Euler--Wick completed matrix/jet orientation

**Architecture.** Literal prime-power residues enter paired quadratic replicas. Valuation-number
insertion restores the canonical Euler logarithmic coefficient, and archimedean completion produces
a global meromorphic two-channel matrix with determinant `Xi^2`. The non-scalar off-diagonal,
full analytic jet, mixed Hedenmalm crossing, and Fock rank census all detect horizontal grade.
A proof would require a pre-divisor source law orienting one of these non-scalar receivers.

**Proved.**

- The regular-orbit inverse Fourier landing, integral cell quantization, arbitrary-rank binary gauge
  towers, and coefficient-faithful replica-to-zeta/Xi handoff are exact. Finite auxiliary orbit
  dimension by itself imposes no divisibility on the original Xi multiplicity.
- `EulerSquarefreeWickGlobalMeromorphicMatrixLanding.lean` continues the ordered positive/opposite
  channels globally as a genuine meromorphic Pauli eigenmatrix with determinant exactly `Xi^2`.
  Continuation from `Re(s)>1` is therefore closed.
- `EulerSquarefreeWickCompletedJetBundleLanding.lean` constructs the countable full analytic jet:
  every coordinate has entire determinant `Xi^2`, some off-diagonal jet is nonzero at every point,
  and a point is a Xi divisor exactly when some nonzero jet matrix is square-zero. This is
  pre-divisor and needs no auxiliary zero-avoidance premise.
- `EulerSquarefreeWickCompletedJetOrientationRigidity.lean` proves the root-number/derivative-parity
  graded-real locus of the full jet is exactly the critical line; universal Xi-copy orientation is
  exactly RH. `EulerSquarefreeWickCompletedJetDivisorColor.lean` gives a nonzero
  dimension-preserving color on the original divisor and separates every free horizontal orbit,
  but that color is defined after divisor selection.
- `EulerSquarefreeWickCompletedFockOperatorLanding.lean` constructs the positive rank-one
  trace-class/Fock color. `EulerSquarefreeWickCompletedFockReflectionCensus.lean` proves rank
  quantum zero on-line and two off-line and identifies the finite multiplicity-squared census with
  HC's canonical reflection self-intersection charge.
- `EulerSquarefreeWickHedenmalmReflectionCrossing.lean` gives the coefficient-exact nonunitary
  mixed crossing: reflected crossing is negative self-energy, hence nonnegative exactly on the
  critical line. `EulerSquarefreeWickHedenmalmPauliCrossingNoGo.lean` proves ordinary positive
  Pauli/Wick memory can remain positive while this mixed contraction is negative.
- `EulerSquarefreeWickGammaSixConditionalExpectationRigidity.lean` proves the literal diagonal
  order-two gauge average is idempotent and retains the full checkerboard interaction, whereas
  completed Gamma-six dephasing is idempotent exactly at neutral horizontal grade. Gauge averaging
  and completed dephasing cannot be identified away from the critical line by formal positivity.
- `EulerSquarefreeWickHedenmalmExteriorCheckerboardNoGo.lean` closes the literal exterior
  checkerboard producer: after prime normalization its Cesaro limit is zero for every admissible
  reflected rectangle, even though the underlying Hedenmalm contour remains coefficient-faithful.
  The four-cell checkerboard therefore cannot orient the completed exterior crossing.

**Open core.** Construct from the arithmetic source, before choosing a Xi divisor, a nonunitary
magnitude-changing incidence or boundary law using an independent vacuum/source carrier, and prove
that it orients the mixed EWQ--Hedenmalm reflection crossing or the full completed jet. It must
return to the original Xi multiplicity without importing common zeros of auxiliary L-sectors
and without replacing orientation by determinant.

EWQ-V remains a candidate, not a live producer: source-to-global-matrix and source-to-full-jet
landings are complete, but every known orientation theorem is a classifier or post-divisor color.
Its Fock census fuses exactly with HC's receiver and changes no route count.

**Closed detours.** Lean excludes scalarization; auxiliary tensor-dimension divisibility; principal
one-variable jets; commuting formal involutions; nonnegative involutive coboundaries; coefficient-
unfaithful full shifts; literal Weyl orbits requiring simultaneous auxiliary zeros; genuine
finite-dimensional Artin positivity; vacuum synthesis from nonvacuum EWQ sectors; common-refinement
descent; arbitrary unitary complete-source gauge schedules; Gamma-six marginal repair; full-source
hypertranscendental descent; projective transgression; Route-P trace domination; and ordinary Wick
positivity or the prime-normalized exterior checkerboard as a substitute for mixed-incidence
positivity. A viable successor must be nonunitary, source-native, independent-vacuum, genuinely
mixed, and retain its interaction before the checkerboard Cesaro normalization erases it.

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
infinite nonphysical candidate, not live. The compact Möbius prime/depth carrier in MSC does not
supply this theorem: `XiMobiusSchurCalkinAxisSeparation.lean` proves a nonzero infinite Sonin
corner lift is noncompact.

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

- **Even-shift screw positivity is terminal.** `ScrewShiftXiValueIdentity.lean` identifies the
  Laplace transform of the literal even-shift filtered screw source exactly with
  `logDeriv xi(s) - logDeriv xi(s+2)` in its half-plane. `ShiftedScrewNegativeWitness.lean`
  constructs an explicit damped-sine packet whose scaled quadratic value tends to `-1/4`, hence
  is eventually negative. This source identity remains useful, but raw shifted-screw positivity is
  false. Any SP-E/SV2/C1 use must retain signed atomic--regular cancellation or a source-derived
  relative renormalization.

- **Finite representation/geometric toolkits do not form RH producers.** Borel--Weil, Gauss--Bonnet,
  HLS, Hilbert irreducibility, finite Hall/Pollard, augmented homology, Cartier/co-Lie,
  Kleinbock--Margulis, and finite-`SU` modules close substantial source-independent mathematics.
  Haferkamp modules now phase-normalize/lift finite Clifford words, prove every nonidentity Pauli
  label in a backward light cone is carried by one ordered Clifford subword to literal root-only
  `Z`; terminal-block code embeds that transport in a full light-cone block while
  retaining a selected root-targeting gate. `HaferkampTerminalPauliPhase.lean` realizes its local
  `I tensor Z` direction as an explicit differentiable `SU(4)` path. Temporal rank/merge laws are exact.
  Bures--Wasserstein modules prove operator geometric-mean symmetry, monotonicity, arithmetic/geometric/harmonic and Loewner bounds, and Wasserstein-equation equivalence; extensions add strict square-root concavity and Etemadi recursion. Hadamard modules prove NPC geodesic uniqueness and nonexpansive Busemann flow; extensions add linear flow, quasi-firm composition, and fixed-point convergence. Hodge edge-cochains identify coercivity exactly with absence of harmonic modes and show those modes undamped; interaction is cancelling and obeys exact forced-dissipation energy identity. A finite controlled-phase Choi theorem gives a product-unitary distance gap. None has arithmetic occurrence or Xi landing.
  Complete-pairing/Wick/vacuum, signed-position
  pairing/Pfaffian combinatorics and abstract parity-Rayleigh decompositions are exact. BZ bridges
  identify Suzuki's two-height wall Gram and the two-level shifted-Xi Jacobi source with rank-one
  BZ residues, then reindex the nilpotent residue as Suzuki/Heisenberg flow. The apparent Lax
  continuation is now sharply separated: `BelinskiZakharovXiJacobiResidueSeparation.lean` proves
  the shifted-Xi Jacobi boundary residue meets the canonical nilpotent BZ residue family only when
  its coefficient is zero. Generic rank-one Xi forcing therefore cannot be substituted into that
  nilpotent Lax family. This closes the naive BZ bridge negatively rather than opening an RH route.
  The Xi mass profile also solves the flat Kerr--Newman scalar wave equation. Kerr--Newman has explicit Maxwell
  antisymmetry, duality-invariant trace-free stress, Rainich square law, and algebraic Einstein-form
  bridges, but no curvature-derived arithmetic occurrence. Positive quantized charged gaps are
  finite Pochhammer/differential-algebraic orbits; nonintegral-gap response and clock are
  hypertranscendental. `KerrNewmanQuantizedOddGapAdS2Bridge.lean` identifies admissible odd sectors
  across Kerr/scalaron/AdS2; `CoordinateCurvature.lean` and
  `KerrNewmanBZDressedCoordinateEinsteinBridge.lean` prove the flat BZ lift has zero coordinate
  curvature, while the Boyer--Lindquist module proves local smoothness only on its honest
  denominator locus. `KerrNewmanXiMassKleinGordonBridge.lean` now identifies the coordinate-
  weighted flat-wave profile with the existing Xi-mass prime-tail profile and proves that uniform
  line-boundedness of its Green--Stokes current is equivalent to RH. The wave equation supplies no
  such bound, and no curved/Boyer--Lindquist arithmetic occurrence is proved. This is an exact
  physical receiver for an existing prime-tail criterion, not an independent producer, route, or
  candidate. Parity splitting still orients neither floor, and Wick expansion supplies no source law.
  Dai--Yoshikawa modules now form a degeneration toolkit: power--exponential suprema, annular Laurent
  pairings and vanishing-cycle substitution, block-determinant/exponential-integral asymptotics,
  smooth convex transition, uniform spectral tails, Gaussian Duhamel constants, heat-trace tails,
  Gronwall/Lojasiewicz bounds, logarithmic cutoff energy, Rayleigh metric comparison, spectral heat
  Cauchy--Schwarz, normalization-Euler defect, Gram positivity, and regularized heat
  log-determinant convergence. None has arithmetic
  occurrence or Xi landing.
- `XiCenteredOrderTwentyOneFourthTraceReduction.lean` proves each residual-annulus atom spends more
  than `3/100000` of fourth reciprocal trace; one off-line orbit spends more than `3/25000`.
  Therefore `normalizedPrimeArchMoment 1 <= 3/25000` empties that annulus and makes moment 20
  positive. No theorem proves this source cap. The result sharpens the finite prime--arch moment
  cone but remains a conditional reduction, not a producer or new route.
- `XiWardCubicPositiveShiftArithmeticCovariance.lean` closes a source-first cross-route connector. On opposite Euler chambers the reflection--Loewner kernel is exactly the positive-real-shift
  quotient of the completed pole--Gamma--von-Mangoldt current; its diagonal finite part is the
  derivative, and continuation to a divisor reads the normalized discrete derivative of Xi
  multiplicity, with positive charge at a positive left translation boundary. This gives G/HC/CLG
  exact source provenance and divisor transgression, but proves neither the height-local `4/25`
  trace ceiling nor a pre-divisor orientation law; no route is added.
- **ABHN infrastructure remains pre-route.** Lean now has substantially more than cyclic toy
  algebra. Brauer operations, cyclic `H^2)/norm quotients, cyclic-algebra descent and splitting,
  scalar-extension functoriality, central-simple algebra packages, fraction-field orders, and
  Azumaya envelopes/base change are exact. Every finite free fraction-field CSA model becomes
  Azumaya after principal localization; working-tree `TwoPrincipalOpenGenericFiber.lean` upgrades
  a fraction-field CSA to a two-stage principal-open Azumaya model while preserving its generic fibre.
  Completed-place transport detects dimensions, kernels, ranges, eigenmultiplicities, centralizers,
  trace forms, nilpotence, idempotents, ideals, and related finite algebraic invariants; ramified
  height-one primes and number-field finite places are proved finite and identified through the
  different (`HasseFiniteRamification.lean`).
  `MilnorGlobalReciprocity.lean` proves the projective-line local--global residue sequence in every
  positive Milnor degree and the degree-two Hasse exactness/approximation law.
  `NonarchimedeanLocalFieldQuadraticGaloisH2Brauer.lean` constructs the concrete quadratic local
  cohomology-to-Brauer map and proves splitting over the defining unramified extension.
  `AlgebraicClosureBrauerSplit.lean` proves every Brauer class splits over an algebraic closure,
  while `ContinuousGaloisCohomology.lean` constructs the discrete-unit continuous Galois module,
  degree-two cohomology objects, open stabilizers, and exact degree-zero invariants.

  The rational Connes--Consani specialization now transports Brauer classes and any future
  `Br(Q_p) -> Q/Z` local invariant across the canonical p-adic field equivalence, identifies every
  local residue field with the prime field, and proves every integral Azumaya residue class split
  (`CCMRationalAdelicAzumayaResidue.lean`). `AzumayaFiniteResidueFiber.lean` extends the split-fibre
  endpoint to arbitrary finite residue fields, finite places and completions of number fields,
  finite and infinite places of finite-constant rational function fields, and finite-coefficient
  Laurent series. `CCMRationalAdelicFiniteResidueBrauerObstruction.lean` also yields a sharp no-go: every additive complex observable
  of that finite-residue Brauer group is zero, whereas the local Tate unit-ball zeta integral is
  nonzero on `Re(s)>0`. A CCM/C1/L comparison cannot factor only through finite residue Brauer
  data; it must retain ramification, a boundary class, or other non-residual information.
  `GlobalCSAResidueFiniteRamification.lean` constructs number-field and
  finite-constant function-field CSA models whose height-one residue fibres split outside a finite
  divisor set. This closes residue-model finite ramification, not completed generic-fibre Brauer comparison.

  Missing mathematics is the actual p-adic local invariant, general local continuous-`H^2`/Brauer
  comparison, number-field restricted-product/global ABHN exact sequence, and—decisively for RH—any
  coefficient-faithful occurrence on the completed prime--Gamma/Möbius source with an Xi landing.
  None of these generic local--global algebra theorems mentions or constructs that source, so they
  strengthen a possible future arithmetic specialization but add neither live route nor candidate.
- Several new exact interfaces close local mechanics without creating producers.
  `PerronUniformFlankProducer.lean` derives carrier flank mass and horizontal escape from uniform
  left-flank bounds plus one quiet-height exhaustion, then proves the exact support law: geometric
  flank radius `R` forces every nonzero Dirichlet coefficient index `n <= R`. No theorem supplies
  those hypotheses for a completed infinite arithmetic carrier, so this is a support-exclusion
  adapter for T1/F2/U rather than a route. `DeningerDynSysPointedMultiplicativeRoot.lean` proves an
  `N`-th root of a pointed multiplicative map exists exactly when the map is trivial on `mu_N`; for
  algebraically closed fields with finite unit kernel this is exactly a cardinal divisibility law.
  It strengthens IW/L algebra but confirms that multiplicative-root existence reads divisibility
  rather than produces it. The Deninger dynamics modules close invariant-point orbit descent,
  rational-Witt Galois descent, Verschiebung rationality, local perfection, and working-tree
  monoid-ring continuity. Working-tree `DeningerDynSysWittRingAction.lean` further proves the actual
  rational-Witt action has open stabilizers, restriction to invariants is surjective, and two
  complex points restrict equally exactly when related by the acting group. Reduced-monoid and
  valued-point modules close their abstract point functors.
  None constructs the completed Xi source or Route L's singular physical comparison.
  `MonotoneDisjointInfiSup.lean`,
  `MinimalCompleteSystem.lean`, and `MinimalCompleteSystemChain.lean` formalize Burnol's abstract
  Sonine lattice-density and complete/minimal/biorthogonal machinery, including a complete minimal
  system whose dual is not complete. Along any decreasing projected chain, minimality is downward
  closed, completeness is upward closed, and the two threshold indices have their exact strict-side
  laws. No actual all-prime Sonin moment weld is constructed, so F2's open core is unchanged.
  `SuzukiWeilLerchBlock.lean` gives the absolutely
  convergent regularized Lerch difference, removes its apparent `0/0` by exact factorization, and
  proves the digamma bridge and base-point continuity. This closes an archimedean connector for
  CCM/O/SV2, not the global ground/limit selection. Finally, the Euler--Riesz dilation modules prove
  unit scale stationary but strictly unstable and realize its negative curvature as a Bourgain
  square-root-curve quadratic phase. `ExponentialMemoryTransportCurvature.lean` corrects another generic transport interface:
  reconstructed two-time commutators only attenuate existing noncommutativity, the even defect
  loses orientation, and the signed odd response belongs to the present--memory lag curvature.
  `CompactOrbitQuotientMetric.lean` supplies the exact compact
  isometric-orbit quotient metric used in Deninger-style dynamics. None of these modules contains
  an arithmetic source occurrence or Xi landing, so no route or candidate is added.
- **DQPT is an exact classifier/landing, not an RH route.** Paired eta tail has sharp half-next-term normal form; zero partial-sum rate is `Re(s)*log 2`, but zero free energy is `log 2` for every strip zero. `DQPTChiOrder.lean` proves `|chi(beta+it)| = Theta(t^(1/2-beta))`, so the functional-equation multiplier records abscissa but does not select it. `DQPTReflectedSlope.lean` proves the exact first normal and equality of reflected raw rates exactly at `beta=1/2`; no declaration derives that equality upstream. `RiemannSourceDQPTMemoryLag.lean` now inserts the canonical horizontal Gamma/co-Poisson parameter into a bounded Pauli memory-lag reporter whose zero locus is exactly the critical line, but it is defined on an Xi divisor fibre and universal annihilation is proved equivalent to RH. Exact observables, eta/zeta derivative bounds, and this coefficient-faithful physical receiver survive; no independent annihilation producer exists.
- **Fractional-part/trigonometric extraction is terminal.** Lean proves exact fractional-part integral, four real/reflected strip-zero equations, and strip-local reflection multiplier. Unit-interval integration requires the first-primitive jump sum; deleting it diverges. Global zero-locus reflection fails at trivial zeros because archimedean factor vanishes. Correct identities supply no critical-line selector.
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
- **Gamma-place analysis is largely connector-complete.** Wendel, real/vertical ratio-root laws,
  quantitative trigamma curvature, finite Gamma-product/Selberg root asymptotics, rank-one sine
  recurrence, and whole-line zeta-chi growth are formal. `EulerMascheroniGaussKernel.lean` cancels
  both logarithmic singularities in Euler's constant integral;
  `DigammaIntegralRepresentation.lean` proves full Gauss representation for `Re(s)>0`, including
  domination, sum/integral interchange, and real archimedean specialization. These close Gamma-side
  inputs for D2/HC/SV2 and T1's contour majorant, but supply no prime coupling, completed-source
  order, or signed short Möbius cancellation; no route is added.
- **Finite character-family infrastructure remains below HC/E/T producer level.** Exact character
  orthogonality, quadratic CRT/Jacobi/Kronecker identification, primitive and fixed-cutoff Jensen
  zero counts, and Bondarenko--Heap finite Fourier/incidence/Ramanujan estimates are formal. Every
  zero-density constant still depends on character, modulus, or fixed cutoff. These results provide
  finite correlation adapters, not conductor/height-uniform density, signed critical cancellation,
  GRH, or a divisor-exclusion producer.
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
  `XiReciprocalCliffordSquare.lean` makes the terminal point exact: existence of the bare reciprocal-
  Xi Clifford splitting is equivalent to RH. No route is added.
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
  drift. `PrimeSquareWoldScaleDominationRigidity.lean` now identifies `c` with the literal centered
  Xi/Wold horizontal coordinate and closes the tempting comparison negatively: fixed Wold
  first-trace domination holds exactly at `c=0`, and its universal Xi-copy form is exactly RH.
  Thus off-neutral drift creates a cofinal superessential signal, but bounding that signal by the
  Wold first-trace scale is not an upstream producer. The positive survivor is an exact
  scale-rigidity classifier. A viable successor must change the comparison scale/topology or use a
  signed global aggregate; the stated first-trace pre-route is terminal and adds no candidate.
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
- Higgs/Goldstone applications classify invisible finite zero modes and non-`ell2` arithmetic
  boundaries, reinforcing O/G/L/U's singular-boundary diagnosis without a completed source or Xi
  endpoint. Generic shell/Noether, Schatten determinant/derivative, Stieltjes recovery, spectral
  action, eigenbranch, and dephasing modules close finite analytic/operator adapters. They select no
  arithmetic parameter, prove no completed-source sign, and supply no cofinal RH route.
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
- Endpoint-complete finite Hamiltonian leaves, exponential-polynomial/determinant graph closure,
  Cassidy `sl2`, Burnside, torsor separation, and difference semi-invariant/Riccati reductions are
  exact generic carriers. None is specialized to completed arithmetic source or an RH reader; they
  do not promote PPM/IRK/HJ/AF.
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
  corpus has neither the remaining two-to-one fibre bound with actual critical-family
  primitivity/source occurrence nor a coefficient-faithful Xi-divisor handoff.
  `CriticalSheetJetUnit.lean` and `CriticalSheetScaleUnit.lean` prove every compatible sheet jet has
  unit constant term and every sheet sends source scale to a unit of the upper Schur valuation
  ring. The later residue chain proves equal reduced labels induce equal residues on every raw,
  normalized, and Schur coordinate and on the whole Schur coordinate ring; a sheet with canonical
  label cuts out exactly the source Schur place (`CriticalSheet{ResidueCongruence,
  SchurCoordinateResidue,CoordRingResidue,SchurPlacePullback}.lean`).
  `CriticalSheetPlaceRamificationIndex.lean` transports its centre through the sheet field
  equivalence and proves that place has ramification index exactly two. These close sheetwise
  normalization, place identification, and ramification index.
  `CriticalSchurInertiaOrderTwo.lean` proves every sheet has ramification index at most two and the
  entire critical Schur inertia group has order exactly two: the local horizon is unconditionally
  a simple fold. This still does not prove the cardinal two-to-one reduced fibre bound or global
  primitivity. Separately, cube/root-family modules prove full symmetric Galois groups once
  every generic hypercube edge swap is realized, construct those swaps in independent transverse
  directions, split every one-direction characteristic polynomial over its radical extension, and
  identify the canonical power-series root after direction reduction. Fraction-field and
  generated-root-family transport now carry a realized permutation across matching embeddings.
  `TwoLocalIntegerWitness.lean` and working-tree `TwoLocalRigidSpectrum.lean` give an explicit
  traceless integral two-local Hamiltonian with full symmetric Galois group, cyclic nonzero vectors,
  and only its rational trace relation. No theorem matches that
  generic witness to the actual critical Schur/Xi source; source-faithful occurrence and Xi landing
  remain absent.
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
- Place-peel/shear-degree, twisted-chain growth, rational iteration, marked-word/circuit hardness,
  rational orbit certification, and exact/approximate quantum-return modules create generic
  action/rigidity clocks only. `ClosedPrimeBraid.lean` confirms scalar closure erases a framed
  two-prime phase. Without prime--Gamma occurrence, Xi landing, or collision-order source law, these
  are infrastructure—not routes or candidates.
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
  no longer open. `AbeUniformDampingNoGo.lean`, `AbeDerivativeDampingNoGo.lean`, and
  `AbeGaussianSmallDivisorNoGo.lean` show that pointwise strict damping has no uniform gap, cannot
  absorb the first derivative factor, and is not repaired by a Gaussian lattice weight when phase
  deficits are super-Gaussianly small. `QuasiAbelianBoundedSeedNoGo.lean` also closes the rank-zero
  shortcut by multivariate Liouville.
  The positive survivor is now exact. `QuasiAbelianConvergentDampedExtension.lean` transports
  all-order jet ampleness from packetwise convergence of complement jet remainders. Graded
  Vandermonde/leading-determinant and normalized Tannery/determinant
  modules prove that positive termwise phases plus summable coefficients and an actual normalized
  entrywise expansion give eventual invertibility without a uniform gap. Working-tree
  `AbeExponentialDampingMultiplier.lean` constructs the invariant normalized entire multiplier but
  explicitly supplies no estimate or asymptotic. The required multiplier-derived
  expansion remains unconstructed. These results strengthen quasi-abelian/MEG carrier formation,
  but supply no completed arithmetic occurrence, functional-equation action, or Xi reader. They
  create no RH route and do not revive AP or AF.
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
- `CompleteHistoryInvariantMetricCone.lean` classifies every positive invariant metric
  for a finite transport history as a fixed invariant metric multiplied by a positive
  self-adjoint commutant factor; scalar-ray uniqueness is exactly absence of nonscalar such factors.
  This sharpens metric-selection language for G/L/P but supplies neither arithmetic transport
  occurrence nor orientation of its commutant cone. It is not a new RH route.
- The Fermi golden-rule modules close the continuum first-order resonance kernel, a finite
  Schrödinger/Duhamel model with error control, the normalized time-domain Dirac limit, the
  energy-domain self-energy/Poisson boundary rate, and equality of the two rates
  (`GoldenRuleLimit.lean`, `FermiGoldenRule.lean`, `GoldenRuleSelfEnergy.lean`). Without a literal
  prime--Gamma spectral measure and a Xi
  collision/position reader this is universal analytic infrastructure, not an HC producer or a new
  route.
- `CoupledShortcutCollision.lean` proves a deterministic finite-dimensional capacity statement:
  the embedded path patch is diagonal, and every Hamiltonian in a separated carrier tube keeps the
  uniform seed below the explicit spectral-collision bound. It has no completed arithmetic source,
  divisor reader, or infinite/cofinal passage, so it is not an RH route or an HC producer.
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
| IW internal SEM Weyl / pointed multiplicative roots | SEM model existence is exactly `2^k` divisibility of actual hole count, depends only on dimension, and universal/cofinal existence is exactly RH. Abstract Deninger `N`-th roots likewise exist exactly by roots-of-unity kernel divisibility. | Exact cyclic clock--shift realization, unique pointed-root construction, and divisibility classification; useful certificates, not producers. |
| AP Big-Witt/Scaling-Site power orbit | Big-Witt reporter law holds, but Arakelov square lift has a pole at `1/2`, so no global entire-source pullback exists; actual Scaling-Site covers act differently; fixed-receiver stability/preperiodicity are RH-equivalent. | Source-first reporter, changed-receiver scaling, and abstract Deninger rational-Witt/Galois/Verschiebung dynamics survive; none supplies completed-Xi occurrence. |
| TD/C1 raw positive completion | Four raw reflected critical Stokes atoms already exceed completed zeroth mass; no finite positive supercarrier dominating them can equal completed seam germ. | Any representing carrier must delete/reweight raw atoms or introduce signed negative correction before final positivity. |
| finite-residue CCM/ABHN landing | Rational local residue Brauer groups are trivial; every additive complex residue observable is zero, while the local Tate unit-ball source is nonzero on `Re(s)>0`. | Global CSA residue fibres now split outside finite divisors. A successor must retain completed generic-fibre, ramified, boundary, or other non-residual Brauer data. |
| EWQ scalar/unitary/auxiliary/checkerboard orientation producers | Scalarization and determinant erase odd orientation. Auxiliary tensor dimension, Weyl/common-refinement descent, one-variable jets, formal involutions, nonnegative coboundaries, genuine Artin positivity, nonvacuum vacuum synthesis, unitary complete-source gauges, Gamma-six marginal repair, ordinary Wick positivity, and prime-normalized exterior checkerboard Cesaro do not orient the completed mixed crossing; several are equivalent to neutral grade or RH, while checkerboard Cesaro is identically zero. | Global meromorphic matrix, full analytic jet, dimension-preserving divisor color, Fock/HC rank census, and nonunitary Hedenmalm crossing survive as exact receivers. Missing producer is a pre-divisor nonunitary magnitude-changing incidence using an independent source vacuum before normalization. |
| AF class-law scale-orbit | Convergent abelian class-law certificate exists iff centered rate is zero; global certificates on all Xi copies exist iff RH. | Terminal rigidity/selection theorem; successor must change interface to singular/infinite-action or genuinely global aggregate law. |
| prime-square-to-Wold first-trace domination | Every positive admissible drift escapes every fixed Wold first-trace budget; domination holds exactly at neutral drift and universally on Xi copies exactly under RH. | Exact prime-square superessential scale classifier; successor must change scale/topology or use signed global aggregation. |
| source-horizontal annealing | Pre-vacuum invariance is RH; post-vacuum annealing moves divisor packets; every nonzero exponent preserves strict-right second-Cartier orbit escape, while universal boundedness is `alpha=0 or RH`. | Exact staging and orbit firewall; P/G must derive singular moderation from source, not attenuation. |
| fixed Route-P wall/theta jet identification | Source-native wall signed-square quadratic jet is `-16/35`, but canonical completed-theta curvature is strictly different. | Wall jet survives only with separately source-derived rescaling/correction; direct fixed-canonical landing is closed. |
| SNR external-aperture nonlinear renewal | The explicit parabolic schedule synchronizes every degree, but normalized Weyl renewal is definitionally the externally selected aperture height; its positive range is all of `(0,infinity)` and is independent of the shifted-Xi moment source. | Exact Schwarz-normal coordinate and parabolic receiver survive. Any successor must use a source-native quantity fixed before reporter aperture is chosen; that successor is not SNR. |
| formation-potential/Kummer/inertia selectors | Local formation charge is analytic order of zeta. A coherent Xi Kummer tower is unconditional on `Re(s)>1`; extending it to `Re(s)>1/2`, equivariant off-line root dissolution, holomorphic formation potential, Mackey flatness, pro-Kummer boundedness/summability, or global-inertia ideal membership all select zero charge and are RH-equivalent or imply RH. | Exact common integer-charge classification and unconditional Euler-region tower. A successor needs an independently constructed literal arithmetic formation law, not another representation of vanishing charge. |
| AGC all-grade Marcinkiewicz selector | Higher nonlinear Euler and tangent grades have bounded mass and vanish in the quotient; all-grade critical/off-line classification is already grade-one classification. | Exact grade-one retract and tail bounds; successor must change topology or use singular boundary/graph data. |
| reciprocal-Xi Clifford split | Bare Super-Poincare/Clifford splitting exists exactly under RH; algebraic `N=2` packaging is not an upstream source construction. | Concrete projection-phase, Deninger-cochain, and `Q8` odd-sector realizations remain reusable algebraic models. |
| Hedenmalm ordinary-`L2` pre-quasi realization | No nonzero momentum-symmetric theta-null Hilbert--Gram form on full Schwartz source can be a positive embedding of proposed pre-quasi Gelfand pair in ordinary `L2`. | Every closed successor must omit a Schwartz source direction or change realization; singular/indefinite boundary carriers remain unexcluded. |
| TSR scalar causal reflection | Canonical theta square-rate reader exists and samples every physical heat exponential exactly, but direct action on reflected theta half is zero; reorientation only duplicates positive half. | Exact infinite source-side biorthogonal reader survives. Any RH successor needs a distinct completed second channel and Xi-divisor landing. |
| weighted-Mertens half-unit tower as producer | One exponent gives one zero-free half-plane, but the full tower `0<=alpha<1/2` is exactly RH; it cannot be invoked as an upstream estimate. | Exact causal transform, one-moment transfer, and invariant half-unit prelimit deficit guide MSC/G aperture research. |
| Suzuki v2 entire characteristic wall | Displayed target has an unavoidable pole, so no all-plane locally uniform limit of entire real-zero characteristics exists; finite holomorphic exponential gauges do not remove it. | Actual entire real-zero Suzuki characteristics now exist; live SV2 uses the corrected two-chart spherical wall. |
| Deninger finite quaternionic real descent | Quaternionic anti-linear square `-1` forces even complex multiplicity, but root number `-1` forces odd central order; order-equals-multiplicity real symplectic realization is impossible. | Legacy radical field is proved degree eight, Galois, with group `Q8`. The source-authenticated Serre field is also now degree eight, Galois with group `Q8`, and carries the literal pulled-back two-dimensional symplectic Artin representation. Only its global Artin epsilon-factor calculation remains; even if supplied, it certifies the parity obstruction rather than reviving finite real descent. |
| direct prime Ising | Raw/scalar-normalized finite balanced tree partitions cannot converge locally uniformly to XiC; rank growth forces scale collapse. | Only singular critical rescaling outside fixed modal closure could be new. |
| compact Thorin/Markov | Compact Thorin and Markov representations are RH-equivalent; canonical measure unique; theta-likelihood candidate not infinitely divisible. | Upstream positive source measure only, not alternative canonical measure. |
| DQPT critical-line extraction | Exact eta/chi rates record `Re(s)`; reflected equality is the critical line, not an upstream law. The coefficient-faithful Pauli memory-lag landing also vanishes exactly on line, but its universal annihilation is exactly RH. | Sharp asymptotic/observable classifiers and bounded physical memory-lag receiver survive; no independent annihilation law. |
| fractional-part/trigonometric extraction | Four strip-zero integral equations do not select the abscissa. Omitting unit-interval jump terms makes the claimed limit diverge; global reflection of zeta's zero locus fails at trivial zeros. | Correct fractional-part representation, jump-complete interval expansion, and strip-local reflection multiplier. |

### Route R exact closure

`RouteRTerminalProducerClassification.lean` proves intrinsic death and RH-equivalence of every
surviving producer/Calkin/physical interface. `RouteRPreDivisorGammaCoronaGlobalizationNoGo.lean`
excludes a pre-divisor Gamma-corona globalizer. `RouteRHyperbolicGaugeQuarticPhysicalProducer.lean`
constructs unconditional quartic landing and proves quadratic comparison no-go.
`RouteRSquarefullStokesSummabilityProducer.lean` gives strongest scalar survivor: one explicit
reflected level-two primewise Stokes boundary is summable exactly when `Re(rho)=1/2`; its global
normality on all Xi divisors is again RH-equivalent, not proved. R contributed novel invariants,
but no intrinsic producer survives; it is closed negatively as an RH route.

### IW, AP, TD/C1, EWQ, AF, and SNR exact closures

`SEMDyadicWeylExistenceClassification.lean` proves internal SEM Weyl-model existence iff dyadic
hole-count divisibility, fixed-dimension source-blindness, and all-level/cofinal equivalence with RH.
IW cannot generate the divisibility it was meant to explain; only its exact cyclic clock--shift
representation of already-present divisibility survives.

`BigWittArakelovSourceEndomorphismTerminal.lean` proves the source-first Big-Witt reporter, then
closes every fixed completed-Xi handoff: global entire pullback is impossible, actual Scaling-Site
cover differs from power lift, Euler Adams gives dilation rather than ramification, half-scaling
changes receiver, and remaining fixed-receiver conditions are RH-equivalent. AP is exhausted.

`GammaSewnMobiusApertureStokesPositiveCompletionNoGo.lean` closes TD/C1's canonical raw-positive/passive handoff and proves exact non-domination survivor; it does not close corrected signed/indefinite C1. EWQ's completed noncommutative landing is now closed: the global meromorphic matrix has determinant `Xi^2`, and the full analytic jet detects every Xi divisor without auxiliary zero avoidance. What remains is not continuation or finite gauge formation. Lean's Artin, Weyl, vacuum-superselection, common-refinement, complete-resolution, Gamma-six hypertranscendental, projective-transgression, and Pauli-crossing no-gos show that scalar, unitary, auxiliary-sector, marginal, and ordinary-positive constructions cannot orient that jet. The exact survivor is a pre-divisor nonunitary magnitude-changing mixed incidence using an independent source vacuum.
`SourceHorizontalAdaptiveFisherGlobalClassLawProducer.lean`
constructs neutral source certificate, proves certificate existence exactly at centered rate zero,
and proves global all-Xi-copy producer equivalent to RH. AF is therefore closed as independent
copywise convergent class-law mechanism, not promoted to live route.

`ThetaCuspTiltFluxWeilParitySchwarzPairParabolicRenewalWeld.lean` does close the former SNR
synchronization problem with one explicit parabolic schedule at every degree. But
`ThetaCuspTiltFluxWeilParitySchwarzPairParabolicRenewalUniversalityNoGo.lean` proves the resulting
normalized increment is exactly the externally chosen aperture height, has the entire positive
half-line as its range, and agrees with any prescribed positive target independently of the
completed shifted-Xi source. SNR is therefore terminal as an independent producer, not a new route
and not an AF revival. Its positive survivor is a sharp interface constraint: reporter aperture
must be selected after, and controlled by, a genuinely source-native invariant rather than serving
as the invariant itself.

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
- transfer of compactness from the prime-by-depth Möbius Schur axis to an infinite Sonin/Calkin
  seam: the former is Hilbert--Schmidt, while every nonzero Gram lift to an infinite Sonin corner
  is noncompact (`XiMobiusSchurCalkinAxisSeparation.lean`);
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
- raw positivity of the even-shift filtered screw form: its Laplace transform is the exact
  `logDeriv xi(s)-logDeriv xi(s+2)` source difference, but an explicit damped-sine packet has
  scaled quadratic limit `-1/4` (`ScrewShiftXiValueIdentity.lean`,
  `ShiftedScrewNegativeWitness.lean`);
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
presentation supplies source-side no-escape. T2 now sends an inverse-log adjacent defect through
arbitrary-order localization to the literal physical-slice second alternative on every strict
base-phase margin, but production on actual prime shells, critical summation, and signed continuation remain open;
its absolute critical graph topology is inconsistent with needed gap energy. CCM-FU reduces its
current to one discrete signed affine-checkpoint average whose slope jumps are negative exactly at
odd-prime-power endpoints and positive on their complement; analytic curvature and endpoint resets
are harmless. Gamma--Binet/Selberg, completed-Riesz graph, critical-chord, and adaptive cofinal
bridges identify its normalized limits with the weighted `psi-id` difference, unit-Riesz/HG, and
completed Chebyshev boundary; the second-grade normalized source quotient even tends to zero on an
explicit schedule. None bounds the moving affine current. G-CE exposes a separate first premise:
the prime-free divisor defect is `O(sqrt N)` and its exact signed Möbius-dilation Abel action is the
same coherent boundary moment, but its uniform normalized cancellation is open. O assembles
all matched interiors into one infinite PSD Fock carrier and
positive projective holonomy, leaving probe-ratio order and physical collar. Both show global coverage/reading, not local
cell formation, is obstruction. CGL has the finite Class-I/Class-II alternative, literal inverse-
incidence fibres, weighted first/third Gram reductions, complete three-residue/`Z^3` Poisson
identity, and the full certified-packet Proposition 4.6 bound. Its first Proposition 5.1 axial
carrier, both cyclic transports, and exact three-axis reassembly now close the entire `S1`
stratum with literal source-power saving. Both small- and large-time Lemma 6.2 far-left tails now
retain all conductor/cutoff/height factors and close at `X^-200`. Actual packet occurrence,
`S2/S3`, remaining non-tail uniform analysis, and height census remain.
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
non-equivariant Cayley depth, or projective monodromy/Chern charge. O makes mechanism exact: scalar
reflection erases odd wall orientation; odd-by-odd pairing retains it; two fixed Hermitian shears
recover the full complex orientation, and source-selected self-polarization turns their squared
norm into a determinant strictly negative off center. The fixed one-shear determinant is only
locally nonpositive and no positive linear cofinal finite part exists. Source-adaptive scalar sign
can survive; transporting its quadratic law into the linear Weil receiver is the new wall.
EWQ-V gives the complementary sharp fact: a PSD matrix density retains literal character orientation, but two positive gauge lifts share one diagonal Xi stream with opposite off-diagonals. Positivity is compatible with orientation; scalarization is irrecoverably two-to-one.
Working-tree `DirectionalWilsonReciprocity.lean` sharpens this firewall: every PSD normalized block
kernel has reverse links equal to adjoints, hence reverse Wilson trace is the conjugate of forward
trace and both real part and norm are orientation-blind. An explicit rational noncommuting sector
still has zero signed real directional contrast. Non-Abelian holonomy alone is therefore not
nonreciprocity; any Wilson successor needs an active non-Hermitian source law.

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

Route O has exact true ground and canonical finite heads. Local Schur completion is closed and
positive linear global accounting is excluded. Its global summable PSD kernel is now a positive
rank-two Schatten-one operator; a chiral exterior minor is a self-adjoint trace-class orientation
observable. A complex Dirac kernel line plus two fixed shears reads both source coordinates, and
self-polarization gives a finite-packet determinant strictly negative exactly off center. Remaining
theorem is coefficient-faithful landing of that quadratic signed scalar in the linear actual-head
floor, not a better trial vector or another order estimate. Across C1/G/O/U finite
sections and compactness are mostly closed; arithmetic order remains.

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

F2, BSH, G-CE, O's trace-free Fock/self-polarized Dirac opening, UEB, CLG/TTF, T2, PSRC, PBM, MSC, EWQ-V, SV2, PCS, SEC, and BPC form a second non-classical family: infinite paired/operator/graph or
analytic source followed by a singular, meromorphic, or homological boundary landing. MSC has the carrier but lacks pointed
divisor covariance. UEB has exact affine marking and a complete order-one Bezoutian classifier but
lacks source-produced kernel positivity. O constructs one global PSD kernel and exact projective
holonomy, then improves its two-coordinate readout to a source-self-polarized determinant with exact
global off-center sign. Its missing theorem is no longer scalar selection but landing that quadratic
determinant in the linear actual-head Weil producer. CLG/TTF turns the same logarithmic-derivative geometry into
exactly equivalent Euler-observability and literal theta-correlation-flux order problems, while
proving positive-shift flow and generic strict-log-concavity shortcuts impossible. Its entire
off-line obstruction is now localized by moving regular two-pole Cauchy packets with exact negative
source limit; missing law is cofinal source no-escape. W2C identifies that detector with canonical even--odd finite-aperture Weil
channels and retains every negative packet, but supplies no pre-divisor positivity. PSRC has exact
continued prime residue and dense finite Euler core, but closability
of its singular graph is already exactly RH. PBM retains quantized monodromy at infinity and proves
finite/local completion cannot carry it; absence of that charge is again exactly RH. EWQ-V now has
the global meromorphic matrix and countable completed jet, a dimension-preserving divisor color,
Fock/HC rank census, and exact nonunitary Hedenmalm crossing. What it lacks is a pre-divisor
source law orienting these receivers. Its no-go suite excludes scalar, unitary, auxiliary-vacuum,
common-refinement, marginal-dephasing, ordinary-Wick, and prime-normalized exterior-checkerboard
substitutes. SV2 has actual entire real-zero characteristics, a canonical paired projective family,
and compatible whole-upper-half-plane cofinal compactness with all jets; it lacks global target identification and the
reciprocal pole chart. PCS has an exact all-prime graph, spectral gap, and divisor boundary
complex but lacks a secondary class capable of seeing homology whose ordinary index is zero. SEC
has an exact end-coherence collapse and a canonical prime-ray Calkin endpoint, but lacks a source
law making the adjacent seam coboundaries eventually compact. BPC
has the exact positive susceptibility singularity and collar-to-RH transfer but lacks source
continuation through that collar. T2 has ordered-prime Wold
residual, exact prime-zeta/log-mesh/Chebyshev-error normal forms, residue-faithful continuation,
and an inverse-log-defect-to-literal-physical-slice second-count receiver on every strict
base-phase margin. It lacks production of that defect on actual prime shells, critical-weight summation, and signed continuation
through every strict subhalf strip.
None can be reduced to one finite positive object or one scalar
response without hitting a proved
firewall.

F2 is the cleanest source-to-source member of this family. Its open premise names neither a Xi zero
nor a divisor-built Gram: one literal positive all-prime operator moment curve must approach one
literal continued prime--Gamma moment germ. Corpus separately supplies the completed
trace-class source and positive prolate carrier, but trace realization is weaker than positivity of
all powers. This isolates a new recurring wall: matching scalar traces or first moments does not
place an entire target sequence inside a positive Hankel moment cone.

Remaining pre-routes reinforce that taxonomy rather than extend route count. Prime-Laplace Gamma
jets are an infinite paired clock with exact translation anomaly/Bianchi curvature, but the
coherent observer is unbounded. Prime-support Hodge theory says phase begins at cycles rather than
paths and finite positive-prime apartments are acyclic. Prime-square Fourier strata give a cofinal
two-level reflection law with exact type `|c|`, but proposed fixed Wold first-trace domination is
terminal: it holds only at neutral drift and universally exactly under RH. Grade--Lambert monodromy inversion has now crossed into PBM's
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
   Möbius/theta object (CCM-FU, G-CE, D2, E, Q, CLG/TTF, SP-E, SCE, T1, T2, HC).
2. **Ground-relative/nonlinear receiver landing:** control exact state selected by full operator and
   carry source sign through its actual reporter; O now has source-self-polarized sign but not its
   linear Weil landing (C1, O, G, U).
3. **Singular boundary descent:** physical comparison across completion boundary without losing
   coefficient, multiplicity, or orientation; for L this is the source-to-fixed-physical
   specialization of its already strict resolved boundary (G, L, P, U).
4. **Mixed-incidence control:** preserve cross terms or nonlinear coordinates diagonal energies
   erase (E, O, Q, HC, T1, CLG/TTF, EWQ-V).
5. **Cofinal synchronization:** one estimate uniform in moving pole/degree/aperture/height;
   CLG/TTF's exact two-pole escape and T2's canonical packet/count-energy assembly make diagonal escape the
   obstruction rather than bookkeeping (CCM-FU, C1, CLG/TTF, E, F2, O, SCE, T1, T2, U, SV2).
6. **Source-native internal dynamics or realization:** projective module, thermal family, corrected Stokes category, monodromy,
   singular depth action, operator leakage, or analytic continuation on literal completed source
   before divisor selection (TK, BSH, UEB, PSRC, PBM, SC, PPM, IRK, OPUC, HJ, BW, MSC, EWQ-V, PCS, SEC, BPC;
   pre-routes PLAC, EPC, MEG, ZGC, and SFP; W2C/de-Poissonization is a receiver/source bridge).
   Abstract Weyl/pointed-root existence, Arakelov power pullback, all-plane entire Suzuki
   convergence, finite-residue Brauer landing, prime-square first-trace domination, annealed-vacuum
   invariance, fixed wall/theta jet matching, and finite real quaternionic descent are terminal in
   their stated interfaces.

Fundamental remaining obstruction is not another equivalent criterion. Corpus already has many. It
is:

> derive favorable global order or discrete rigidity from literal completed source while retaining
> matrix/off-diagonal orientation and mixed incidence erased by scalarization, finite truncation,
> invariant-energy readout, and post-divisor fitting.

## Highest-value questions exposed by Lean

- **CCM-FU:** Can one fixed-`b` affine Suzuki checkpoint current be bounded uniformly in `H`,
  using cancellation between odd-prime-power negative jumps and complementary positive jumps rather
  than absolute estimates?
- **G-CE:** Can the unconditional `O(sqrt N)` prime-free divisor defect be propagated through the
  complete signed Möbius floor-dilation action to prove the normalized half-order Abel moment
  uniformly bounded?
- **C1:** Can literal normalized adelic cutoff traces be proved positive and convergent to the
  completed Weil distribution after a coefficient-faithful signed/non-dominating correction that
  controls the cofinal antisymmetric two-pole escape?
- **D2:** Can the sole positive-frequency prime--arch tail be controlled by a reflected
  signed/non-dominating source law after directed passivity and raw-positive completion fail?
- **E:** What exact source-predeclared squarefree relation realizes Ramaré incidence with unit
  all-interval Hall load, co-moving cutoff flux, and critical Gibbs cost?
- **F2:** Can one source-derived Sonin aperture section or positive barycenter match every
  residual-energy moment to the continued prime--Gamma moments, preserving the full Hankel moment
  cone rather than only one trace?
- **BSH:** Can literal nested Sonin/source contractions instantiate the reciprocal section and make
  both adjoint-versus-inverse mate defects cofinally small without assuming unit dilation modulus?
- **G:** What independent nonlinear/distinct-channel source law forces the already transported Ward
  coefficient to vanish or acquire the favorable four-unit wall order?
- **L:** What singular comparison sends the resolved Xi boundary to the existing Burnol/Deninger
  physical landing, commutes with strict differentials, preserves prime/depth/multiplicity and the
  nonzero Xi coefficient, and makes the physical reader kill that boundary without assuming its
  conormal defect vanishes?
- **O:** What coefficient-faithful intertwiner sends the source-self-polarized determinant, strictly
  negative off center, into the linear actual-head/restricted-Weil floor after spectral integration
  and physical-collar restoration?
- **P:** What separately source-derived rescaling/correction—or different singular boundary
  landing—carries the source-native wall jet into the second-Cartier endpoint/radial-work channel,
  given Lean proves its fixed canonical quadratic jet differs from completed theta/Xi curvature?
- **Q:** Why is the explicit exterior paired source diagonal nonnegative for every admissible pole
  before divisor selection, when the known Xi specialization and scalar matrix collapse pass
  through RH?
- **CLG/TTF:** What completed theta/prime--Gamma law excludes every cofinal regular two-pole escape
  `(even, odd, source) -> (0, N, -N)` before divisor selection? Higher even Turán curvature and the
  local four-point even wall are already positive; the surviving obstruction is reflection-odd.
- **SP-E:** Can the exact prime dilation gain-minus-debt flux be compared with its continuum
  increment without splitting the cross-scale cancellation or invoking false raw screw positivity?
- **SCE:** What source recurrence or convex-dual inequality proves every Suzuki checkpoint
  conjugate at most its Mangoldt moment, given Bregman drawdown does not orient the absolute floor?
- **T1:** What signed short Möbius-block estimate controls the depth-invariant
  top-row/translation transfer current without splitting its cancellation?
- **T2:** Do actual ordered-prime shells produce the inverse-log adjacent defect and physical-slice
  envelope on one strict base-phase margin; do the closed alternatives sum at critical weight; and
  does the Chebyshev recurrence continue in a signed topology allowing critical-line poles?
- **U:** What non-scalar source mechanism excludes the nonintegrable strict-frontier Christoffel
  quotient or proves cofinal shifted reciprocal Hankel-tail order?
- **HC:** Can actual selected rows instantiate the certified Proposition 4.6 packet, can `S2/S3`
  and the isolated inverse-character Dirichlet-prefix window be controlled uniformly, and can the resulting height
  aggregation cross absolute collision quantum two? Full `S1` and both small/large Lemma 6.2
  far-left `X^-200` tails are closed.
- **SV2:** What source identity identifies the compatible whole-upper-half-plane cofinal
  Livsic/projective limit with the global divisor-faithful characteristic, propagates it to the
  full finite chart, and controls the reciprocal pole chart?
- **MSC:** Can the moving squarefree channel cross its half-unit continuation deficit and pointed
  graph-domain wall to prove four-unit covariance, given prime/depth compactness does not survive a
  nonzero infinite Sonin lift?
- **EWQ-V:** What pre-divisor nonunitary magnitude-changing incidence, using an independent source
  vacuum, orients the completed full jet or mixed Hedenmalm crossing after scalar, unitary,
  auxiliary-sector, marginal-dephasing, and ordinary-Wick mechanisms fail?
- **PCS:** What completed reflection-sensitive secondary class detects all-prime boundary homology
  despite identically zero Fredholm index?
- **SEC:** What completed prime--Gamma theorem makes adjacent-prime FE--Schwarz seam coboundaries
  eventually compact on the canonical ray, without importing MSC's inapplicable prime-axis
  compactness?
- **BPC:** Can the prime--Gamma/Möbius expression continue through the full susceptibility collar
  without importing a zero-free region or equivalent radius bound?
- **TK and other candidates:** Can a source-defined growing finite thermal/KMS family converge
  pointwise to all prime--arch moments? Can BSH, UEB, PSRC, PBM, SC, PPM, IRK, OPUC, HJ, or BW acquire
  a literal pre-divisor global source operation carrying their existing invariant to the Xi endpoint?
  Can PLAC, EPC, MEG, ZGC, or SFP obtain both arithmetic occurrence and a coefficient-faithful
  completed landing without collapsing to a terminal selector?
- **Pre-route infrastructure:** Can critical Schur monodromy, difference Picard--Vessiot,
  prime-support secondary cohomology, or ABHN/Manin-horizon dynamics be specialized to the literal
  completed prime--Gamma/Möbius source? Generic finite-rank, Brauer, Bures--Wasserstein, and circuit
  geometry alone has no Xi occurrence and changes no route count.

Until one is answered, endpoint reformulations, finite real-zero models, additional seed
asymptotics, diagonal moment inequalities, or scalar transport identities do not move the formal
RH frontier.
