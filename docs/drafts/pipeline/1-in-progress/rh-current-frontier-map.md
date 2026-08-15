# Current Formal Frontier Toward Proving or Disproving the Riemann Hypothesis

## Scope and verdict

This document is a state map of the `HTGeometry`, `HilbertMetric`, and `RHTower` research corpus.
It records current proof architectures, theorem chains, first open source statements, terminal
mechanisms, and structural conclusions shared across routes. It is not a chronology or build log.

**Corpus cutoff:** 15 August 2026, committed snapshot
`a0c096c0f9ba79510b6b9c44911175a3fd6fd290`, together with explicitly audited active-tree
declarations present at that cutoff.

RH and its negation remain unproved. Current independent live count is:

- ten lettered routes: **C1, D2, E, G, L, O, P, Q, T, U**;
- one unlettered live architecture: **CCM-FU**;
- no instantiated Route V;
- Route R terminalized as an independent producer.

An **endpoint** is a Lean-proved implication or equivalence ending in RH. It is a receiver, not
evidence for its premise. An **open core** is first unproved source theorem after proved connectors
and RH-equivalent reformulations are removed. An **independent route** requires a literal source,
an unconditional chain to an RH endpoint, and an open producer not already identified with another
route under corpus source-isogenies.

## Executive route map

| Route | Architecture | First open core |
|---|---|---|
| CCM-FU | finite Sonin source → coefficient-faithful CCM packet → parity/simple-ground Fourier law → compact-Fourier zero transfer → Xi orientation | Construct canonical cofinal `Pi(lambda,k)`, prove its simple-ground and arithmetic mean-square approximation hypotheses, complete endpoint-renormalized weighted-cosine diagonal, and orient four-unit ground incidence. |
| C1 | theta source inverse → entire Fredholm determinant/Weil form → real spectrum or positive closure → RH | Prove a source-derived real-spectrum/positive-closure theorem for fixed theta inverse, or an Euler-product/intersection inequality controlling deviation-weighted divided differences. |
| D2 | safe-line Euler deficit → analytically continued prime–Gamma trace → finite high-frequency ceiling → RH | Continue literal positive deficit through Euler wall and prove any finite uniform ceiling above frequency four. |
| E | squarefree central Wold shell → fixed opposite-parity relation → Hall/load/flux/cost transport → Mertens cancellation → RH | Prove `ENTROPY-SPREAD-GRADE-RECURRENT-CUBE-CAPACITY` for fixed source-first relation with unit incoming co-degree, interval Hall expansion, moving cutoff flux, and strict-half cost. |
| G | Suzuki source → restricted-Weil ground or two-ray meromorphic exterior → Hermite–Biehler orientation → RH | Floor: classify/control every attained near-ground direction. Exterior: assemble completed all-prime/all-aperture forcing, retain cutoff/jump law, reduce residual support globally, and force physical trace orientation/return. |
| L | completed Xi Green/BV source → resolved target boundary → fixed Burnol/Deninger reader → `K_n(rho)=0` → RH | Identify transgressed Big-Witt first-ghost seam as an actual strict Green/BV boundary in fixed physical square and prove source-side submass before divisor specialization. |
| O | restricted-Weil operator → explicit prolate/band source → whole-ground control → nonnegative cofinal floor → RH | Prove quadratic threshold inheritance for a nonzero even band component, concrete PSWF/whole-channel estimates, then source-derived exhaustion and lower control of every near-ground sequence. |
| P | primitive Euler cubic Gram with total budget `<2` → completed boundary restriction → Xi conormal trace → exclude one off-line charge → RH | Transport canonical Euler-node Burnol Gram to actual Xi divisor nodes at exact `s=0` wall; equivalently short polar–Gamma surplus before conormal landing. |
| Q | theta–Cassini source → source quantization or direct jet saturation → inward saturation → transverse charge zero → RH | Prove direct Cassini–Jensen/jet saturation, or construct a source-derived label-sensitive discontinuous plateau quotient. Selected continuous power carrier is retired. |
| T | exact AFE/moment source → translated Gabriel endpoint estimates → zero count → `7/10` prime supply → physical current composition → RH | Prove uniform translated left-`4/3` and right-`2` endpoint moments, then quantitative detector zero counting, density-to-short-interval prime supply, and composition. |
| U | shifted-Xi Hankel first crossing → fixed-carrier even/odd/cross source anomaly → source-specific exclusion → positivity → RH | Exclude every cofinal diagonal/cross anomaly. Pole cross term is too small; cross branch therefore needs von-Mangoldt completion of exact Gamma commutator, while diagonal branches need source-specific lower control. |

## Live architectures

### CCM-FU — four-unit source-codiagonal incidence

**Endpoint.** A moving Gamma/Sonin/Hodge incidence carrying continued Xi Ward column with
nonincreasing four-unit energy gives required Ward orientation and RH.

**Architecture.** Literal finite Sonin source `sigma_S` lands in actual module-one invariant class
space. Its finite periodization is a Boolean Euler cube with coefficient `mu(n)/n`; Fourier
transport preserves coefficients. Published finite restricted-Weil packet has exact even/odd PSD
blocks and rank-one cross commutator. A parity-free simple-ground theorem forces real zeros of the
finite Fourier numerator. Fixed-support mean-square convergence then transfers real-zero laws to
any nonzero compact-Fourier limit.

**Established structure.** Corpus proves:

- source-faithful whole-`L2` finite-stage Sonin comparison and density of literal cores;
- published finite CCM packet, parity blocks, simple-ground visibility, and parity-free real-zero
  theorem;
- complex mixed CCM form and exact CCM–Suzuki screw/Weil identification;
- compact-Fourier zero transfer under fixed-support mean-square convergence;
- finite Guinand–Weil source quotient for every continuous source functional, including measures;
- pre-quotient pole density and finite von-Mangoldt atoms giving exact polar–prime sine source;
- endpoint-cancelled singular Gamma density giving exact archimedean sine source;
- universal Gamma first-jet law and mode-independent weighted-cosine endpoint counterterm;
- complete mixed-order odd and diagonal dictionaries at every integer mode;
- whole completed centered source packet equal to published restricted-Weil matrix entrywise;
- four-unit prime-entry event law: odd tangent equals mode times mode-independent diagonal tangent;
- prime-entry whole-matrix tangent is a negative-semidefinite rank-one constant-boundary contraction;
- every finite visible prime-event aggregate remains the same negative rank-one boundary contraction;
- local field-one/Suzuki four-half-step factorization and four-unit detector;
- cubic-Green identification of each critical prime atom with Route P primitive base mass.

Finite matrix quotient has only `2N+1` source coordinates; even strictly positive source weights
are not recoverable beyond observer dimension. Canonical selection must therefore occur before
finite quotienting.

**Open core.** Construct canonical `Pi(lambda,k)` before quotient loss; prove block/simple-ground
hypotheses cofinally; construct canonical arithmetic approximants with fixed-support mean-square
convergence to a nonzero Xi landing; assemble the mixed-order finite-aperture source as a global
BV/Stieltjes connection whose atomic residues are the formal prime-entry four-unit law; identify its
centered continuation with the existing Xi Ward column; combine atomic negative orientation with
continuous pole/Gamma transport and orient four-unit ground incidence. Finite
odd/diagonal source normalization and whole published-matrix reconstruction are not open.

**Route relations.** CCM–E is only an opening until a cofinal Hall/load/flux-to-floor theorem is
proved. CCM–P is Route P's existing completed boundary wall in CCM coordinates, not another route.

**Principal Lean evidence.** `CCMGuinandWeilContinuousSourceQuotient.lean`,
`CCMGuinandWeilLiteralPolarPrimeSource.lean`, `CCMGuinandWeilArchimedeanOddSource.lean`,
`CCMGuinandWeilArchimedeanFirstJet.lean`,
`CCMGuinandWeilCompletedCenteredSourceMatrix.lean`,
`CCMGuinandWeilPrimeEntryIncidence.lean`,
`CCMGuinandWeilPrimeEntryRankOneTangent.lean`,
`CCMGuinandWeilPrimeEntryAtomicConnection.lean`,
`FieldOneFiniteStageThetaSourceNormalization.lean`, and CCM–Suzuki comparison modules.

### Route C1 — complete Xi–Weil / Hedenmalm positivity

**Endpoint.** Positivity of complete Xi–Weil form on faithful singular domain implies RH.

**Architecture.** Fixed theta-cusp source defines compact nonnormal inverse `B`, entire determinant,
weighted derivative, shifted cokernel, and singular Weil form. Corpus proves

```text
thetaSourceEntireDet2(z) = XiC(z)/XiC(0),
thetaSourceEntireDet2(z)=0  iff  XiC(z)=0.
```

Analytic order equals reciprocal-eigenvalue algebraic multiplicity. Thus source construction,
divisor realization, and multiplicity accounting are closed. Required producer is not another
spectral model: it is a source law making nonzero spectrum of this specific `B` real, or making
complete Xi–Weil form positive.

**Established structure.** Closed operator, shifted-cokernel, supersymmetric Dirac, essential
inverse-flow trace, and prime–Gamma coefficient interfaces are formal. Gauss–Hodge/Weil fusion
identifies off-line obstruction as deviation-weighted divided-difference mass and as negative odd
sector of an unconditional Krein decomposition. Known arithmetic input gives a strict wall-repulsion
ceiling below `1/4`, but RH is vanishing of entire deviation mass. Probe-circle laws show holomorphic
ray samples cannot determine required Hermitian circle relation.

**Open core.** Either:

1. prove source-derived real spectrum/positive closure for fixed theta inverse; or
2. prove a pre-zero Euler-product/intersection/compressed-trace identity dominating deviation-
   weighted divided-difference moment by even energy on entire square-summable tests.

Complete monotonicity of source-resolvent field is already unconditional outside exact wedge
`n>=19`, `0<X<(n+1)^2`; missing theorem is source-derived positivity inside that wedge. More finite
ray jets, probe samples, post-divisor moments, or indefinite GNS repackaging do not advance C1.

**Principal Lean evidence.** `HedenmalmThetaSourceDeterminantMultiplicity.lean`, shifted-cokernel and supersymmetric
theta modules, `GaussHodgeWeilPolarizationFusion.lean`,
`GaussHodgeWeilDeviationMoment.lean`, `GaussHodgeWeilArithmeticDeviationGap.lean`, and
`XiProbeCircleCriterion.lean`.

### Route D2 — continued prime–archimedean ceiling

**Endpoint.** A finite upper bound for continued positive-frequency relative trace above frequency
four is equivalent to RH. If RH fails, continued source is cofinally unbounded.

**Architecture.** On safe line `sigma=1+1/log x`, corpus proves uniformly in `tau`

```text
log log x - log|zeta(sigma+i tau)|
  = sum_(p<=x) (1-cos(tau log p))/p + O(1).
```

Euler logarithm, prime-square correction, head shift, cutoff tail, and Mertens normalization are
closed. One quarter of doubled-frequency deficit lower-bounds pretentious distance from every real
prime sequence `|r(p)|<=1` to `p^(i alpha)`.

**Open core.** Continue this positive source through critical strip with literal prime–Gamma
completion and prove any finite uniform high-frequency ceiling. Larger safe-side bands, more
Euler-convergent sieve tails, and real-twist geometry do not cross continuation wall.

**Principal Lean evidence.** `ZetaEulerLogPrimeSum.lean`, `ZetaOneLineDeficit.lean`,
`RealTwistDeficitTransfer.lean`, and continued prime–archimedean trace modules.

### Route E — squarefree Möbius parity transport

**Endpoint.** Source-predeclared physical transport with square-root Gibbs cost, unit incoming
capacity, interval Hall control, and normalized friable/one-large-prime flux yields critical
Mertens cancellation and RH.

**Architecture.** Prime-power depth is reduced to negligible tail; hard cancellation lives on
squarefree depth-zero central Wold breadth. Transport must pair distinct opposite-parity integers
without defining adjacency from observed imbalance. Same fixed relation must control row load,
incoming co-degree, every interval, moving cutoff flux, and total mixed-difference cost.

**Established structure.** Two-large-prime and positive-depth tails, every fixed off-normal breadth
tail, coprime opposite-sign supply, prime-anchor capacity, and finite Wold-moment blindness are
closed. Patch seams are exact coboundaries. Finite differential-algebraic Euler germs cannot see
free infinite prime-clock orbit. Source-faithful Euler gauge cancels exactly when physical multiplier
is retained. Whole-anchor full allocation is capacity-impossible. Unconditioned scalar saddle
coercivity fails at explicit antiscale resonance; Gamma completion does not attenuate it. Scalar
characteristic amplitude decays only logarithmically, fixed terminal prime bands carry vanishing
harmonic mass, and terminal odd determinant grades reinforce rather than cancel.

**Open core.** For fixed source-first grade-recurrent relation `R_X^gr`, prove
`ENTROPY-SPREAD-GRADE-RECURRENT-CUBE-CAPACITY`:

- normalized row load and physical incoming co-degree at most one;
- interval Hall expansion by distinct opposite-parity integers;
- crossing of moving zero/one-large-prime cutoff with correct signed flux;
- total mixed-difference Gibbs cost `X^(1/2+o(1))` at `H=X^(1/2+o(1))`.

Multi-node and slot-sequence separation preserve squarefree jet multiplicity, but do not create
capacity. Additional scalar moments, Gaussian approximations, patch estimates, or complete-
bipartite flows are dead work.

**Principal Lean evidence.** Route-E depth/breadth reduction modules,
`RouteESourceFaithfulEulerTiltUnitShell.lean`, saddle/escape no-go modules,
`MultiNodeInjectiveParameter.lean`, and `SlotSequenceSeparation.lean`.

### Route G — Suzuki two-angle meromorphic source

**Endpoint.** A source-admitted Suzuki Hermite–Biehler/de Branges carrier implies RH.

Route G contains two producer branches sharing completed Suzuki source but not same final theorem.

#### G-floor branch

Literal restricted-Weil form has a Friedrichs operator, compact resolvent, attained ground vector,
dense smooth source range with same Rayleigh infimum, formally self-adjoint `D†G_aD`, exact complex
mixed source form, real corrections on real core, and strict Beurling–Deny modulus irreducibility.

**Open core.** Classify or lower-control entire attained ground family from source. Irreducibility,
ground attainment, and smooth visibility do not imply nonnegative ground energy or identify
arithmetic ground direction.

#### G-exterior branch

Weak Gamma equation is classified on each full frequency ray; point-supported solutions vanish.
Homogeneous channels glue through upper strip exactly when `c_-=-i c_+`, equivalently zero half-log
endpoint trace. One Fourier profile represents every interior height. Two-sided Gamma carrier,
forced-ray Hardy, one-prime nonnormal similarity, and terminal pruning are closed. Normalized Gamma
jump is bounded nonnegative accretive Hilbert-valued multiplier with exact first-order control.
Endpoint-centered one-prime polar trace is an unconditional whole-line `L2` weak-derivative pair;
continuous codomain maps and finite sums preserve such pairs.

**Open core.** Assemble completed all-prime/all-aperture physical source as one weak-derivative
forcing; retain full cutoff/jump commutator; subtract classified channels globally; prove residual
is point-supported and satisfies full equation; force zero-half-log trace and nonzero oriented
physical return coherently across apertures.

More one-prime regularity, generic weak-derivative theory, homogeneous strip estimates, or Gamma
symbol bounds do not advance exterior branch.

**Principal Lean evidence.** Suzuki restricted-Weil/Friedrichs modules,
`SuzukiLimitingLogIrreducibilityCore.lean`, Gamma weak-equation classification modules,
`GammaJumpFourierMultiplier.lean`, `SuzukiOnePrimePolarSource.lean`, and
`L2WeakDerivativeContinuousLinearMap.lean`.

### Route L — Deninger/Green/Hodge source descent

**Endpoint.** Strict source-derived chain identity places canonical resolved Green boundary in
Meyer–Poisson range, hence fixed Möbius–Fourier detector kernel. Coefficient-faithful physical
reader evaluates same boundary as `c_rho K_6(rho)` with `c_rho!=0`; vanishing forces
`Re(rho)=1/2` for every Xi divisor.

**Architecture.** Required commutative square is fixed:

```text
completed Green ⊗ BV_1  --id⊗b-->  completed Green ⊗ BV_0
          | F_1                              | F_0
          v                                  v
    resolved target_1  -----d_T----->  resolved target_0
                                                |
                                                v
                                      fixed physical reader.
```

`F_0` must be existing Burnol/Deninger physical landing, not defined quotient. Reader must kill
target boundaries; prime/depth/divisor/multiplicity provenance and nonzero leading Xi jet must
survive; construction precedes divisor specialization and may not assume `K_n(rho)=0`.

**Established structure.** Completed Xi Green primitive, coefficient-faithful Green-to-Calderón–
Witt comparison, Tate boundary/top-coordinate reader, actual Burnol conormal identity,
ordinary-integer BV/Hochschild boundary, all-cross-prime Koszul cycle, rational-adelic relative
complex, and strict resolved-Xi chain provenance are closed. Big-Witt prime-seam source has first
ghost zero and second ghost `-2` times physical Dirichlet energy.

Division-free Frobenius two defined from `f(T)f(-T)` transports input second ghost exactly into
first ghost over every commutative ring, naturally under base change, while squaring Teichmüller
representatives. Polarized aggregate is reflection-invariant; transgressed first ghost is `-2`
times physical seam energy and normalized residue tends to `-4` times one-particle seam norm.
Ghost-degree mismatch is therefore closed without torsion-free, injectivity, division, or RH
premises.

**Open core.** Identify this explicit transgressed first-ghost object as actual strict Green/BV
target boundary and prove source-side submass in fixed square. This is singular source-to-physical
specialization, not missing complex packaging. Generic mapping cones, Koszul exactness, cyclic
traces, KMS untwisting, compact-orbit tomography, or declaring physical vector a boundary erase or
relocate `K_n`; they do not prove comparison.

**Principal Lean evidence.** `DeningerMeyerReflectedGaussianCompletedSourceGreen.lean`,
`DeningerCalderonWittCompletedXiGreenIncidenceComparison.lean`,
`DeningerBurnolConormalRadialTopBoundaryComparison.lean`,
`DeningerOrdinaryIntegerBVGreenStokesRadialComparison.lean`,
`CCMRationalAdelicPrimeIsotropyRelativeXiChainMap.lean`, and
`DeningerBigWittFrobeniusPrimeSeamTransgression.lean`.

### Route O — Connes restricted-Weil/prolate ground space

**Endpoint.** Let `epsilon_lambda` be true restricted-Weil ground floor. Floors are antitone; one
negative trial pins all later floors below fixed negative value. Therefore nonnegative cofinal
floor, or convergence `epsilon_(lambda_j)->0` on one cofinal nested family, implies RH.

**Architecture.** Explicit constrained prolate/Hermite source supplies Rayleigh value `r_lambda`.
Seed analysis, radial prime response, polar term, and band decomposition must be promoted from one
trial direction to lower control of every near-ground direction. Rayleigh–Ritz gives only
`epsilon_lambda<=r_lambda`; RH requires opposite control.

**Established structure.** Finite restricted-Weil matrix, reflection, real-rooted completion,
nested-floor monotonicity/no-evacuation, true Friedrichs ground attainment and continuity,
small-aperture asymptotic, limiting-core modulus irreducibility, prolate ladder, Gaussian strict
half-threshold trial, radial Abel transport, whole unit-band Hilbert decomposition, reflection
compatibility, and parity of every nonzero band component of an even profile are closed. Generic
compact-Fourier window uniqueness is also formal.

**Open core.** Three nested layers remain:

1. prove Gaussian quadratic strict-half inequality is inherited by at least one nonzero even band
   component;
2. prove concrete PSWF-to-leading-density, inverse-bandwidth, and summed-channel primitive estimates
   with intact polar–prime cross terms;
3. classify every near-ground sequence as prolate ladder + translated two-edge boundary + prime-
   phase escape + coercive bulk + `o(1)`, and prove relative coercivity/exhaustion.

Additional seed asymptotics, finite real-zero determinants, or renamed ground comparisons do not
control true floor.

**Principal Lean evidence.** restricted-Weil/Friedrichs modules,
`ProlateGaussianTrialPositive.lean`, `ProlateEvenEigenspaceQuadratic.lean`,
`ProlateBandHilbertSum.lean`, `ProlateReflection.lean`, `ProlateBandComponentEven.lean`, and radial
source/Abel modules.

### Route P — primitive cubic Euler/Burnol trace

**Endpoint.** Every strict-right Xi zero contributes at least one indivisible cubic conormal charge,
while entire primitive Euler source has total trace budget below that charge. Completed trace
contraction therefore excludes all strict-right zeros and proves RH.

**Architecture.** Primitive Euler cells `(p,e)` carry resolved von-Mangoldt amplitude and cubic
Cauchy Gram. P-G181 base cube is PSD with total budget `<2`; P-G182 identifies target feature as
normalized completed-Xi conormal residue; P-G183 resolves multiplicity; P-G184 identifies budget
with balanced Euler codiagonal; P-G185 proves exact joint damping wall `s>=0`; P-G186 constructs
inverse-Burnol-window features whose entire finite-aperture Gram is exactly base cube before zeros;
P-G187 identifies `s=2c` as energy time of a contractive weighted-aperture semigroup and proves
that every negative time creates a nonintegrable boundary pole on an explicit finite-energy datum.

**Established structure.** Arbitrary ordinate clusters are PSD with spacing-free trace. Source
summability, depth-square contraction, source-window formation, Burnol target support, and
multiplicity accounting are closed. P-G185's arithmetic wall and P-G186's source Gram are now one
unilateral semigroup wall at `L=0`. Cubic Green test in CCM maps every critical prime atom to same
base mass and writes pole–prime completion as polar surplus minus truncated `<2` budget.

**Open core.** Prove completed boundary-value/closed-graph restriction from canonical Euler nodes
to actual Xi divisor nodes at exact balanced wall `s=0`; equivalently short polar–Gamma surplus
before conormal landing. Ordinary absolute contour crossing is impossible for `s<0`, and P-G187
rules out backward evolution inside the positive-aperture `L2` space itself. Viable producer must
add a completed dilation/defect channel before positive Gram comparison. Alternative curvature
lane would need finite uniform high-tail ceiling.

More cluster estimates, seed/source-window construction, target support identification, scalar
capacity, or multiplicity normalization are closed work.

**Principal Lean evidence.** P-G174–P-G187 modules, especially
`RoutePPrimitiveBurnolWindowGramSquare.lean`,
`RoutePPrimitiveBurnolApertureDampingSemigroup.lean`,
`XiWardCubicBurnolWindowConormalIncidence.lean`, and
`FrankensteinCCMRoutePBaseCubicGreenSourceBridge.lean`.

### Route Q — theta–Cassini boundary saturation

**Endpoint.** Cassini inward saturation, source dominance, transverse-charge vanishing, and RH are
equivalent.

**Architecture.** Theta source supplies aperture-independent positive likelihood, finite positive
Hankel blocks, analytic boundary-to-seam continuation, and selected exponent. Absolute centered
moments obey height-damping recurrence, giving geometric `1/81` ratio from certified height floor.

**Closed negative result.** Selected continuous power-reciprocal carrier cannot satisfy all-degree
closure. Its pushforward has positive mass outside countable Xi thermal nodes, while any positive
all-degree witness is rigidly canonical atomic Xi measure. Continuous injective or strictly
monotone scalar transforms are therefore impossible.

**Positive survivor.** Complete moment matching requires source-side quantization: successful
reporter needs positive-measure plateau fibres over Xi thermal atoms.

**Open core.** Direct Cassini–Jensen/jet saturation, or source-derived label-sensitive
discontinuous plateau quotient. Paper-level verified low-zero height floor `T>9` and signed first-
moment comparison remain formal certification backlog, but they do not revive retired continuous
carrier.

**Principal Lean evidence.** Cassini/theta saturation modules,
`ThetaCuspCalibratedPowerReciprocalAllDegreeNoGo.lean`, and structural absolute-moment height-gate
modules.

### Route T — mass-shifted critical outgoing current

**Endpoint.** Uniform translated Gabriel endpoint moments give center detector inequality; combined
with quantitative zero count and `7/10` short-interval prime supply, physical lower/upper phases
compose into RH.

**Established structure.** Literal primal, reflected dual, and confluent-pole AFE pieces each obey
`N^(101/100)` dyadic budget; exact AFE identity gives unconditional critical fourth moment.
Mollifier second moment, detector-error `4/3` moment, and absorbed height exponent `<7/10` are
closed. Concrete pole-cleared Gaussian field is globally bounded and `DiffContOnCl` on exact
Hadamard strip. Free-prefix Littlewood estimates and Abel transport give explicit uniform bound
for `zeta(1+delta+it)` on `0<=delta<=1`. Fixed-right-edge coefficient gap gives power-saving
mean-square decay.

**Open core.** Prove uniform translated left endpoint `4/3` moment and right endpoint second
moment for concrete field; substitute into closed scalar interpolation; prove quantitative
coefficient-three detector zero count; derive prime in `(x,x+x^(7/10)]` for every sufficiently
large `x`; compose with source-faithful current. Wold chart separately needs signed pole-preserving
continuation.

Repeated short-block freezing is dead at `T^(5/3)`. More AFE decomposition, contour bookkeeping,
fourth-moment repackaging, prefix bounds, or shifted-line pointwise bounds do not close translated
moments.

**Principal Lean evidence.** smooth AFE modules, Ingham/Gabriel detector modules,
`InghamGabrielScalarAnalytic.lean`, `DirichletPrefixLittlewood.lean`, and
`ZetaShiftedLineRate.lean`.

### Route U — shifted-Xi null-face Krein–Lorentz flow

**Endpoint.** Far-right shifted Hankel forms are positive. If positivity first fails, first
crossing is singular. Excluding every right-half first crossing by completed-source orientation
proves shifted-Hankel positivity and RH.

**Architecture.** False RH is equivalent to one fixed polynomial–Gaussian carrier producing
negative Hankel packets at every sufficiently large hard-edge mass. Finite periodization is exact
Chebyshev evaluation at complex Cayley nodes. Antipodal split `P=E+O` yields exhaustive anomaly:
negative even diagonal, negative odd diagonal, or negative even–odd cross capital. Each branch has
literal completed Gamma–polar–von-Mangoldt source disintegration.

**Established structure.** Null flags, odd contact, Lorentz crossing, adaptive all-jet Cassini
transport, degree growth, source disintegration, hard-edge inversion, and fixed-carrier cofinal
witness are closed. Nyquist signed current `E^2-O^2` has unconditional complete-divisor exchange
and normalized mixed-source flux tending to zero, so Nyquist lane is spectrally silent. Source-
matched Kelvin heat integration leaves exact Gamma commutator; two-chart theorem rules out every
global scalar counterterm.

Polar cross term is classified exactly at spectral point `i/2`. For mass `a_k=k+1` and transported
Cayley node `z_k`:

```text
P_k(z_k)  -> Re(F_n(i/2)),
P_k(-z_k) -> 0,
N_k = (P_k(z_k)^2-P_k(-z_k)^2)/(2(a_k^2-1/4)),
a_k^2 N_k -> Re(F_n(i/2))^2/2,
N_k -> 0.
```

Every shifted-reversal degree power cancels under actual common filter. Pole is direct-polyphase
selector with hard-edge valuation two, not logarithmic chart-charge reservoir.

**Open core.** Exclude all three fixed-carrier anomaly branches. Diagonal branches require source-
specific lower bound or contradiction with degree-free Cauchy density. Cross branch requires
von-Mangoldt cross source to supply and orient chart-local charge against exact Gamma commutator;
pole cannot do it. Universal positivity is RH-equivalent and not a producer.

**Principal Lean evidence.** shifted-Hankel/null-flag modules,
`XiShiftedHardEdgeCofinalLinearFiniteHankelDimension.lean`,
`XiShiftedHardEdgePrimeGammaAntipodalPolarization.lean`, Kelvin current/detailed-balance/two-chart
modules, and `XiShiftedHardEdgePrimeGammaPolarPolyphaseValuation.lean`.

## Terminal and retired routes

Closure applies to stated mechanism, not every future construction using similar vocabulary.

| Route | Closed mechanism | Positive survivor or lawful successor |
|---|---|---|
| A | Fixed source-faithful physical-phase transports are identity; nonidentity transport has explicit connection defect. Positive aperture-dependent Markov transport exists iff source scalar is nonnegative; universal feasibility is RH. | Phase-natural rigidity and barycentric orientation completeness test any successor. |
| B | Fixed-width rectangular Weil quadrature/scalar transport contains no source orientation. | Variable-width or relation-valued primitive would be new route. |
| C2 | Finite theta detector saturates its available width; missing width is already RH-bearing. | Interfaces survive inside Q. |
| D | Finite prime–archimedean Hankel reconstruction/local positivity cannot orient completed all-degree source. | All-degree compact moment survivor is P; continued tail survivor is D2. |
| F | Finite-height Sonin/Burnol completion and compact multiplicative correction have wrong asymptotic order or collapse source. | An order-one pre-Gamma packet-diagonal primitive would be new route. |
| G2 | Required relative-Volterra germ is RH-equivalent. | Route G retains exterior source problem without Volterra repackaging. |
| H | Moving completed-source Taylor parity loses orientation after even factorization. | Relation-valued indefinite primitive would be new route. |
| I | Claimed sharp dyadic width is same saturated C2 coordinate. | No independent premise. |
| J | For `L_m=6 log m`, `m>=25`, Lean proves `E_bad(x,L_m)>=log(m)/20` for every Julia scale. Uniform unrenormalized energy budget is impossible; off-diagonal cancellation cannot remove unit diagonal; post hoc subtraction breaks one-node capacity. | Principal-relative current must be defined before good/bad projection. Existing concrete realization is R. |
| K | Quadratic spectral mechanism fails. | Strong all-order marked-prime/quartic content belongs to P. |
| M | Source-faithful Gamma–Jacobi reader is complete; remaining anchored cofinal flatness is RH. | No lower producer inside M. |
| N | Prime-normal/common-forcing and conormal carriers are exact, but response equality, endpoint contractivity, or bounded polar work is RH-equivalent. | These are coefficient-faithful receivers shared with L/P/R, not producer. |
| R | Intrinsic pre-polar producer category is empty. Every audited external positive-polar, Calkin, compactness, first-Xi-jet, and loss-zero Fisher interface—and their disjunction—is RH-equivalent. Hyperbolic-gauge quadratic positivity is identically zero; quartic Stokes amplitude annihilation is RH-equivalent. | Only nonfunctorial external polar/compression admission can survive. Quantitative Burnol collar decay strengthens receiver but does not reopen R. |

Route S remains upstream source-algebraicity/dynamical infrastructure, not independent RH route:
it lacks both Xi-typed source handoff and non-circular critical-line producer.

## What routes have in common

### 1. Information is usually lost before endpoint, not absent at source

Corpus routinely constructs prime labels, depth, reflection, multiplicity, and horizontal grade.
Failures occur when later operation forgets decisive coordinate:

- scalarization erases parity, phase, or incidence (E, U);
- finite CCM quotient erases overcomplete source provenance (CCM-FU);
- positive square/Gram formation erases reflection-odd current (C1, P, R);
- compact topology erases noncompact escape required by singular physical landing (L);
- one trial Rayleigh quotient supplies upper, not lower, ground control (G, O).

Any successor must preserve route's missing coordinate until producer theorem acts.

### 2. R, L, CCM, and Gauss–Hodge see one horizontal obstruction

Source-zero horizontal carrier, Gamma Bockstein, Deninger Green obstruction, Burnol seam energy,
and Gauss–Hodge mass are coefficient-faithful realizations of same reflection-odd horizontal class.
Corpus constructs and orients class; global vanishing is RH-equivalent. Different target geometries
do not constitute independent evidence. A viable merged mechanism needs source-generated nonzero
mixing before divisor specialization, preserving prime/depth/divisor/multiplicity and both
reflections. Rank-one, holomorphic, compact, or fitted contractible repairs only re-present or erase
obstruction.

### 3. Ground selection is common spectral wall

CCM-FU, C1, G-floor, and O all possess explicit sources, operators, finite positivity, and spectral
receivers. None yet proves actual complete ground/entire spectrum is controlled by explicit source
sector. Required mathematics is profile exhaustion, reduced-resolvent control, relative coercivity,
or source-derived real-spectrum law—not more seed vectors or determinants.

### 4. Singular boundary restriction is common geometric wall

L and P have source carriers and target readers on both sides. Missing theorem is exact singular
map at boundary of ordinary convergence:

- L: transgressed Big-Witt/Green source into strict BV boundary and fixed reader;
- P: Euler-node Burnol Gram into Xi-divisor conormal at `s=0`.

CCM–P bridge confirms shared source mass but does not solve either boundary map.

### 5. Arithmetic routes need non-scalar all-prime control

D2, E, T, and U have exact finite/safe-side/one-prime source identities. Remaining statements are
uniform continuation, interval incidence, translated moments, short-interval supply, or signed
von-Mangoldt cross control. Modulus-only bounds, coefficient-free positivity, fixed finite prime
bands, and post hoc scalar renormalization are formally insufficient.

### 6. Quantization is a real constraint

Q proves continuous monotone source carrier cannot land on atomic Xi all-degree measure. P and U
also expose indivisible conormal/contact charges. Successful source selection may require
label-sensitive discontinuous plateau fibres, boundary indices, or singular graphs—not smoother
scalar reporters.

### 7. No serial super-route exists

C1, D2, E, G, L, O, P, Q, T, U, and CCM-FU share connectors but have different admission and
producer theorems. Combining endpoints does not multiply evidence. Merger becomes mathematical
only when one literal source map transports open premise of one route into producer of another
without assuming RH-equivalent orientation.

## Candidate architectures not yet routes

### CCM–E floor transport

Literal finite Sonin source carries `mu(n)/n`, but no theorem sends E's fixed Hall/load/flux law
into CCM cofinal floor selector. It becomes new route only after such coefficient-faithful
comparison and unconditional floor handoff exist.

### Relative formation-completion current (Route-V candidate)

Constitutive and relative-formation modules show source laws may require nonzero mixing before
radical-preserving normalization. No literal Xi-typed formation object currently has both
non-coboundary displacement and coefficient-faithful RH handoff. Therefore Route V is not
instantiated.

### Helson Fredholm wall

Potential architecture would encode canonical Xi stream in fixed Fredholm threshold with global
wall law. Corpus lacks canonical stream, fixed threshold, and source theorem; present material is
receiver language only.

### Post-J principal-relative current

J proves current must be defined before good/bad projection. Existing concrete primitive is Route
R and is terminalized. A genuinely different source object with non-coboundary incidence and
unconditional handoff would be new route.

### Cubic Ward/Hellinger source-trace opening

This is not Route P. P-G labels identify committed dependency and receiver blocks used by a
cross-route Ward/CCM/R opening.  The source-to-zero comparison itself has not been constructed, so
the opening is not another numbered route either.  Its missing mechanism remains a completed,
coefficient-faithful pre-divisor incidence/contraction from pole--Gamma--von-Mangoldt source data
to cubic zero-side energy with signed ordinate control retained.

P-G186 and the Burnol-window incidence theorem remove one misleading obstruction. Primitive
source columns and completed-Xi conormal columns both live in the same unweighted
`L2(R_+,dL)`; inverse logarithmic cubes come from
`integral L^2 exp(-2lambda L)dL=1/(4lambda^3)`, not from a `dL/L^3` source measure. The remaining
Riesz gap is absence of a coefficient-faithful completed intertwiner, not Radon--Nikodym loss.

P-G187 identifies a second, sharper universal obstruction. Weighted aperture translation
`T_c f(L)=L/(L+c)f(L+c)` is a contraction semigroup for `c>=0`, diagonalizes every Burnol column,
and turns primitive energy into P-G185 damping by `s=2c`. For every `c<0`, an explicit
finite-energy boundary datum acquires a nonintegrable pole at `L=-c`. Hence completion cannot be
ordinary backward motion in this Hilbert space: polar--Gamma coupling must supply an additional
boundary/dilation defect channel before Gram comparison.

W-H185 gives a sharp new no-go and design law. Every primitive Euler column has exponential decay
rate at least `log 2`, whereas every strict-right centered zero column has rate
`0<a<1/2<log 2`. The exact tail is

~~~
T(lambda,R)=exp(-2lambda R)
 [R^2/(2lambda)+R/(2lambda^2)+1/(4lambda^3)].
~~~

Hilbert--Schmidt tail control for P-G186's full primitive synthesis proves that no strict-right
Xi conormal column belongs to its bare synthesis range, for any primitive ordinate clocks:
otherwise `exp(2(log 2-a)R)` would remain bounded. Thus direct Douglas factorization of the
positive primitive Gram is impossible even for one off-line copy.

Completion must therefore act before Gram comparison and create slower modes through signed
polar--Gamma/functional-equation coupling while preserving the global subquantum trace. This does
not exclude arbitrary bounded nonlocal operators; it isolates the exact source-derived completion
property still missing from W-H184. Lean proves exact tail integral and strict-right/log-2 rate
separation in `XiWardCubicPrimitiveTailRateNoGo.lean`.

## Fundamental nature of remaining problems

The live open cores fall into six mathematical classes.

1. **Source selection and spectral exhaustion.** Determine complete ground/spectrum from explicit
   source sector (CCM-FU, C1, G, O).
2. **Singular boundary admission.** Construct closed-graph/relative-chain maps exactly at
   convergence or trace-ideal wall (L, P).
3. **Oscillatory arithmetic incidence.** Prove signed all-prime cancellation or transport without
   scalarizing phase/parity (D2, E, T, U).
4. **Source quantization.** Produce label-sensitive discontinuous or singular selector compatible
   with atomic Xi support (Q, parts of P/U).
5. **Relative coercivity.** Bound entire unwanted complement, not one seed, diagonal, or finite
   packet (C1, G, O).
6. **Non-circular annihilation.** Convert already-oriented horizontal charge into zero by an
   independent source law; current vanishing statements themselves are RH-equivalent (L/R/CCM/
   Gauss–Hodge interfaces).

These are not mainly missing formal packaging. In most routes source object, receiver, and RH
endpoint already exist. Missing theorem is constitutive: why physical source occupies favorable
ground, crosses singular boundary, cancels all-prime oscillation, or quantizes onto correct atomic
support.

## Research programme

Highest-value research topics are those capable of supplying one of these constitutive theorems:

- source-derived ground-state profile decomposition and reduced-resolvent estimates for
  nonlocal restricted-Weil operators;
- singular boundary values of vector-valued Hardy/de Branges/Burnol transforms at exact abscissa
  of convergence, including trace-ideal and closed-graph transport;
- arithmetic Hall expansion for fixed factorization-generated graphs with simultaneous local load
  and moving-cutoff signed flux;
- uniform translated zeta/mollifier endpoint moments and quantitative detector zero counting;
- pretentious-distance continuation from Euler-convergent line into completed prime–Gamma strip;
- source-specific von-Mangoldt Kelvin/polyphase cross currents rather than scalar explicit-formula
  bounds;
- discontinuous source quantization, plateau fibres, and atomic moment realization without fitting
  Xi divisor after fact;
- source-relative intersection/compressed-trace identities controlling Hermitian deviation sector;
- noncommutative or singular mixing mechanisms that preserve reflection-odd horizontal class until
  annihilation, rather than radical-preserving normalization.

The separate literature-exchange paper records external state of art and proposed imports:
[`rh-route-literature-exchange-august-2026.md`](./rh-route-literature-exchange-august-2026.md).

## Shared analytic infrastructure that does not change route count

Reusable Lean results close several former technical adapters:

- bounded Hilbert-valued `Lp` and Plancherel multipliers, including accretivity for nonnegative
  symbols;
- `L2` weak derivatives preserved by continuous codomain maps and finite sums;
- compact Fourier transforms of interval-integrable amplitudes are entire, with window-uniqueness;
- torus translate-difference dominated convergence and sharp Poincaré passage;
- complete differential matroid of actual multiple-sine difference-differential operator outputs,
  stable under translations and differential-algebraic perturbations;
- binomial threshold derivative bounded by replica order and order-`r` Lipschitz regularity.

These remove interface excuses. None supplies missing Xi-typed source selection, boundary
restriction, arithmetic incidence, or annihilation theorem.

## Final state

Current corpus contains several genuinely nonclassical RH architectures, especially Route R's
terminalized primitive-current calculus, Route U's adaptive null-face flow, Route P's primitive
cubic source budget, Route L's strict Green/BV descent, and CCM-FU's source-faithful finite Sonin
incidence. Novelty of architecture does not imply completion: every live route stops at a precise
source theorem not presently supplied by corpus or external literature.

No additional independent route follows from current seams. No live route is closed to RH. No
formal disproof route exists. Frontier advances only when one named open core above is proved or
falsified with a positive survivor; additional RH equivalences, finite positivity, source-free
compactness, seed asymptotics, or renamed receiver criteria do not change state.

### Route T left Gabriel endpoint closed

`Sieve/InghamCriticalGlobalErrorMoment.lean`,
`Sieve/InghamGaussianWindowAbsorption.lean`, and
`Sieve/InghamCriticalGaussianTranslatedMoment.lean` close the actual left boundary premise for
the Gaussian pole-cleared scalar family. Uniformly for every translate `z` with `Re z=1/2`,

```text
integral_[-X,X] |poleClearedGaussianError_X(z+it)|^(4/3) dt
  <= C X^(251/250).
```

New universal interpretation: translation is not a demand for translation-invariant raw moments.
A translate of `[-X,X]` sits in the symmetric window of radius `ceil(|Im z|+X)`; raw error grows
only polynomially with that radius, while Gaussian distance from the window kills that polynomial
uniformly. This avoids false pointwise zeta substitution and preserves exact Route T exponent.

This materially advances Route T but is not RH. Left endpoint is closed; uniform translated
right-edge `L2` is sole missing premise of concrete Gabriel interpolation. Detector zero density,
density-to-prime supply, and final composition follow afterward.
