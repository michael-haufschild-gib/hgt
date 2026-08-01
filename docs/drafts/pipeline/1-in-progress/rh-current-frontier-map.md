# Current Formal Frontier Toward Proving or Disproving the Riemann Hypothesis

## Formal research map of HTGeometry, HilbertMetric, and RHTower

**Corpus cutoff:** 1 August 2026. “Formal corpus” means declarations reachable from the three area
umbrellas at the audited snapshot; unwired work-in-progress files are not counted as established
frontier results.

## Abstract

This paper states where the project stands now. It maps every independent route toward a
proof or disproof of the Riemann hypothesis represented in `HTGeometry`, `HilbertMetric`,
and `RHTower`, together with its proved chain, endpoint, first open premise, obstruction,
and strongest surviving theorem.

The central fact is negative but precise: the formal corpus contains no unconditional
theorem of `RiemannHypothesis` and no unconditional theorem of
`¬RiemannHypothesis`. It contains a large connected atlas of exact RH equivalents,
conditional reducers, disproof certificates, and source-independent infrastructure. After
quotienting that atlas by shared unresolved premises, the live proof frontier consists of a
smaller set of genuinely different source routes. The nearest are: the literal CCM
first-clock tail/Bohr route; fixed-width rectangular Weil lower floors; all-node
Xi-Weil form positivity; theta-cusp center-mixed positivity; critical Möbius cancellation;
all-prime Sonin closure;
Suzuki full-frequency Hermite–Biehler/Ward realization; and Xi Taylor core-current control.
The Julia compound-Poisson route is retired by an exact diagonal-energy obstruction.
Operator, Deninger, Gamma–Jacobi,
Connes/prolate, and source-domain Hedenmalm routes remain structurally meaningful but
farther upstream.

On the disproof side, the most source-explicit current route is a negative growing-order
squared-Xi reverse-Bessel radial jet. Its logical tail is closed, but all orders through
eighteen are positive and the surviving `n≥19` problem requires a moving-prime-window
comparison not present in corpus or literature.

The map uses exact Lean declaration types as authority. **RH equivalent** means a complete
target, not progress toward its source proof. **Open core** means first unproved premise
after proved connectors are removed. **Dead mechanism** kills only stated construction;
its strongest positive survivor remains part of frontier.

## 1. Current conclusion

Project has solved most connector problems and has not solved source-acquisition problem.
Nearest routes require one global source theorem: first-clock lower control, fixed-width
Weil floor, completed Hedenmalm positivity, critical Möbius cancellation,
positive-linear-excursion Sonin floor restoration and source handoff, Suzuki full-frequency
source realization, or Xi-current control. No route currently supplies that theorem.

## 2. What the foundational tower actually proves

`RHTower/RiemannTower.lean` supplies the logical skeleton:

```text
RH
↔ Xi has no zero in Re(s) > 1/2
↔ a coherent dyadic Kummer root tower exists
↔ every right-half zero multiplicity is divisible by every power of two
↔ analytic 2^k-roots exist on the right half-plane for every k.
```

`RHCharacterizations.rh_tfae` packages fifteen equivalent coordinates: right-half
nonvanishing, tower existence, all ladders, empty off-line height locus, top valuation
profile, zero census jumps, empty boxes, zero-free descent, trivial deck charge, line
holography, window certificates, and zero local modulus slopes.

These declarations are exact and valuable. They are not source producers. A proof route
must establish one coordinate from information that does not already contain Xi zero
location. The same rule applies to the hundreds of later `↔ RiemannHypothesis`
theorems.

## 3. Complete quotient of proof-route coordinates and one source-adjacent coordinate

This section quotients thousands of declarations by their first unresolved premise. Two
criteria belong to the same route when their proved chains return to the same missing
source law. Retired coordinates are marked explicitly; all others remain live at their stated open
core.

### Route A — literal CCM first clock

**Endpoint.**

- `CCMFirstClockPublishedSourceEventuallyBoundedBelow`;
- `CCMFirstClockScaledSourceAsymptoticallyBohrAlmostPeriodic`.

Both are Lean-proved equivalent to RH.

**Proved chain.**

```text
literal published first-clock source
→ exact prime creases and von Mangoldt atom recovery
→ rational divisor moments / complete source-divisor tomography
→ Landau exclusion of a right-half divisor
→ RH.
```

The Bohr form adds:

```text
continuous asymptotic Bohr model
→ bounded source tail
→ eventual lower floor
→ RH.
```

HTGeometry proves summable-spectrum screw almost periodicity, exact Bohr coefficients,
uniqueness, recurrence, full tail closure, and Torelli recovery once an asymptotic model
exists. For finite rationally independent phase packets it also proves a separated-tolerance
Haar recurrence-frequency sandwich. That finite theorem supplies neither the literal CCM
identification nor dimension-uniform control for an infinite prime packet. RHTower proves
complete single-clock source/divisor tomography.

The Bohr algebra now includes an exact product-spectrum law: for bounded continuous
almost-periodic functions represented by bounded continuous maps, the product frequency module
lies in the join of the two factor modules; a parallel theorem passes the same containment from
uniform trigonometric approximation. This closes a generic frequency-bookkeeping step, not the
literal first-clock asymptotic model or its uniform prime-tail approximation.

**Open core.** Prove directly from the literal source either:

```text
∃ C ≥ 0, A ≥ π/2, ∀ L ≥ A, -C ≤ B₁(L),
```

or a continuous Bohr-almost-periodic asymptote for the scaled source.

**Obstacle.** A zero-frequency top layer, accumulating spectrum, or failure of uniform
remainder separation can evade the existing AP-vanishing theorem. Torelli recovery occurs
after model existence and therefore cannot supply it.

**Assessment.** Nearest single-source route and cleanest current endpoint.

### Route B — fixed-width rectangular Weil floor

**Endpoints.** For one fixed width `L > 0`, the rectangular logarithmic Weil samples are
eventually bounded below. Lean proves this equivalent to RH. An exact positive-quadrature
chart is also closed: RH is equivalent to eventual domination of the positive prime-wall
mass by completed positive archimedean lag mass, equivalently to domination of the
positive Mangoldt quadrature by that completed lag mass.

**Proved chain.**

```text
¬RH
→ rightmost right-half Xi divisor
→ dominant rectangular Dirichlet coefficient
→ Landau singularity and shifted-zeta/Xi order contradiction
→ rectangular samples cofinally diverge to -∞.
```

Equivalent charts include multiplicative screw curvature, negative-channel abscissae,
cumulative negative mass, holomorphic continuation, and adjacent critical-Mellin block
imbalance.

The sharp rectangular identity is now oriented entirely between positive objects:

```text
Weil polarization + fixed Euler–π boundary charge
= positive continuous completed-lag mass - 2 × positive prime-wall mass.
```

The completed lag has an explicit strictly positive zero-lag lower carrier,
`2L·e⁻ᵗ/(1-e⁻ᵗ)·(1-e⁻ᵗ/⁴)`, under the rectangular window hypotheses, and the sampled
positive channel lies pointwise between zero and the completed kernel. This identifies the
source of archimedean strictness but does not by itself dominate the prime wall.

Pairwise-disjoint equal-mass log-Haar cells pay monotone prime branches, and every
unresolved atom is localized to a bounded turning seam. Exact obstructions show that an
apex atom has no positive-volume pointwise dominating cell, even along a cofinal
powers-of-two family, and that bicausal splicing creates only duplicated seam mass rather
than new capacity.

**Open core.** Construct source-specific grouped apex/flank transport across turning seams
at capacity one, paying the fixed boundary charge and proving tail quadrature domination.
Equivalently, prove one fixed-width lower floor from prime–Gamma or theta source without
invoking global Weil positivity.

**Obstacle.** Finite-cutoff positivity has a tail budget. Recent finite Guinand–Weil
theorems quantify certification but do not produce the required cutoff-free floor.
Pointwise apex transport and free bicausal splicing are formally dead.

The literal Groskin rank-two archimedean tail kernel is now present in Lean without a
computed cutoff. The digamma density is proved to tend to `+∞`, an analytic eventual
positivity threshold is selected, and every compact tail-window increment beyond that
threshold is positive semidefinite. This imports the Loewner-monotonicity core of Groskin's
Theorem 3.2. Strict positive definiteness, strict total positivity, the improper infinite
tail, and Corollary 3.3's trace/eigenvalue budget are not yet formalized and the result does
not pay the rectangular boundary charge.

### Route C1 — complete Xi-Weil/Hedenmalm-form positivity

**Endpoint.**

- `riemannHypothesis_iff_xiWeilPolarization_nonneg`;
- `HedenmalmXiPositiveFormWall`.

**Proved chain.**

```text
nonnegative completed form on every admissible test
→ every Xi spectral point real
→ RH.
```

**Open core.** Construct the complete positive form from literal source on its full test
class. This premise is not source-level equivalent to the theta Fourier-current premise
below; no theorem converts one missing sign law to the other without traversing RH.

### Route C2 — theta-cusp center-mixed Fourier current

**Endpoint.** `thetaCuspCenterMixedFourierNonnegative_iff_riemannHypothesis`.

**Unconditional progress.**

- actual positive center-mixed theta density;
- exterior-aperture positivity;
- central frequency band through `|b| ≤ 218/25`;
- global ordered three-point PSD;
- nondegenerate two-node positivity;
- several order-three chambers;
- fourth reflection-jet Hankel positivity;
- exact incomplete-Gamma shell coordinates;
- higher-shell value quadrants and horizontal derivative directions;
- absolute far-shell convergence;
- exact coupled-cone integral normal form.

**Open core.** Prove the actual Fourier-current sign in the remaining interior
high-frequency region
`0 < a < 1/2`, `|b| > 218/25`.

**Exact unresolved data.**

1. signed ground-shell cancellation without total-variation loss;
2. transverse derivative components;
3. cofinal reflected product-fibre compensation after every finite endpoint order
   cancels.

**Obstacle.** Pointwise cone-kernel positivity is false. Every fixed finite shell prefix
has the wrong cusp asymptotic; only the infinite completion cancels it. Generic positivity,
log-concavity, and fixed local derivative order cannot close the route.

### Route D — prime–archimedean Hankel sign and reconstruction

**Endpoint.**

- `PrimeArchSourceTraceHankelIntNonnegative`;
- `PrimeArchSourceMomentHankelExactReconstructionPhase`.

The degree-tail and exact reconstruction formulations are RH equivalent.

**Proved chain.**

```text
all-polynomial prime–Gamma source Hankel nonnegativity
→ complete countable Weil source cone
→ RH.
```

HilbertMetric proves existential unisolvent reconstruction for independent features and an
equivalence at arbitrary prescribed nodes. It does not construct reconstruction on the
fixed prime–archimedean source packet or establish its all-degree sign.

**Closed carrier classifications.** Two carrier loopholes are closed unconditionally in Lean.

1. `primeMellinJet_eulerSubsetPositiveLift_classification`: even arbitrary off-diagonal prime
   outputs and an arbitrary fixed Gamma/polar boundary cannot make positive-log Mellin packets
   bounded while preserving exact positivity for every finite Euler subproduct. Four-subset
   polarization forces zero real cross-prime covariance; divergent local prime energy remains.
2. `IsPrimeArchMomentWitness.eq_primeArchXiCompactMomentMeasure`: every unrestricted positive
   measure representing the complete source moments, with no support hypothesis, equals the
   canonical compact atomic Xi-divisor pushforward. Unique carrier existence is exactly RH, and
   every Euclidean spectral realization has this same observable pushforward.

Together with the existing Krein constraint—positive isotropic reciprocity is zero and the full
doubled signed reciprocity graph is Lagrangian with zero quotient—this retires diagonal mixing,
subset-natural off-diagonal mixing, naive positive quotienting, and alternative moment carriers.

**Irreducible open core.** Construct a genuinely global signed prime–Gamma boundary/domain defect
whose positive quotient is formed only after completion, and prove its resolvent-flux identity with
the literal source. This is no longer a reconstruction-node or carrier-selection problem. The
identity pins the quotient divisor to Xi; its positivity is global Weil positivity and therefore
exactly RH.

**Obstacle.** Low theta moments do not weaken the target. Lean proves any infinite exact
degree set already reconstructs the full cone by opposite high-degree perturbations.
Zero-selected tests are circular. Positivity and reciprocity alone underdetermine the divisor:
reciprocal spectral pairs can be adjoined unless the exact resolvent-flux identity is proved.

**Assessment.** Route D's carrier/reconstruction freedom is fully classified. RH is neither proved
nor disproved. No independent source-first Route D mechanism remains below the global
boundary-defect/Weil-positivity theorem.

### Route D2 — continued prime–arch high-frequency ceiling

**Endpoint.** `ContinuedPrimeArchPositiveFrequencyAboveImBoundedAbove 4 ↔ RH`.

**Proved chain.**

```text
verified central band through height 9/2
+ any finite upper ceiling for continued prime–arch imaginary source above frequency 4
→ global upper ceiling by reflection
→ RH.
```

If RH is false, the source exceeds every finite ceiling at admissible points above four.

**Open core.** Construct any finite uniform upper bound from literal source. Existing
central-band sign cannot propagate itself to high frequency.

### Route E — critical Möbius/Mertens cancellation

**Endpoints.**

- critical or strict-half Mertens bounds;
- half-polylog discrete Laplace decay;
- additive triangle and second-Cesàro bounds;
- `MobiusLaplaceCofinalGammaHankelOffDiagonalFrequentlyUpperBounded`.

**Proved chain.**

```text
critical Möbius decay or cofinally bounded off-diagonal covariance
→ Mellin continuation / strict-right L² energy
→ ζ nonvanishing in Re(s) > 1/2
→ RH.
```

The Gamma–Hankel split removes diagonal and lower-bound obligations. Only sparse upper
bounded returns are needed.

The Plücker normal-cone branch now has a cofinal diagonal on `Re(s) > 1`: for every
positive critical sequence tending to zero, Lean constructs a monotone cofinal exhaustion
by finite prime sets whose Euler-normal source transfers converge locally uniformly to the
reciprocal squarefree section. The same diagonal survives multiplication by the inverse
archimedean factor and projectivization to the negative reciprocal-square horizon. Fixed
finite prime apertures still cannot have a finite Euler-normal limit. These theorems combine
finite-prime exhaustion with the Euler-boundary and Gamma-completion limits, but all
convergence remains in the absolutely convergent, zero-free Euler half-plane and supplies
no continuation to critical Möbius data.

Verjovsky's shrinking-arc local-moment theorem gives another exact Mertens coordinate:
subpolynomial local moments for every finite order, or for an unbounded admissible set of
orders, are equivalent to RH. Its unconditional moment-to-point inequality converts local
`L^q` control into a bound for `M(N)`, but supplies no Möbius local-moment estimate. It is
therefore an upstream Route E connector, not a new source producer, and is not formalized.

**Open core.** Prove cofinal upper bounded returns of the actual upper-signed Möbius
Gamma–Hankel covariance, or an equivalent critical Möbius cancellation estimate, from a
nonlocal all-prime law.

**Killed mechanisms.**

- fixed-order Gowers uniformity supplies only logarithmic savings;
- second fixed-prime removal has a negative lobe;
- ternary divisor insertion pays excessive mass;
- Lambert lifting collapses to the binary source or loses two powers;
- positive semiprime LCM blocks have excessive cubic mass.

**Positive survivor.** Difficulty localizes to the supercritical LCM boundary; bounded
returns suffice, not uniform all-aperture control.

### Route F — all-prime Sonin transfer

**Endpoints.** Per-test, finite-moment, cofinal-block, and valuation-cone Sonin-to-prime
coupling interfaces, each with an RH conclusion.

**Proved chain.**

```text
positive Sonin finite/block/moment values
+ source-faithful closure onto literal prime–arch Hankel values
→ prime–arch source cone
→ RH.
```

**Unconditional progress.**

- aperture refinement is strictly subadditive;
- lost-layer coupling energy is positive and divergent;
- inverse-dilated packet physical cutoff and physical-band error vanish exactly;
- a square-root norm floor follows from the packet-energy floor under the stated mean and
  square-tail hypotheses;
- the remaining coupling-band budget is exactly three packet-frequency norms at radii
  `rb`, `ra`, and `b`;
- concrete squared estimates on those three terms are proved and bound the budget by an
  explicit square-root expression;
- the packet mean is eliminated from that bound, giving one annulus-free expression
  uniform over every packet in a shell cut;
- a sharper replacement retains the mean's own tail estimate rather than bounding it by
  one, reducing the band term to one gap-tail times a fixed profile constant;
- division by the explicit norm floor has a closed form: each sharp band slack is the
  gap-tail factor times the square root of band radius divided by shell width and fixed
  profile mass, exposing exactly which coupled scales must vanish;
- the reference tail majorant absorbs every fixed polynomial weight, including the square-
  root radius weight occurring in the middle slack term;
- the packet norm floor is explicit and positive, and the resulting energy theorem has no
  free analytic parameter beyond the shell schedule and its stated tail/slack conditions;
- the shell schedule itself is now explicit: tying the scale to a cut into `N` annuli makes
  half-width times scale exactly one prescribed product; middle and high-side normalized
  slacks then depend only on that product, while the outer slack vanishes with refinement;
- one product can be chosen to satisfy both packet-tail conditions and both product-driven
  slack obligations, and after that one arbitrarily fine cut can satisfy every remaining
  scale, aperture, and outer-slack obligation; the total normalized slack is an exact sum
  of those three terms;
- right composition by the moving dilation preserves Hilbert–Schmidt energy, so the
  three relative-ideal error energies have one exact aperture-dependent, scale-free sum;
- one fixed schedule product and starting cut now give a single admissible sequence of
  scales whose successive-layer coupling energy is bounded below by a positive linear
  function of both annulus count and scale;
- one analytic comparison also excludes every logarithmically capped additive term in the
  typed completed-packet model along the schedule;
- more generally, every sublinear scalar additive term `f(scale)` in the typed
  `soninCompletedPacketValueVar` model fails along the constructed schedule when
  `f(r)/r → 0`, even if `f` is positive and unbounded.
- conversely, any typed additive term restoring the floor for every admissible schedule is proved not to
  satisfy `f(r)/r → 0`;
- more sharply, one explicit `s > 0` is constructed such that every typed contribution
  eventually bounded by `s r` fails on one admissible schedule, while any contribution
  restoring the floor for every admissible schedule must satisfy `s r < f(r)` frequently;
- every uniformly bounded family of continuous linear operators paired quadratically against
  a uniformly bounded vector sequence produces a bounded contribution sequence and therefore
  fails to restore the typed floor;
- more generally, even an unbounded channel family fails when its images on the bounded packet
  vectors admit a sublinear-in-scale norm envelope; the operator norms themselves need not be
  bounded;
- the canonical unscaled Sonin packet has a uniform twelfth-order pointwise spectral-density tail
  beyond twice its carrier and an integrated eleventh-order Fourier-cutoff energy tail;
- for the actual frequency-side logarithmic channel, the exact shell-energy split separates
  the finite sub-cut logarithmic mass from the outer weighted tail. A power tail gives a bound
  independent of tower height. For rescaled Sonin packets, choosing the least cut past twice the
  carrier removes both tower height and cut index: the bound depends only on base, ratio, carrier,
  half-width, packet norm, and an outer inverse power of `δ * (2w)`. This isolates possible growth
  to an explicit carrier logarithm and packet data; it does not construct a floor-restoring
  completion.
- composing that carrier bound with the sublinear-image no-go now closes the full
  frequency-side logarithmic-channel family for arbitrary tower heights whenever carrier is at
  most proportional to schedule scale, half-width times twice the carrier has a fixed positive
  lower bound, packet norms are uniformly bounded, and the stated positivity/mean hypotheses hold;

**Open core.** Construct a literal all-prime typed additive completion whose lower floor exists for
every `κ`, every starting index, and every admissibility proof in the schedule theorem. Only under
that universal premise is frequent domination of one explicit positive linear rate proved
necessary; no such necessity is proved for one selected schedule or for an unreduced semilocal
operator.
Alternatively prove that the arithmetic completion is not governed by the typed model, then
establish the source handoff. Schedule existence,
scale-free ideal discount, one-sequence linear coupling growth, the actual logarithmic-shell
channel's arbitrary-height family under its exact packet hypotheses, uniformly bounded
operator-family quadratic
contributions, sublinear-image channel families, and every scalar contribution eventually below
the proved positive slope inside
that typed model are closed. No corpus theorem constructs a source-faithful positive-linear-
excursion compensation satisfying the floor or reduces a semilocal operator completion to this
scalar model.

**Dead mechanisms.** Bounded scalar, uniformly bounded operator-family quadratic, sublinear-image
channel-family, fixed-operator,
Burnol counterterm, position-side,
aperture-refinement-only and actual logarithmic-shell completions fail; every sublinear scalar
additive term, and more generally every term eventually below the proved positive linear slope,
inside the typed completed-packet model also fails. Mere unboundedness or merely nonzero normalized
limsup below that slope is insufficient within that model.

### Route G — Suzuki Hermite–Biehler, anti-Pick, and Ward realization

**Endpoint.** `SuzukiHermiteBiehler xiHedenmalmDeBrangesE` implies RH without a
simplicity hypothesis.

**Proved finite/source chain.**

```text
finite self-adjoint extensions and interlacing
→ finite anti-Pick identity
→ signed partial fractions and residue signs
→ measure-level anti-Pick law
→ half-plane Herglotz representation and support theorem.
```

Finite projective spectral algebra is now exact: projective chord is a sum of spectral gaps
times source Plücker minors; in two modes its sign is exactly source-minor orientation under
ordered nodes and positive source-weight product. Marked affine secant has a full finite
spectral double sum plus homogeneous channel.

At the abstract compact self-adjoint resolvent level, discreteness is now derived rather
than assumed: real spectral points outside any neighborhood of zero are finite, hence only
finitely many model levels can lie in a fixed negative band. This removes the auxiliary
finiteness premise from the finite Morse completion once a compact source resolvent and its
level identification are supplied; it does not construct either object.

The critical prime-power wall field now has a positive Hermitian carrier without erasing
phase: every finite height section is an exact rank-one Gram matrix, its diagonal is the
positive von-Mangoldt wall weight, and its functional-equation-reflected anti-diagonal is
the far delayed-hinge numerator. This identifies the right positivity type but does not
orient an aggregate of distinct source atoms; rank one at each atom is not the global
chord-mass theorem.

The wall branch extends further. Finite reflected-current packets have an exact
positive-minus-negative light-cone Gram completion. Cubic aperture dressing gives an
all-prime Hilbert completion; summing valuation depth supplies a sharp positive floor;
and coherent causal depth fusion gives an absolutely convergent all-prime cross-prime
Gram with a faithful height separator. For the affine inverse-Krein defect, the negative
part is also the unique least—and hence the unique Loewner-minimal—continuous functional-
calculus correction among commuting positive completions. The completed aperture carrier
nevertheless has height-flat diagonal and cannot by itself supply Xi curvature, and the
abstract least correction has not been identified with the literal arithmetic source.

**Required continuation.**

```text
actual monotone source eigen-coefficient law
→ source-selected chord-mass gap
→ full normalized jump Pick kernel / Ward semiboundedness
→ Hermite–Biehler for the global Hedenmalm pair
→ RH.
```

**Open core.**

1. actual source coefficient law;
2. chord-mass threshold;
3. full normalized jump kernel;
4. orientation and sufficient aggregate mass of actual source minors;
5. control of homogeneous channel and passage from finite spectral sums to global carrier;
6. identify the actual division-free Robin/Gamma/holonomy or Gamma-projected rectangular
   trace with, or dominate it by, the forced negative-light Gram channel while retaining
   marked half-gap and holonomy Schur debts;
7. prove the resulting rectangular Ward residual uniformly lower-semibounded.

**Dead predecessor.** The legacy entire compact-limit target is impossible because the
actual quotient has genuine poles. The live route is meromorphic and full-frequency.
Further exact no-gos show that the fused observer rectangle is not the literal sharp trace
cell, local positive semidefiniteness does not survive subtraction of twice the prime
block, no finite uniform inverse gain recovers sharp wall from damped causal response,
and the undressed sharp all-prime wall source cannot lie in ordinary `ℓ²`. The survivor is
finite cutoff plus a genuinely renormalized or semifinite limit with cutoff-dependent
unbounded relative observation.

### Route G2 — relative-Volterra phase source-germ weld

This is a separate disjunctive route; it bypasses Suzuki coefficient monotonicity,
chord-mass, Pick-kernel, Ward, and Hermite–Biehler obligations.

**Unconditional algebra.** `2V = C + iH`, with `C` and `H` self-adjoint. Under explicit
hypotheses that the reflection operator is self-adjoint and conjugates `T` to its adjoint,
`C` is reflection-even and `H` reflection-odd; odd-sector claims additionally require the
reflection square to be the identity.

**Endpoint.** `riemannHypothesis_of_suzukiVolterraPhaseEulerDefect_source_germ_weld`
concludes RH from analytic response/Weyl packages, real-zero conditions, and the seed
source-germ identity.

**Open core.** Prove the actual phase Green/Christoffel–Darboux Euler-defect source-germ
weld (`hseed`) and discharge its analytic and real-zero premises from source.

**Retired transfer mechanism.** Under the stated reflection structure, sign or positivity
of the symmetric coordinate cannot simply be transferred to the complementary phase
sector. The exact difference identity is an algebraic separation, not an unconditional
universal impossibility theorem.

### Route H — Xi Taylor/theta core current

**Endpoint.** `XiCTaylorThetaTailCoreCurrentSublinearUpper`, with several equivalent
schedule and remainder formulations.

**Proved chain.**

```text
unconditional superaccurate Taylor schedule
+ sublinear oriented core-current bound
→ absence of transverse Xi zero
→ RH.
```

**Open core.** Control the actual off-diagonal Hermitian block/top-row translation current.

**Dead shortcut.** The combined finite-arithmetic remainder is invariant under admissible
Haar-depth refinement and tends to four times the unresolved current, not zero. Prefix and
top-row decay cannot dissipate it.

**Positive survivor.** Exact refinement conservation identifies the current that must be
oriented directly.

### Route I — sharp dyadic prime window

**Endpoint.** `DyadicWeightedPrimeWindowSubpowerUpper N`.

**Chain.**

```text
sharp weighted-prime main term + subpower error for all large n
→ Landau/shifted-zeta contradiction at a right transverse zero
→ RH.
```

**Open core.** Prove the sharp dyadic error from source. Monomial-tail and finite-degree
estimates cannot reach the necessary height-linear range.

### Route J — Julia compound-Poisson coherent energy

This route is distinct from older diagonal Julia attenuation.

**Endpoint.** There is no standalone Julia-to-RH theorem. The intended handoff is to
Route A: use Julia energy to prove the literal completed first-clock source has an
eventual lower floor.

**Proved chain.**

```text
literal compound-Poisson equilibrium source
→ exact variance 3/2
→ normalized Julia defect kernel
→ positive definiteness on the real line
→ bad-origin-correlation² ≤ coherent cross-prime energy
→ negative completed source forces a squared excursion into that energy.
```

The equilibrium kernel is now an actual characteristic function, not only an abstract
positive-definite kernel: source gives an explicit compound-Poisson law with zero atom
`1/(2√2)`, a square-biased law with density `(2/3)x²`, and an independent centered
triangular-clock realization. `CharacteristicDefectGramCapacity` packages the universal
finite-second-moment anchor-correlation bound used directly by RHTower. It also proves
`0 ≤ K ≤ 1` and the finite two-packet Cauchy inequality. The raw totalized Julia
profile is not positive definite because its value at zero is wrong; the corrected spectral
extension is essential. Its Lévy density is strictly positive, and the critical Dirichlet
density has an exact finite scale-four decomposition into positive Julia innovations plus
one unresolved tail.

**Proved finite hierarchy.** `bad correlation² ≤ coherent energy ≤ total bad mass²`.

For the literal signed prime-power packet, the stronger completed-packet formulation is
now closed at every finite aperture: prime and archimedean-plus-prime coherent energies
are nonnegative; the squared completed attenuated value is bounded by completed coherent
energy; its squared deviation from continuous budget is bounded by full signed prime
energy; good/bad cross-correlation obeys the two-packet determinant inequality; and, on
the admitted window, signed energy is exactly good energy plus bad energy minus twice
their cross term. The literal/good/bad coherent Gram is positive semidefinite but exactly
singular: the pointwise source relation gives null vector `(1,-1,1)`. Thus adding all three
channels creates no independent coherent capacity. This bypasses cutoff and good/bad
splitting in the primary capacity bound while sharply classifying its boundary.

**Exact closure.** Prime exhaustion and zero-scale de-attenuation were already finite-window
theorems; the actual residue was the proposed global energy budget. That premise is false.
At `L_m = 6 log m`, every prime in `(2m⁴,5m⁴]` is admitted with exactly one mode and
phase in `(4π/3,3π/2]`. Its squared bad coefficient is at least
`(log p)²/(4p)`. Pointwise positivity and unit diagonal of the Julia kernel retain all these
terms, while the unconditional Chebyshev block law gives, for every Julia scale `x`,

```text
E_bad(x,L_m) ≥ log(m)/20.
```

`ccmFirstClockJuliaFullBadCoherentEnergy_sixthPower_lower` proves this exact floor;
`ccmFirstClockJuliaFullBadCoherentEnergy_unbounded_uniformly_in_scale` proves uniform-in-scale
unboundedness. Conversely, `tendsto_ccmFirstClockJuliaFullBadCoherentEnergy_zero` proves that
zero scale restores rank-one energy `(sum_p B_p)²`, not cancellation.

**Positive survivor.** Literal Julia coherence has a two-boundary classification: every scale
retains an arithmetically unbounded diagonal, while zero scale restores maximal rank-one
coherence. Post hoc diagonal subtraction is also formally impossible for the normalized anchor
capacity law: a one-node unit packet would require `1 ≤ 0`.

**Status.** `RETIRED / FORMALLY CLOSED NO-GO`. The unrenormalized Route-J energy-budget handoff
cannot prove Route A's floor. Only a new source-defined principal-relative current, with its
counterterm inserted before good/bad positive projection and with a new orientation theorem,
survives; that is not Route J.

### Route K — quadratic spectral realization

**Endpoint.** `XiQuadraticSpectralReality ↔ RH`.

**Needed chain.**

```text
source-built closed self-adjoint realization of -D(D+1)
+ every Xi zero supplies ρ(ρ-1) in its spectrum
→ real quadratic spectral parameter
→ strip and no-real-zero facts
→ RH.
```

**Open core.** Construct operator, domain, and scattering determinant from arithmetic
source without selecting the Xi divisor. The current module explicitly asserts no such
realization.

### Route L — Deninger/Hodge/cohomological realization

**Endpoint family.** Oriented Hodge, Weil-transport, dense-range, resolvent, and
divisor-spectrum inclusions, all conditionally implying RH.

**Needed chain.**

```text
literal arithmetic relevant complex
→ positive Hodge/Kähler polarization
→ one-way inclusion of every Xi divisor eigenvalue
→ spectral real-part 1/2
→ RH.
```

**Unconditional infrastructure.** Weil-height/Kummer groups, L¹/L² completions, real
scalar extension, a completed real Hilbert/Kummer inner-product package, radial flow,
Poisson realization, polar-sign correction, Fredholm kernel reductions, and exact lifting
of compact-group invariants through equivariant surjections by Haar averaging. Generic
dense-span orthogonality also makes the Kronecker phase functional nonzero off zero, and
the suspension radius is exactly deck-invariant and scales linearly in the suspension
coordinate. For every countable family of nonzero Hilbert vectors, the locus orthogonal to
none of them is a dense `Gδ`. On every finite real torus, the linear orbit is now proved
dense exactly when its integer annihilator is trivial, through a formal Weyl criterion.
The generic fine-point carrier also has explicit modulus and phase one-parameter groups,
their affine conjugation/bracket law, rank-two generators, integrated leaves, Frobenius and
Galois naturality, and suspension-flow transversality. These close the generic Kronecker and
affine-foliation mathematics, not the arithmetic identification of the frequency vector,
prime fibres, relevant complex, or Xi spectrum.

In a standalone half-line complex-pair ODE model motivated by an affine leaf, each nonzero
frequency has an explicit decaying closed/coclosed-labelled chiral solution with squared norm
`1 / |μ|`; every square-integrable solution of the stated ODE is its scalar multiple, while
zero frequency has no nonzero square-integrable solution. Opposite frequencies have the defined
pairing `i / μ`, positive star-pairing value `1 / |μ|`, and the defined power pullback shifts
`μ ↦ q μ` with pairing weight one. The radial solution is also tensored with Fourier characters
on `UnitAddTorus` to form a concrete analytic cylinder model: Haar integration makes distinct
characters orthogonal, gives the same reciprocal-frequency norm, kills cup pairing unless the
characters are opposite, recovers `i / μ` for the opposite pair, and makes the normalized modes
orthonormal. A continuous torus function whose coefficient against every character vanishes is
identically zero, and two continuous torus functions with equal character coefficients agree.
Frequency is the integer-character pairing with the same Kronecker direction used by the
dense-orbit criterion. The Kronecker derivative now transposes through Haar integration onto each
character with its exact frequency. Consequently, under joint continuity and the stated leafwise
derivative system, every nonzero-frequency character coefficient solves the radial Hodge ODE and
every square-integrable coefficient is a scalar multiple of the explicit mode; vanishing of all
coefficients forces a continuous torus slice to vanish. This closes coefficientwise descent and
uniqueness, not a Fourier expansion or completeness theorem for arbitrary square-integrable
cylinder data. No Lean theorem identifies this analytic cylinder with the separately defined
integrated affine-leaf carrier or with the arithmetic relevant complex.

The generic packet layer is also stronger. On a compact probability packet, averaging splits
continuous real functions exactly into constants and zero-average functions and obeys mean-modulus
and quadratic-mean bounds. The same average is provably nonlocal on any proper clopen restriction,
and a clopen set of intermediate mass produces a nonzero zero-average mode. It therefore cannot be
used as an endomorphism of an ordinary sheaf; any arithmetic comparison must keep this global
retraction separate from local sheaf maps. Every open cover of a compact totally disconnected factor times a
compact manifold admits a finite subordinate continuous family summing to one, locally constant
along the first factor, and smooth along the manifold factor; the circle case is explicit. The
exported fineness theorem does not assert nonnegativity. A separately defined suspension with
trivial monodromy is homeomorphic to the product with `AddCircle T`. The concrete candidate unit
group `U_p = ∏_{ℓ ≠ p} ℤ_ℓˣ` is now defined, proved compact Hausdorff and totally disconnected, and
`U_p × Circle` is smoothly fine. No theorem identifies `U_p` with the automorphism group of the
prime-to-`p` roots of unity, forms the required quotient by the closure of `p`, proves the
Frobenius action trivial there, or identifies the generic period with `log p` and the resulting
space with Deninger's actual prime fibre.
Separately, an abstract
symbol additive in every entry over a torsion group is torsion; a group generated by such symbols has
zero real tensor product. This is not an instantiation of Milnor K-theory over an algebraic closure
of a finite field or of the arithmetic relevant complex.

**Open core.** Complete the unit-group/closure quotient and prime-fibre comparison; identify the
trivial-monodromy mapping torus, packet, symbol, and
coefficientwise cylinder constructions with
the literal arithmetic Meyer/Deninger relevant complex; establish radial Schwartz and global
square-integrable domains, a valid local/global interface for the nonlocal packet average, nuclear
topology and closed range, nonradial acyclicity, arithmetic
cup/trace/flow/Hodge transport, nuclear almost-idempotence, middle-kernel vanishing, and
source-to-Xi spectrum inclusion.

The generic contraction hypotheses are now instantiated unconditionally on
`ℓ²(ℕ,ℝ)`: the unilateral shift is an eigenvector-free linear isometry, its range is
orthogonal to the first basis vector, and the unit sphere is contractible. No theorem
identifies this model with the arithmetic Deninger completion or transports its source,
flow, cup product, or spectrum, so this closes generic angular topology, not arithmetic
comparison or spectral realization.

### Route M — Gamma–Jacobi singular reader

**Unconditional progress.** Odd artanh heads converge to the source coordinate; adaptive
head plus residual recovers the full coefficient; singular normalization is forced;
rank-one Szegő tail transgression and adjacent residual coordinates reconstruct prime
labels; reciprocal counterreader nodes form a Blaschke-admissible boundary sequence.

**Needed chain.**

```text
joint infinite-index Krein head/tail object
→ completed Euler cyclic reader
→ positive jet-opening flux
→ fibre-pointed Berezin orientation
→ RH.
```

**Open core.** Construct the joint object, prove convergence of finite inner factors, and
identify the forced outer factor.

### Route N — Hedenmalm all-prime normal boundary

**Endpoint.** `XiCZeroHedenmalmPrimeNormalSubLogSquare`.

**Proved identity.**

```text
prime-normal energy
= vertical clock energy + radial reflected energy.
```

Sub-`(log X)^2` energy at Xi zeros forces the centered imaginary coordinate to vanish.

**Open core.** Prove a uniform source-domain sub-log-square estimate for every vector in
the closed theta Grushin domain, before specialization to a root, retaining the full Jordan
tower.

**Dead predecessor.** Strict descent of every named Xi root block into the
prime-harmonic Besicovitch domain is already RH equivalent.

### Route O — Connes restricted-Weil/prolate limit

**Endpoint.** `ConnesXiGroundStateLimitWall ↔ RH`.

**Open core.** Prove a source-locked comparison between the actual restricted-Weil ground
state and the prolate seed, including the two prolate-to-Hermite coordinate limits and
rigorous convergence of the finite spectra/determinants to Xi.

**Circularity warning.** Arbitrary real-zero entire approximants are an RH mirror:
under RH, constant Xi-based sequences witness the property.

### Route P — completed-seam Thorin/Markov representation

**Endpoint.** Compact Thorin exponent and compact Markov germ representations are RH
equivalent.

**Proved content.** Compact moment determinacy makes any witness unique; RH supplies the
canonical divisor measure.

**Open core.** Construct the literal compact positive carrier from source without using
the Xi divisor.

**Obstacle.** Uniqueness closes alternative-carrier freedom; it cannot establish
existence.

### Route Q — theta–Cassini boundary saturation

**Endpoint.** `ThetaCuspCassiniInwardBoundarySaturated ↔ RH`.

**Unconditional progress.**

- aperture-independent positive theta carrier;
- all raw latent Hankel blocks strictly positive definite;
- exact nonlinear inward response;
- unique entire continuation from the boundary germ;
- a unique power `α_* > 1` whose calibrated reciprocal pushforward matches degrees zero
  and one.

**Open core.**

1. test and then control the `α_*` carrier from degree two onward;
2. construct a fixed compact positive Markov carrier for the actual response; or
3. prove the boundary Jensen/jet saturation inequality directly.

**Dead producers.** Raw reciprocal square-gap carrier has wrong mass; calibrated
`α=1` carrier fails at degree one; one-particle infinite divisibility fails by atomic
support. A two-particle completion survives but has no transform identification.

No Route R is assigned at this snapshot. The following divisor-fed coordinate is retained for its
exact identities but fails the paper's source-independence criterion for a live route.

### Non-route coordinate — divisor-fed prime-seam submass

**Endpoint.** `XiPrimeSeamPairEnergySubmass ↔ RH`.

**Unconditional progress.** The degree-one Euler functional-equation coefficient energy
is identified exactly with a horizontal prime-seam weighted norm square. Prime-pair
difference energy divided by reciprocal prime mass converges to twice this quantity, and
the energy controls `(Re(ρ)-1/2)^2 (log 2)^4` on a divisor fibre.

**Classification.** This is not yet a live source route. The predicate quantifies directly
over `XiDivisorSupport`, and its fibrewise content is exactly `Re(ρ)=1/2`; even the
first-coefficient energy remains parameterized by `ρ`.

**Potential promotion condition.** Construct a source-to-divisor-fibre all-prime/Sonin
operator that produces submass growth or zero first-coefficient energy without selecting
the Xi divisor.

**Obstacle.** Existing identities expose and coerce the quantity but do not orient it on
Xi fibres. An outer Euler modulus or prime-seam coupling remains unproduced.

### Route S — source algebraicity and dynamical mirrors

This quotient includes Arakelov power orbits, Hurwitz anchor circuits, Böttcher charges,
Kummer/Jordan conditions, valuation sectors, deck charges, and related dynamical
coordinates.

**Status.** Exact consequence atlases or fringe rigidity routes.

**Open core.** An independent source theorem must produce algebraicity, integrality,
contractivity, finite differential capture, or divisor-preserving dynamics on Xi fibres.
No such producer exists. Expected coordinates are often transcendental, so these are not
leading routes.

### Secondary criteria with no new primitive source

The following families reduce to Routes A–S or remain bare equivalences:

- Li coefficient and shifted reciprocal moment criteria;
- Pólya-frequency and consecutive Xi-coefficient Toeplitz-minor criteria;
- Nyman–Beurling/Báez–Duarte closure and its scalar Hardy-cost abstraction;
- Salem integral exclusion;
- Hardy and Colombeau closure criteria;
- theta-infinity and arbitrary-length mollifier criteria;
- Burnol co-Poisson scalar/parity criteria;
- OPUC and phase-adapted Prouhet terminal identities;
- Hurwitz FE/Schwarz seam, current, and energy charts;
- outer Euler modulus × prime-seam coupling;
- divisor-fed Xi prime-seam submass;
- determinant-line and spectral-flow no-first-crossing charts;
- function-field `q → 1` degeneration;
- hyperbolic/adelic scattering;
- multivariate stable-section models;
- radial Jensen/Schur norm gaps;
- Böttcher, QECC, static-Choi/observer, and universality atlases.

They remain useful coordinates. None adds an independent source producer.

The exact local Nyman–Beurling scope is smaller than its module commentary: Lean defines the
normalized half-plane kernel and vanishing floor and proves their scalar identities, positivity,
inverse-height upper degradation, and a complementary reciprocal-length inequality. It does not
formalize the fractional-part generators, their Mellin transform, the global closure equivalence,
or an RH connector. Yang's August 2026 localized Friedrichs-angle theorem adds an RH consequence
and unconditional subspace-sum structure, not a distance estimate tending to zero. A Nyman route
therefore remains a classical equivalent closure problem with no new primitive source theorem in
the corpus or located literature.

The local Pólya-frequency scope is likewise smaller than its commentary: Lean proves generic
even-pair/cosh identities, positive finite cosh pairings, and tautological transport of an assumed
`PF ↔ Reality`; it does not formalize the Schoenberg Xi equivalence or literal consecutive
Xi-coefficient minors. `HankelToeplitzWindow` proves an exact factorial window and a generic
order-two log-convex moment inequality, not all Toeplitz minors. Michalowski's July 2026 theorem
proves `D_{r,k} > 0` uniformly for `r ≥ 2` and `k ≥ 10^18 r^3`, but leaves the entire complementary
region—and especially the RH-critical cone `k = O(r)`—open. Its analytic gates use directed-rounding
certificates, so it is not imported under the no-computation rule. The theorem supplies a sharp
external boundary for this secondary criterion, not a source theorem for any live route.

## 4. Role of HilbertMetric

HilbertMetric has no RH declaration. Its mathematical statements form a source-independent
mechanism layer, except that `FourthCurvatureMixture.lean` currently has an implementation
dependency on an HTGeometry integral inequality.

### Closed infrastructure

- finite Gaussian Fock determinant laws;
- CCR dimension/variance identities on invariant blocks;
- rank-one Gaussian metric curvature;
- symmetric-Fock lowering and phase classifications;
- Slater/Plücker and quasi-free rank/variance laws;
- finite unisolvent evaluation and prescribed reconstruction;
- exact three-point determinant/angle/Riccati criteria;
- fourth-reflection and positive-mixture transport;
- dense scalar functional rigidity;
- character-intertwiner trace obstruction.

### Direct RH handoff

```text
HilbertMetric.PrescribedEvaluationReconstruction
→ RHTower.PrimeArchHankelDeterminantCriterion
→ PrimeArchSourceMomentHankelExactReconstructionPhase
↔ RH.
```

Existence of some unisolvent nodes is closed, and reconstruction at prescribed nodes is
characterized exactly. Reconstruction and PSD for the fixed prime–arch source nodes are
not proved.

### Complete direct import handoffs

The direct surface is 3 HTGeometry consumers and 25 RHTower consumers through 30 import
statements. Only `PrimeArchHankelDeterminantCriterion` directly reaches an RH equivalence.

| Handoff class | Exact direct consumers |
|---|---|
| HTGeometry reconstruction/energy | `BipolarGramDriftAnomaly`; `ContinuousCofiniteRealHilbertReconstruction`; `PointedCollisionIncidenceLinearBridge` |
| RHTower reconstruction/freeness | `GammaShiftDirichletLSeriesArithmeticHilbertReconstruction`; `GammaShiftZetaJetArithmeticHilbertReconstruction`; `PrimeArchHankelDeterminantCriterion`; `XiJetFreeness`; `XiMobiusContinuousApertureSzegoMetric`; `XiTransverseValuationCanonicalReconstruction` |
| Hedenmalm/theta low-block geometry | `HedenmalmCenterMixedCorrelationAngle`; `HedenmalmCenterMixedFourthJetCusp`; `HedenmalmCenterMixedFourthJetCuspClosure`; `HedenmalmCenterMixedLocalThreePoint`; `HedenmalmCenterMixedRaywiseCoalescedCone`; `HedenmalmCenterMixedThreePoint`; `HedenmalmCenterMixedUniformCoalescedSquare`; `SquaredXiThreePointOrbitPositivity`; `ThetaCuspFullReflectionFourthTuran`; `ThetaCuspReflectedRiccatiAngle` |
| Gaussian curvature | `GaussianMetricHermiteStableRankFractureUniversalityLaw`; `HermiteEvenGaussianMetricCurvature`; `XiTransverseValuationGaussianCurvatureHilbertPhase`; `XiTransverseValuationGaussianCurvatureSignDuality`; `XiTransverseValuationGaussianRadicalConnector` |
| Fock/Plücker/phase | `GammaSewnFourRatePluckerConnector`; `HermiteEvenSlaterPluckerConnector`; `UniversalPhaseCoherenceEntropy` |
| Rigging no-go | `ArithmeticSchurExactNormRiggingNoGo` |

### HilbertMetric-facing downstream boundaries

**Internal HilbertMetric mathematics:**

1. affine-dimension-three Gaussian curvature boundary;
2. arbitrary-rank Gaussian curvature classification.

**RHTower literal-source cores using HilbertMetric infrastructure:**

3. all-order prime–arch Hankel reconstruction;
4. all-order Hedenmalm positivity beyond closed low blocks;
5. source-specific CCR/Fock realization with a decisive sign;
6. source filling/rank/phase estimates.

**Category and interface boundaries:**

7. a viable post-scalar rigging category;
8. sufficiency, not merely necessity, of matching characters.

## 5. Role of HTGeometry

HTGeometry supplies rigidity, faithful encodings, source decompositions, exact no-gos,
moment determinacy, Bohr recurrence/Torelli machinery, and the new Julia positive-definite
source.

### Material HT-enabled routes

- first-clock Bohr model and recurrence: Route A;
- compact moment/Thorin determinacy: Route P;
- Julia diagonal/rank-one obstruction: retired Route J;
- Euler-tail faithfulness and source tomography feeding prime/Gamma programs;
- prime KMS and orientation obstruction;
- source-specific Pick obstruction;
- moment and reporter guardrails preventing false source identifications.

### Upstream but not yet RH-connected HT programs

- Gamma differential hypertranscendence;
- reflected-digamma orientation;
- weighted Cauchy-jet smoothness and compact-patch finite-probe transversality, now lifted
  to nonlinear exponential Herglotz charts for arbitrary base measures;
- generic transported-parent energy barriers for unitary dynamics;
- conversion of the now-proved literal-zeta Gamma-field nonrelation into divisor or
  zero-location information;
- Stanley–Reisner/boundary-wedge dimension;
- generic monodromy rigidity;
- transitive transposition generation of the full symmetric group and the exact critical-horizon
  radical boundary: multiplicity at most four occurs only for the five depth pairs with one side
  equal to one,
  while every two-sided depth pair has a nonsolvable symmetric state group;
- uniqueness of Gamma-jet asymptotic data and residues, algebraic independence of every finite
  normalized squared-jet coefficient family, and cancellation of origin-invertible common factors
  from truncated tangent relations;
- maximal-stabilizer fixed-field primitivity and the exact recurrence showing reciprocal power-
  series coefficients remain in every subfield containing the original coefficients;
- continuous-functional-calculus norm bounds converting uniform spectral-symbol smallness into
  operator-norm convergence;
- Lindelöf exponent campaign.

These are not counted as current RH proof chains because no exact source-to-RH handoff is
present.

The literal zeta specialization is closed only for the exact Gamma-jet normal form stated
in `ZetaGammaFieldHypertranscendence.lean`: its denominator, dominant-monomial,
noncancellation, and differential-monomial hypotheses must not be erased. Controlled
digamma quotient valuations and centered coefficient algebraic independence are also now
proved, but neither has an RH handoff.

Dirichlet exponents are now identified exactly as Bohr-hull frequencies under uniform
Dirichlet approximation, closing the exponent-to-spectrum link in the Gamma-field
nonrelation chain. The shift/elimination assembly is now closed at germ level. Rational
germs intertwine rational shift with germ translation, flatness is shift-stable, and each
actual digamma-jet germ satisfies the exact shift-plus-rational-pole law. Polynomial
evaluation into the germ ring is injective: no nonzero differential polynomial in the
digamma jets over `ℂ(s)` is flat on even one vertical line. Universal-to-generic centering,
coefficient-substitution injectivity, and algebraic independence of centered generic
coefficients are proved. The centered coefficient field is a rational function field in
`d-1` independent variables; the associated radical polynomial is irreducible, its root has
the exact expected extension degree, and full symmetric monodromy of the centered equation
survives the even radical base change and every positive odd radical base change; the same
odd-degree law is proved for the uncentered generic polynomial. Every higher digamma
derivative also has its exact vertical leading constant after the natural power
normalization, so normalized jet monomials have explicit nonzero limiting data. Gamma is
transcendental over each finite digamma-jet field in the precise germ-polynomial sense: a
finite polynomial in the Gamma germ with digamma-jet polynomial coefficients vanishes only
coefficientwise. No Xi-source spectral polynomial or analytic handoff exists. The
upper-half-plane germ ring makes every nonzero rational germ a unit, makes flat germs a
rational module, and excludes nonzero rational flat germs.

### Highest-value HT-specific missing inputs

1. first-clock lower floor or Bohr model;
2. completed prime–Gamma sign combining prime and archimedean terms;
3. a source-defined principal-relative Julia current with orientation proved before positive
   good/bad projection;
4. non-diagonal KMS/inter-scale inequality;
5. contractive or variation-diminishing Möbius inversion;
6. literal compact Thorin representation;
7. honest Xi-linked indeterminate Hamburger family;
8. completed Euler cyclic reader with infinite-index Krein packaging;
9. convergence and outer factor for finite prime-clock inner factors;
10. a theorem converting Dirichlet/Gamma nonrelation into zero-location information;
11. actual two-variable HT/SR realization;
12. literal source-specific centered-jet instantiation and an RH-facing handoff from the
    now-proved generic compact-patch transversality;
13. Lindelöf second-spacing plus across-class cancellation.

## 6. Dead routes: exhaustive mechanism map

A route is retired only at the quantifier level proved or paper-falsified. Each entry
therefore lists the surviving positive theorem.

### 6.1 Universal finite selectors and local readers

**Dead.**

- finite rank-one selectors;
- finite seam jets and fixed local derivative order;
- finite-dimensional linear reporters;
- finite-codimension landscapes;
- finite reciprocal moments and finite polynomial degree tests;
- finite divisor prefixes;
- least-prime or any fixed finite-prime localization for growing-order squared-Xi
  reverse-Bessel radial jets;
- scalar orbit quotients and unweighted invariant `ℓ²` lifts;
- invariant-fibre “deciders” that merely restate the target.

**Reason.** Explicit no-free-lunch, blindness, completion, gauge, and tail-insertion
theorems preserve all finite observations while changing the unresolved divisor datum.

**Survivor.** Exact sharp resolution/codimension bounds, weighted orbit invariants, and
the conclusion that any viable selector must be infinite, divisor-sensitive, and
source-faithful. For the reverse-Bessel mechanism specifically, the normalized polynomial
has an exact positive Gamma-integral representation, is bounded by the cancelling
exponential, and converges to it at every fixed Euler frequency. The limiting fixed-prime
weights are therefore proportional to `Λ(m)/√m` and are nonsummable: viable growing-order
work must locate and control a moving prime window against the completed source before
passing to the order limit.

### 6.2 Universal Gaussian/CCR/Fock signs

**Dead.**

- universal Gaussian bandwidth log-concavity;
- unrestricted finite full-CCR tuples;
- universal quasi-free Fano nonnegativity without filling;
- compressed-annihilator universal positive defect;
- coherent row/column compensation as a universal sign law;
- all finite annihilation-invariant-subspace sign laws;
- pairwise commutativity as an identification of defect with half the mixed-commutator
  square;
- arbitrary commuting, nilpotent, symmetric-graded tuples as a universal sign producer;
- direct Fock-square repair; cubic/triadic source-incomplete replacements.

**Lean-certified falsifiers.** Degree-five ambient-16 Gaussian positive log-curvature;
finite full-CCR nonexistence; explicit two-mode quasi-free margin `-2`.

**Paper-level retirements.** The compressed-annihilator, row/column compensation,
commuting-tuple, and universal finite invariant-subspace mechanisms are paper-level
falsifications or implications unless a separate Lean declaration is cited.

The proposed complete-Bernstein Gaussian scale law is also dead by a symbolic
equilateral-three-point paper falsifier, but no matching Lean declaration was found; its
status is PAPER-FALSIFIED, not formally certified.

**Survivor.** Rank-one strict concavity, intrinsic-dimension power concavity, invariant
block CCR, sharp filling threshold, rank/phase defect classifications, stable higher-rank
fracture, and the paper-level exact row–column decomposition. The strongest formal
quadratic survivor is the complete graph completion: annihilation invariance and the
determinant law `t^(e+m) det(tI + LᵀL)`.

### 6.3 Generic positivity, moment, and Pick arguments

**Dead.**

- “hypertranscendence implies Hankel positivity”;
- coefficient positivity or complete monotonicity alone;
- axis positivity as a substitute for a Hankel cone;
- generic positive/log-concave Schwartz shape as Fourier positivity;
- direct Pick-kernel positivity at a quadratic boundary contact;
- Schur/Nevanlinna collapse after assuming an RH-equivalent singularity statement;
- one-state universal KMS closure;
- Gamma-field asymptotic valuation stopped modulo a vertically flat residual, without
  polynomial-level germ evaluation and shift-stable annihilator assembly.

**Survivor.** Exact counterexamples and boundary-contact signs identify missing literal
source structure; corrected Krein/indefinite kernels remain possible.

### 6.4 Hedenmalm/theta finite-shell mechanisms

**Dead.**

- shellwise sign as the completed sign;
- every fixed finite canonical shell prefix;
- fixed finite endpoint asymptotics;
- order-three positivity as RH closure;
- total-variation domination of the exceptional ground shell at the verified cutoff;
- automatic inward transport from boundary positivity;
- one-particle infinite divisibility of the seam carrier.

**Survivor.** Infinite-tail seam cancellation, global three-point PSD, fourth-jet
positivity, exact higher-shell quadrants, one compact ground defect, and the coupled
completed integral.

### 6.5 Sonin and Suzuki finite completion mechanisms

**Dead.**

- Sonin aperture refinement alone;
- bounded scalar, uniformly bounded operator-family quadratic, fixed-operator, and position-side
  Sonin completions, together with every scalar-additive term eventually below the proved positive
  slope in the typed completed-packet model;
- second-order Koplienko subtraction that deletes required linear terms;
- legacy Suzuki entire compact limit;
- scalar jump/Herglotz identifications with mismatched coordinates;
- finite signed-frequency repairs;
- local differential corrections;
- unrenormalized cofinal Bianchi mass;
- atomwise finite causal splice;
- raw completed-Mellin positive-domain proposals;
- transfer of symmetric Volterra positivity/sign to the complementary phase coordinate
  under the stated reflection hypotheses;
- rank-one, single-mode, or diagonal spectral positivity as control of projective chord:
  every diagonal chord contribution vanishes.

**Survivor.** A source-faithful floor-restoring Sonin contribution exceeding one explicit
positive linear rate frequently, or a semilocal completion outside the typed additive model;
meromorphic Suzuki anti-Pick, Herglotz, full-frequency Ward, and projective/Plücker
structures; self-adjoint relative phase coordinate, complementary parity sector, genuine
spectral-pair orientation, and independent source-germ-weld route.

### 6.6 Möbius/additive cancellation shortcuts

**Dead.**

- fixed-order Gowers savings;
- two-prime positivity by repeated Euler removal;
- ternary slack insertion;
- Lambert ternary lift;
- blockwise LCM/cubical positivity;
- numerical “reciprocal-sum contradiction”.

**Survivor.** Gamma–Hankel off-diagonal bounded-return target, supercritical LCM boundary
localization, and exact positive Liu reciprocal-square gap.

### 6.7 Moving completed-source polynomial parity

**Proposed chain.**

```text
far-right positivity + right-even factorization
→ central source Hankel positivity
→ RH.
```

**Verdict.** PAPER-FALSIFIED. For `P=X`, the second completed moment is positive at the
center, negative at 10, and positive far right, forcing odd-multiplicity crossings and
contradicting even factorization.

**Lean nuance.** Lean proves center positivity and conditionally refutes the factorization
given the negative value at 10; the explicit negative estimate itself is not formalized.

**Survivor.** Four-crossing law and signed crossing structure. Do not erase crossings;
classify them.

### 6.8 Axiomatic and deformation routes

The abstract “positive generalized prime system + Riemann functional equation” lane is
circular-or-false.

**Dead.**

- moving zeros of zeta inside the positive-measure axiom class;
- continuous or nonsummable divisor deformations preserving all axioms;
- intrinsic Landau analysis of the whole source, whose pole at one dominates;
- Hamburger uniqueness as an RH shortcut;
- even/odd Weil splitting as a new lever;
- positive-definiteness tested only in the already zero-free half-plane;
- heat/homotopy flow inside the same domination class.

**Survivor.** Landau deformation rigidity and sharp pole-order budgets classify how a
positive generalized system can deviate. A from-scratch Beurling system remains a
dichotomy about the strength of the axiom class, not a proof route for zeta.

### 6.9 Source algebraicity and representation theatre

**Dead or unsupported.**

- Arakelov integrality without a source producer;
- zero-fed Deninger eigenmodels;
- divisor-preserving dynamics that read the divisor they must control;
- abstract witnesses with degenerate inhabitants;
- scalar gluing, orbit shape, ramification quotient, or connected deck charge as
  orientation;
- function-field, scattering, QECC, Böttcher, observer, and physics analogies without a
  typed arithmetic source functor.
- genuinely unbounded closable scalar-current rigging on a dense domain: every closed
  densely defined real scalar functional has full domain, and on a Banach source every
  closed or closable dense scalar functional extends boundedly and continuously;
- invertible linear intertwiners across a trace/character mismatch: one mismatched element
  excludes every invertible intertwiner.
- complete Hochster derived topology plus Stanley–Reisner differential matroid and embedded
  differential field as an orientation selector: arbitrary finite negative residue surgery
  preserves all three while changing the Herglotz chamber.
- residue-programmed diagonal operators as spectral evidence: the canonical `ℓ²` model realizes
  the Gauss-paired logarithmic Schatten residue and exact depth, and its cutoff family escapes every
  fixed positive Schatten class, but the singular values are defined from the target residue and
  no Xi-source operator or RH connector is produced.

**Survivor.** Exact consequence atlases, bounded continuous scalarization, character
equality as a necessary—but not sufficient—compatibility condition, and an exact
topology–orientation product classification. Live rigging must leave the scalar closable
Hilbert category. These structures become RH routes only after a new source construction.

### 6.10 HTGeometry direct RH-adjacent failures

HTGeometry adds:

- differential-field real-zero nonidentifiability;
- Gamma-hypertranscendence/Hankel-sign independence;
- localized Selberg fixed-ratio kernel failure;
- multiplicity-only bosonic horizon;
- polarized infinite-pair orbit-lift failure;
- Sonin second-order regularization;
- capacity growth from hypertranscendence.
- postcritical reciprocal reading of a pure critical horizon: two states with the same critical
  polynomial have different negative inverse constant-term values, so that postcritical coordinate
  is not determined by critical data alone.

Their positive survivors are, respectively: divisor-sensitive gauge classification;
source-specific sign necessity; sharp flat inverse; multiplicity classification; weighted
invariants; exact residual correction; and clock-dilation norm rigidity.

Fifteen additional adjacent physics/algebra mechanisms have no exact RH endpoint:

- `actuality-factorization-interchange-law`;
- `albert-hessian-as-rank-six-event`;
- `autogenic-time-law-conjecture`;
- `clock-geometry-conservation-forces-einstein-dynamics`;
- `finite-cross-law-interference-without-containing-theory`;
- `fixed-carrier-quadratic-variation-as-gravity`;
- `gamma-digamma-mixed-jet-matroid-universality-law`;
- `higgs-tangent-universal-soldering-topology-law`;
- `noncommutative-holonomy-word-growth-differential-innovation`;
- `operational-history-reconstruction-conjecture`;
- `polarized-framed-derived-source-character-principle`;
- `projective-source-directions-are-color`;
- `ratfunc-cyclic-fixed-field-universality-law`;
- `source-reporter-counts-are-particle-indices`;
- `universal-bare-source-effectivity-reconstruction`.

They remain retired and are excluded from the active RH map until an exact source handoff
exists.

### 6.11 Named RHTower no-go modules and exact survivors

| Module family | Retired mechanism | Strongest survivor |
|---|---|---|
| `EdgeScaleNoGo` | sub-resolution edge selector | sharp phase resolution `π/ρ₀` |
| `EndpointNoGo` | fixed deck class determines endpoint sign | all four sign pairs occur |
| `JointReadingNoGo` | a joint scalar reading selects the branch | exact `C₂×C₂` orbit obstruction |
| `LandauShadowNoGo` | global orientation from the Landau shadow | parity localizes the fixed locus |
| `PinnedAffineWeldBoundaryNoGo` | raw pinned affine source selects a weld | nonzero Fitting class survives, but raw source activates everywhere |
| `PrimeDivisorAtomsNoGo` | individual prime-factor atoms detect the divisor | prime atoms are analytic units |
| `SeamArchimedeanNoGo` | seam support alone transfers archimedean orientation | exact support/sampling quotient separation |
| `ShortWindowNoGo` and `ShortWindowNoGoGeneral` | short local windows select the global phase | local/spread-cone obstruction |
| `SpurNoGo` | one-pair preservation under the spur construction | sharp geometric spur law |
| `WeldGermOrientationNoGo` | scalar or vector germ reader recovers orientation | symplectic area survives and requires at least two arithmetic directions |
| `WindowSymmetryNoGo` | a larger hidden window stabilizer supplies phase | stabilizer is exactly identity/mirror |

### 6.12 Additional structural retirements

Current corpus also retires the following mechanisms at their exact stated scope:

- polynomial surgery that leaves the Dirichlet-series class;
- scalar gluing that records orbit shape but not orientation;
- ramification data descending only to the orbit quotient;
- positive weld metrics attempting to recover Krein signature by congruence;
- conservation of connected deck charge as a zero selector;
- rational coefficient charge, which disappears although integral charge survives;
- constant sources, which collapse to scalar sums;
- positive prime-rate blocks, which are mutually congruent;
- weld/Hankel finite-block combinations required to be simultaneously positive, finite,
  and source-faithful;
- finite repaired frequency packets, whose infinite replacement demands the missing
  admissibility condition;
- zero-frequency reservoirs that are target equivalent or collapse to the `dx/x`
  boundary;
- boundary-Weyl, Stieltjes, contractivity, and finite-KMS atlases used without an
  independent source producer;
- generic Julia “coherent capacity” based only on Gram/Cauchy–Schwarz rather than the
  literal equilibrium source.

## 7. Disproof frontier

No unconditional disproof is present. The corpus nevertheless has exact witness-producing
interfaces.

### Direct witness

```text
produce a nontrivial zeta/Xi zero ρ with Re(ρ) ≠ 1/2
→ ¬RH.
```

### Equivalent finite or typed witnesses

| Certificate class | Representative exact interface | Classification |
|---|---|---|
| Completed-flux/Laguerre failure | `completedFluxTaylorCoeff_two_line_re_pos_not_RH` | typed negative certificate |
| Negative completed source jet | `not_riemannHypothesis_of_completedSourceJet_neg` | typed source certificate |
| Prime continuation nonanalyticity | `not_riemannHypothesis_iff_primeContinuationNonanalyticPhaseUniversalCertificate` | exact equivalent certificate |
| Positive Ward endpoint index | `xiEndpointWeightedWardIndex_pos_iff_not_rh` | exact equivalent certificate |
| Nonzero SEM Fitting charge | `not_riemannHypothesis_iff_exists_semHoleFittingCharge_ne_zero` | exact equivalent certificate |
| Heat-Hankel negativity | negative heat form, Turán defect, or trace determinant | finite analytic certificate |
| Shifted-reciprocal negativity | negative reciprocal Hankel quadratic | finite analytic certificate |
| Rectangular/first-clock divergence | cofinal negative rectangular floor or first-clock failure | source-asymptotic certificate |
| Bernstein/source-sector failure | persistent negative mass or sector violation | source-asymptotic certificate |
| Right-half divisor/ladder | nonempty right-half Xi copy and sharp ladder failure | divisor-fed mirror |
| Hurwitz orientation/modulus slope | positive orientation energy or nonzero slope defect | divisor-fed mirror |

### Closest source-level disproof route — growing-order squared-Xi radial jets

For each order `n` and radius `w>0`, the completed source jet `Q_n(w)` has an exact
reverse-Bessel split

```text
Q_n(w) = rational–Gamma contribution
         - positive von-Mangoldt reverse-Bessel contribution.
```

One strict negative value implies `¬RH`. Orders through eighteen are unconditionally
strictly positive, so any witness has `n≥19`. At growing order, normalized reverse-Bessel
weights cancel Euler damping at each fixed prime and converge to nonsummable
`Λ(m)/√m` weights. Least-prime and every fixed finite-prime proof are therefore dead.
The open core is a cancellation-preserving moving-prime-window comparison against the
regularized completed Gamma/polar source, strong enough to make one `Q_n(w)` negative.
Neither corpus nor located literature supplies that comparison.

Every current theorem either derives these from assumed `¬RH` or concludes `¬RH` from
an unproduced certificate. Thus the disproof open core is a concrete certified negative
witness, not a missing logical connector.

## 8. Research hypotheses that would create a leap

The following questions remain unanswered by both formal corpus and current primary
literature. They are stated at source level, before specialization to Xi zeros.

### Tier 1 — shortest RH chains

1. **First-clock lower-floor theorem.** Is the literal published first-clock source
   eventually bounded below?
2. **First-clock Bohr theorem.** Does its scaled source admit a continuous
   Bohr-almost-periodic asymptote?
3. **Fixed-width Weil theorem.** Can one fixed rectangular logarithmic family be bounded
   below from prime–Gamma source alone?
4. **Grouped Mangoldt transport theorem.** Can grouped apex/flank log-Haar cells cross
   every turning seam at capacity one while paying the fixed boundary charge?
5. **Critical Möbius theorem.** Can the actual Gamma–Hankel off-diagonal covariance return
   to a bounded upper region cofinally near the critical exponent?
6. **Hedenmalm completion theorem.** Is the completed center-mixed Fourier current
   nonnegative in the interior high-frequency corner?
7. **Prime–arch high-frequency ceiling.** Can literal source supply any finite uniform
   upper bound above frequency four?

### Tier 2 — source-to-operator or source-to-form construction

8. A source-faithful Sonin completion satisfying the floor and exceeding the proved positive
   linear rate frequently, or a proof that the arithmetic completion lies outside the typed
   scalar-additive model, followed by the literal all-prime source handoff.
9. Suzuki source coefficient monotonicity, chord-mass gap, full jump Pick kernel, or a
    source identification of the forced negative-light Gram channel with the rectangular
    Ward residual.
10. Relative-Volterra phase Euler-defect source-germ weld.
11. Source-built all-degree prime–arch Hankel PSD/reconstruction.
12. Source-built self-adjoint quadratic-scale operator with Xi spectrum inclusion.
13. Deninger relevant-complex comparison, nuclear estimate, Hodge transport, and kernel
    vanishing.
14. Uniform source-domain Hedenmalm prime-normal sub-log-square estimate.
15. Joint infinite-index Gamma–Jacobi Krein reader and forced outer factor.
16. Restricted-Weil/prolate ground-state comparison and rigorous finite-to-Xi convergence.
17. Literal compact Thorin/Markov carrier for the completed seam.
18. A continuation mechanism carrying the proved finite-prime/Euler-boundary Plücker
    normal-cone diagonal from `Re(s) > 1` to critical Möbius data.

### Tier 3 — new structure that could unlock Tier 1 or 2

19. Non-diagonal inter-scale KMS inequality neutralizing persistent bad layers.
20. Contractive or variation-diminishing Möbius inversion of Gamma occupation.
21. Source-stable OPUC terminal identity.
22. Burnol co-Poisson scalar Berezin sign or parity-block flatness.
23. Source determinant-line no-first-crossing theorem retaining negative index.
24. All-prime Calkin collinearity or two-particle Sonin subroot estimate.
25. Affine-dimension-three and arbitrary-rank Gaussian curvature classification.
26. Viable vector/operator-valued or nonclosable post-scalar rigging.
27. Actual two-variable HT/SR realization with rank-one period group.
28. A theorem converting Dirichlet/Gamma differential nonrelation into zero-location
    information.
29. Lindelöf second-spacing estimate plus across-class cancellation, followed by an exact
    typed RH handoff.
30. A cancellation-preserving moving-prime-window asymptotic for growing reverse-Bessel
    squared-Xi radial jets, strong enough to orient one order `n≥19` against the completed
    Gamma/polar source.
31. A uniform positivity theorem for consecutive Xi-coefficient Toeplitz minors in the
    complementary region `k < 10^18 r^3`, especially `k = O(r)`, or a theorem reducing every
    remaining minor to the proved cubic tail wedge without numerical certification.

### Disproof leap

32. A rigorously certified off-line zero or any equivalent negative finite certificate.

## 9. Literature reconciliation

Current primary literature distinguishes new finite or structural advances from proof
completion.

- Connes and van Suijlekom prove real zeros for the Fourier transform of an isolated
  simple even ground state of a lower-bounded convolution operator. This validates a
  spectral mechanism but does not identify a convergent Xi ground state:
  [Quadratic Forms, Real Zeros and Echoes of the Spectral Action](https://arxiv.org/abs/2511.23257).
- Connes's survey obtains real finite approximants and explicitly leaves finite-to-infinite
  Euler-product convergence as the prospective proof step:
  [The Riemann Hypothesis: Past, Present and a Letter Through Time](https://arxiv.org/abs/2602.04022).
- Connes–Consani–Moscovici report striking finite spectral convergence; they state that a
  rigorous proof of convergence would establish RH:
  [Zeta Spectral Triples](https://arxiv.org/abs/2511.22755).
- Hedenmalm constructs the theta boundary-value eigenproblem and a formal self-adjoint
  pair. The source-positive Hilbert realization remains open:
  [Spectral interpretation of Riemann zeta zeros](https://arxiv.org/abs/2606.17494).
- Suzuki constructs finite self-adjoint extensions and conjectures the limiting
  self-adjoint operator. The infinite/full-frequency identification remains open:
  [Weil's quadratic form via the screw function](https://arxiv.org/abs/2606.09096).
- The July 2026 finite-element realization of Suzuki's operator proves an archimedean
  Mellin head coefficient but classifies its spectral, ground-state, characteristic-zero,
  and critical-line observations as numerical and universal rather than new arithmetic;
  it supplies no unconditional finite-to-Xi limit:
  [A Numerical Realization of Suzuki's Weil-Quadratic-Form Operator](https://arxiv.org/abs/2607.24830).
- The finite Guinand–Weil dictionary gives exact finite zero sums and an explicit
  archimedean tail budget, while expressly making no RH claim:
  [A finite Guinand-Weil dictionary and archimedean tail order](https://arxiv.org/abs/2607.02828).
- Liflandsky's discrete Möbius Laplace bound implies RH, while the converse needs extra
  zero hypotheses. The critical bound remains an input:
  [Explicit formula for the discrete Laplace transform of the Möbius function](https://arxiv.org/abs/2607.09797).
- Verjovsky proves that subpolynomial shrinking-arc local moments of Möbius Fourier
  polynomials, at arbitrarily high finite orders, are equivalent to RH and gives an
  unconditional moment-to-point inequality recovering `M(N)`. No local-moment bound is
  proved, so the Route E source estimate is unchanged:
  [Local Moments of Möbius Fourier Polynomials and the Riemann Hypothesis](https://arxiv.org/abs/2607.25002).
- The theta-infinity paper proves zero-free consequences conditional on arbitrary-length
  mollified moment bounds; it does not prove those bounds:
  [The θ=∞ Conjecture and RH for Automorphic L-functions](https://arxiv.org/abs/2605.24363).
- The 2026 Hardy-space and Colombeau papers give closure/generalized-function criteria,
  not the missing source estimates:
  [Hardy space approximation](https://arxiv.org/abs/2606.16097) and
  [Colombeau–Beurling criterion](https://arxiv.org/abs/2606.22562).
- Yang proves RH-implied zero Friedrichs angles for localized Nyman–Beurling subspace pairs and
  unconditional strict subspace-sum inclusions. These sharpen the Hilbert geometry but do not
  provide the missing approximation estimate:
  [A Friedrichs angle between the Nyman–Beurling spaces and the Riemann hypothesis](https://doi.org/10.1016/j.jmaa.2026.130494).
- Michalowski proves consecutive Xi-coefficient Toeplitz-minor positivity in the explicit
  uniform tail wedge `k ≥ 10^18 r^3`; the paper itself leaves `k < 10^18 r^3`, particularly
  `k = O(r)`, open and makes no RH claim. Its rigorous proof uses directed-rounding
  certificates, precluding import under the no-computation rule:
  [An explicit uniform cubic wedge for consecutive Toeplitz minors of the Riemann ξ-coefficients](https://arxiv.org/abs/2607.16795).
- Gaber's July preprint is not a valid SOTA input. Its claimed RH-conditional `O(x)` error
  for the summatory Euler totient at `ℓ=1` contradicts Montgomery's unconditional
  `Ω±(x sqrt(log log x))` theorem, so no result from it is imported:
  [Euler's ℓ-totients and Riemann hypothesis](https://arxiv.org/abs/2607.26114),
  [Fluctuations in the mean of Euler's phi function](https://doi.org/10.1007/BF02837826).
- The Salem note is explicitly an equivalence:
  [A new equivalence by means of the Salem integral equation](https://arxiv.org/abs/2604.15396).
- Polson's revised Thorin paper establishes the probabilistic/Hadamard framework, not a
  source-constructed critical-seam carrier:
  [Riemann, Thorin, van Dantzig Pairs, Wald Couples and Hadamard Factorisation](https://arxiv.org/abs/1804.10043).

The cited primary sources close no Tier-1 or Tier-2 open core above.

## 10. Priority and research policy

### Highest expected leverage

1. first-clock lower floor / Bohr asymptote;
2. Hedenmalm completed high-frequency current;
3. Möbius Gamma–Hankel bounded returns;
4. fixed-width rectangular Weil floor;
5. any finite prime–arch high-frequency ceiling;
6. Sonin source-faithful floor restoration with the proved positive-linear excursions and literal
   all-prime handoff;
7. Suzuki source-selected full jump kernel or relative-Volterra source-germ weld.

These routes begin with literal source and have short, formally closed tails to RH.

### Valuable but longer-horizon construction programs

- Deninger/Hodge;
- quadratic spectral realization;
- Gamma–Jacobi reader;
- Connes/prolate convergence;
- compact Thorin/Markov carrier.

### Do not spend cycles on

- new names for RH-equivalent divisor coordinates;
- finite local selectors;
- shellwise or finite-prefix positivity as completed positivity;
- abstract zero-fed spectral models;
- generic HT, positivity, log-concavity, or moment arguments without literal source;
- legacy Suzuki entire-limit, Sonin scalar/position-side completion, or moving-polynomial
  even factorization;
- lexical HT/RH crossmatches without exact imports and identifier use.

## 11. Final frontier statement

The corpus has already solved most connector problems. Its remaining difficulty is not a
shortage of RH criteria. It is source acquisition.

Every leading route has the same abstract shape:

```text
literal prime/theta/Möbius/clock source
→ one global sign, recurrence, rate, or operator-realization theorem  [OPEN]
→ a fully formal zero-exclusion connector                              [PROVED]
→ RiemannHypothesis.                                                   [NOT PROVED]
```

The routes differ in the missing theorem:

- lower floor or Bohr asymptote for the first clock;
- fixed-width lower floor for rectangular Weil;
- all-order completed positivity for Hedenmalm/prime–arch;
- critical cancellation for Möbius;
- positive-linear-excursion floor restoration and literal all-prime handoff for Sonin;
- source-selected full-frequency Pick/Hermite–Biehler structure for Suzuki;
- relative-Volterra phase source-germ weld;
- off-diagonal core-current control for Xi Taylor;
- source-defined principal-relative Julia current and pre-projection orientation;
- source-built operator and spectrum inclusion for spectral/Deninger programs.

The disproof side is equally exact: one certified off-line zero or equivalent negative
finite witness would suffice, but the corpus produces none.

Therefore the honest current conclusion is:

> **RH is neither proved nor disproved. The formal frontier is a finite quotient of
> source-level open cores, led by first-clock, completed positivity, critical Möbius,
> Sonin/Suzuki and Xi-current problems. Retired Route J leaves only a principal-relative
> Julia representation change, not a coherent-energy-budget problem. All other
> RH-facing declarations are connectors, mirrors, infrastructure, or retired
> mechanisms unless and until they supply a new literal-source theorem.**

## Appendix A. Principal Lean anchors

- `RHTower/RiemannTower.lean`
- `RHTower/RHCharacterizations.lean`
- `RHTower/CCMFirstClockTailLowerBoundCompleteness.lean`
- `RHTower/CCMFirstClockAsymptoticBohrLaw.lean`
- `RHTower/CCMSingleClockCompleteSourceDivisorTomography.lean`
- `RHTower/CCMRectangularWeilCompleteness.lean`
- `RHTower/SuzukiRectangularPositiveArchLagCompletion.lean`
- `RHTower/SuzukiMangoldtLogHaarTransport.lean`
- `RHTower/SuzukiMangoldtApexLock.lean`
- `RHTower/SuzukiBicausalNoFreeSplice.lean`
- `RHTower/XiWeilPositivityCriterion.lean`
- `RHTower/HedenmalmCenterMixedOrientationBoundary.lean`
- `RHTower/PrimeArchThetaHankelDegreeTail.lean`
- `RHTower/PrimeArchHankelDeterminantCriterion.lean`
- `RHTower/PrimeArchMomentRepresentationRigidity.lean`
- `RHTower/MobiusLaplaceMellinPlancherelBridge.lean`
- `RHTower/MobiusLaplaceGammaHankelWall.lean`
- `RHTower/MobiusPlueckerNormalConeDiagonalLift.lean`
- `RHTower/SoninCoupledPrimeArchGramTransfer.lean`
- `RHTower/SoninDilatedBandTransport.lean`
- `RHTower/SoninShellCutBandPacketTerms.lean`
- `RHTower/SoninShellCutBandBound.lean`
- `RHTower/SoninShellCutBandTotalBound.lean`
- `RHTower/SoninShellCutSharpBandBound.lean`
- `RHTower/SoninShellCutSharpSchedule.lean`
- `RHTower/SoninShellCutSlackClosedForm.lean`
- `RHTower/SoninShellCutHighSlackClosedForm.lean`
- `RHTower/SoninRefTailWeightedVanishing.lean`
- `RHTower/SoninShellCutEnergySchedule.lean`
- `RHTower/SoninShellCutScheduleExists.lean`
- `RHTower/SoninIdealErrorEnergyConstant.lean`
- `RHTower/SoninCouplingEnergyUnbounded.lean`
- `RHTower/SoninCouplingEnergyLinear.lean`
- `RHTower/SoninScheduleSequence.lean`
- `RHTower/SoninLogCappedCompletionFails.lean`
- `RHTower/SoninSublinearCompletionFails.lean`
- `RHTower/SoninCompletionMustGrowLinearly.lean`
- `RHTower/SoninBoundedSequenceCompletionFails.lean`
- `RHTower/SoninBoundedFamilyCompletionFails.lean`
- `RHTower/SoninLinearThresholdCompletionFails.lean`
- `RHTower/SoninChannelHeightSplit.lean`
- `RHTower/SoninShellTailWeightedSum.lean`
- `RHTower/SoninChannelHeightUniform.lean`
- `RHTower/SoninPacketChannelHeightBound.lean`
- `RHTower/SoninPacketChannelCombinedForm.lean`
- `RHTower/SoninChannelCutIndex.lean`
- `RHTower/SoninPacketHighTailPolynomial.lean`
- `RHTower/SoninSublinearChannelFamily.lean`
- `RHTower/SoninChannelMovingThreshold.lean`
- `RHTower/SoninFourierChannelFamilyClosed.lean`
- `RHTower/QuantitativeNymanBeurling.lean`
- `RHTower/GroskinArchimedeanTailOrder.lean`
- `RHTower/SuzukiFiniteApertureHermiteBiehler.lean`
- `RHTower/SuzukiVolterraCartesianPhaseDefect.lean`
- `RHTower/SuzukiAffineSecantSpectralSum.lean`
- `RHTower/SuzukiWallFieldAntidiagonalGramLift.lean`
- `RHTower/SuzukiWallFieldLightConeKernelCompletion.lean`
- `RHTower/SuzukiApertureDressedWallLightCompletion.lean`
- `RHTower/SuzukiValuationDepthLightCoercivity.lean`
- `RHTower/SuzukiCoherentCausalDepthFusion.lean`
- `RHTower/SuzukiRectangularWallGramGate.lean`
- `RHTower/SuzukiCoherentResponseGainNoGo.lean`
- `RHTower/SuzukiCoherentSharpSourceDomainNoGo.lean`
- `RHTower/SuzukiFiniteMorseResolventOperatorLift.lean`
- `RHTower/StrictHermiteBiehlerGivesRH.lean`
- `RHTower/XiCTaylorThetaTailCoreCurrentCapstone.lean`
- `RHTower/CCMSharpPrimeWindowSubpowerGate.lean`
- `RHTower/QuadraticScaleSpectralRH.lean`
- `RHTower/DeningerHilbertKummer.lean`
- `RHTower/DeningerShift.lean`
- `RHTower/DeningerHaarAverage.lean`
- `RHTower/DeningerKronecker.lean`
- `RHTower/DeningerResidualLeaves.lean`
- `RHTower/DeningerWeylCriterion.lean`
- `RHTower/DeningerKroneckerDense.lean`
- `RHTower/DeningerAffineLeafFlow.lean`
- `RHTower/DeningerAffineLeafSymmetry.lean`
- `RHTower/DeningerHarmonicMode.lean`
- `RHTower/DeningerHarmonicCup.lean`
- `RHTower/DeningerHarmonicUniqueness.lean`
- `RHTower/DeningerCylinderModes.lean`
- `RHTower/DeningerTorusCompleteness.lean`
- `RHTower/DeningerParametricTorus.lean`
- `RHTower/DeningerKroneckerTranspose.lean`
- `RHTower/DeningerModeDescent.lean`
- `RHTower/DeningerSymbolTorsion.lean`
- `RHTower/DeningerPacketAverage.lean`
- `RHTower/DeningerClopenPartition.lean`
- `RHTower/DeningerTransversePartition.lean`
- `RHTower/DeningerBoxRefinement.lean`
- `RHTower/DeningerPacketFine.lean`
- `RHTower/DeningerPacketFineSmooth.lean`
- `RHTower/DeningerMappingTorus.lean`
- `RHTower/DeningerPacketUnits.lean`
- `RHTower/HedenmalmPrimeNormalWickBoundaryEnergy.lean`
- `RHTower/ThetaCuspCalibratedPowerReciprocalMomentLaw.lean`
- `RHTower/CCMFirstClockJuliaEquilibriumGram.lean`
- `RHTower/CCMFirstClockJuliaTwoPacketCapacity.lean`
- `RHTower/CCMFirstClockJuliaCoherentEnergyDiagonalFloor.lean`
- `RHTower/GaussPairedDiagonalResidue.lean`
- `RHTower/PrimeArchVerifiedHeightAccretivity.lean`
- `RHTower/XiPrimeSeamPairAsymptotics.lean`
- `RHTower/ReverseBesselFixedFrequencyBlindness.lean`
- `RHTower/ReverseBesselPositiveIntegral.lean`
- `RHTower/RiemannHypothesisSOTA2026.lean`
- `HTGeometry/SummableSpectrumScrewAlmostPeriodic.lean`
- `HTGeometry/SummableSpectrumScrewBohrCoefficients.lean`
- `HTGeometry/SummableSpectrumScrewRecurrence.lean`
- `HTGeometry/FiniteSpectralRecurrenceFrequencyLaw.lean`
- `HTGeometry/BohrProductUniformLimit.lean`
- `HTGeometry/BohrFrequencyModuleProduct.lean`
- `HTGeometry/CarriedConclusion.lean`
- `HTGeometry/PositiveDefinitePacketCauchy.lean`
- `HTGeometry/NonnegativeKernelDiagonalCapacity.lean`
- `HTGeometry/JuliaDefectSpectralEquilibrium.lean`
- `HTGeometry/JuliaDefectEquilibriumPositiveDefinite.lean`
- `HTGeometry/CharacteristicDefectGramCapacity.lean`
- `HTGeometry/ZetaGammaFieldHypertranscendence.lean`
- `HTGeometry/DirichletBohrSpectrum.lean`
- `HTGeometry/VerticalFlatness.lean`
- `HTGeometry/HalfPlaneGermShift.lean`
- `HTGeometry/DigammaJetGerm.lean`
- `HTGeometry/VerticalFlatGermElimination.lean`
- `HTGeometry/GammaTranscendentalOverDigamma.lean`
- `HTGeometry/PolygammaLeadingAsymptotic.lean`
- `HTGeometry/DigammaJetLeadingConstants.lean`
- `HTGeometry/GammaJetDatumUniqueness.lean`
- `HTGeometry/TranspositionTransitive.lean`
- `HTGeometry/CriticalHorizonRadicalRegime.lean`
- `HTGeometry/SquaredJetCoefficientIndependence.lean`
- `HTGeometry/HorizonTruncationCancel.lean`
- `HTGeometry/CoatomFixedField.lean`
- `HTGeometry/LogMaxSublinear.lean`
- `HTGeometry/ReciprocalCoefficientField.lean`
- `HTGeometry/CenteredCoeffFieldRational.lean`
- `HTGeometry/CenteredFullMonodromy.lean`
- `HTGeometry/CenteredFullMonodromyOdd.lean`
- `HTGeometry/GenericFullMonodromyOdd.lean`
- `HTGeometry/HerglotzJetMapSmoothness.lean`
- `HTGeometry/WeightedCauchyTranslatedExpandedEvaluationCompactPatch.lean`
- `HTGeometry/HerglotzTranslatedExpandedEvaluationCompactPatch.lean`
- `HTGeometry/HypertranscendentalHochsterSourceCoherenceDuality.lean`
- `HTGeometry/AnalyticEulerTailExactFaithfulnessUniversalityLaw.lean`
- `HTGeometry/PrimeOrientationCompletedRingSignNoGo.lean`
- `HTGeometry/QuadraticContactPickObstruction.lean`
- `HTGeometry/FiniteReporterBlindness.lean`
- `HTGeometry/OrbitQuotientLiftNoGo.lean`
- `HilbertMetric/PrescribedEvaluationReconstruction.lean`
- `HilbertMetric/GaussianMetricStableRankFractureLaw.lean`
- `HilbertMetric/CCRFiniteBlockObstruction.lean`
- `HilbertMetric/ThreePointCorrelationAngle.lean`
- `HilbertMetric/DenseClosedScalarRigidity.lean`
- `HilbertMetric/CharacterIntertwinerObstruction.lean`
- `HilbertMetric/QuadraticGraphFockConnector.lean`
