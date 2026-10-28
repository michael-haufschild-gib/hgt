# Arithmetic index descent

Objective: develop the programme described in `docs/reports/review-2710/astra2.md`, including its
arithmetic producers and transfer theorems. Full success is not established by a README or by
repackaging existing RH criteria.

Owner: `formal/GaloisForLFunctions/ArithmeticIndexDescent/`.
Umbrella: `formal/GaloisForLFunctions/ArithmeticIndexDescent.lean`.
Durable log: `logs/arithmetic-index-descent.log`.

## Mathematical scope

1. Completed-form refinement and signed overlap with actual prime, Gamma and pole terms.
2. Charged near-incidence estimates at the Euler source.
3. Finite-Gram limits and growing arithmetic presentations.
4. Rigidity of Gram equality and shared multi-window resources.
5. Quantitative index–transverse-work comparison.
6. Terminal boundary-to-interior estimates and individual-defect exclusion.
7. Finite-field source calibration.

## Initial questions

Determine which of the following advances are already in the corpus, then pursue missing results:

- A quantitative index–energy inequality for every finite actual Weil Gram, stronger than separate
  RH equivalences and with multiplicities/normalizations explicit.
- Stability of finite negative-index budgets under entrywise limits and pullbacks, including
  singular overlap Grams.
- A source estimate for interacting section spaces beyond the currently proved shrinking spaces.

## Evidence and status

The foundational README is in place. The energy–work modules, source radical/range theorem,
actual section projection, singular inertia calculus and locally bounded source kernel have
passed individual Lean checks with standard endpoint axioms. The closed source threshold and
common finite stratum have passed their direct final audits; the dependency-producing modules
still need direct final audits. The literal residual-index bridge and uniform projection-cost
bound are now checked. Canonical source completion has passed its dependency-producing check;
its source-work transfer has passed its direct final check. Existing local section positivity,
polar gluing, spline index laws, source-work exhaustion and matrix inertia are reused explicitly.

No missing analytic estimate may be introduced as a hypothesis to obtain the desired endpoint.
General structural theorems must expose their conditions and discharge them in actual arithmetic
applications. No numerical experiments or full builds. Lean checks use `lake --old env lean` from
`formal/`, one foreground process at a time. Existing unrelated workspace changes are preserved.

## Completion conditions

Each contribution has a source-defined statement, paper argument, Lean proof, direct final check,
umbrella import and README explanation. The full programme stays open while its producer,
exhaustion, surplus or extinction questions remain unresolved. Every no-go retains its strongest
positive survivor and formalizes it when ready.

## Contributions under development

- `TheIndexIsPaidByTransverseEnergy.lean`: the distinct transverse energy bounds every finite
  smooth Weil Gram's negative index; the pole plane adds one to the corresponding intersection
  positive index. The module has passed its required direct final audit with standard endpoint
  axioms.
- `TheArithmeticSourcePaysTheIndex.lean`: select one multiplicity copy per support point to compare
  distinct and copied energy. Ordered damping/taper limits turn each finite index witness into a
  finite arithmetic source-work witness. Required direct final audit passed with standard endpoint axioms.
- `BoundedSourceWork.lean`: the angular kernel is bounded rowwise by the summable Cauchy height
  weight. Finite off-line support therefore gives finite copied energy; the reverse follows from
  the distinct-energy bound. Required direct final audit passed with standard endpoint axioms.
- `TheWorkAndIndexHaveTheSameFiniteStratum.lean`: the fixed spline integer-log index is uniformly
  bounded iff damped source work is eventually bounded. Both are exactly finite off-line support.
  Direct final check passed; wired into umbrella. This is a finiteness classification, not an extinction theorem.
- `SingularRefinement.lean`: for a mixed block `B=A X`, triangular congruence gives all three
  inertia additivity laws without inverting `A`; the Schur complement is independent of the lift
  `X`. Dependency-producing check passed with standard endpoint axioms; final direct audit remains.
  Actual section range compatibility is proved in the source module. Complement payment remains open.

## Strict energy margin: checked argument

Let `rho=beta+i gamma` be an off-line Xi support. Its horizontal partner `1-conj(rho)` contributes
one to its angular row. The second zero `1-rho` is distinct from that partner because Xi has no
real zeros. Its contribution is

`(2 beta-1)^2 / ((2 beta-1)^2 + (2 gamma)^2) > 0`.

Thus every off-line angular row exceeds one. A nonempty finite right packet together with its
reflected packet has twice as many members, so its global transverse-energy cost strictly exceeds
its cardinality. Extracting a packet of size equal to a positive finite Weil negative index gives
`index < distinct energy <= copied energy`. The ordered-limit consequence that source work eventually exceeds the index
itself has passed its direct final check in `TheSourceWorkHasAClosedQuantumThreshold.lean`.
That module also proves RH iff damped source work is cofinally at most two. Conjugation supplies two right zeros when RH fails, hence a strict global gap above two.
There is no claimed uniform extra margin: the displayed surplus can tend to zero.

The exact strict-energy proof has passed Lean in `TheEnergyStrictlyExceedsTheIndex.lean`.
Its direct final audit has passed with standard endpoint axioms. The central arithmetic upper
estimate, signed-overlap payment, exhaustive descent, signed prime surplus, terminal exclusion and
finite-field realization remain open programme tasks.

## Arithmetic singular range: new source application

The narrow-section floor `W >= L2` implies that a section Gram null vector synthesizes the
zero test. It therefore annihilates all mixed Weil entries against arbitrary ambient tests.
Factoring each mixed functional through the old Gram range and extending it linearly gives
`B=A X` even for redundant section presentations.
`ArithmeticSectionsHaveOnlyPresentationRadicals.lean` has passed its dependency-producing check;
all printed endpoints have standard axioms only. It is wired; its final direct audit remains.
The signed Schur complement remains to be bounded arithmetically.

## Source projection: checked positive survivor

The range theorem gives a unique actual projected section P(g), despite nonunique coefficients.
The projection is linear and idempotent. Its residual satisfies the exact identity
`W(g-Pg,h-Ph)=W(g,h)-W(Pg,Ph)`. The removed energy is nonnegative from the existing
arithmetic square-mass floor; therefore removing a positive section cannot improve a negative
witness. It isolates the signed obstruction rather than paying it. The residual energy also
minimizes over the old span, with excess at least the actual squared L2 error. These statements
passed the dependency-producing check of `ArithmeticSectionProjection.lean`; all four printed
endpoints use only standard axioms. Its final direct audit remains. The actual matrix application
has also passed its dependency-producing check in `TheSectionComplementCarriesAllNegativeSquares.lean`:
complexification is the literal complete Weil Gram, and the actual residual Gram carries exactly
the negative index of the old-section extension. Its direct final audit remains.

## Checked source upper estimate for projection cost

For a fixed actual smooth compact test g and fixed support window [-R,R], the exact source
averaging identity constructs a continuous complete kernel K_g. Compactness gives a finite
constant C(g,R) with |W(p,g)| <= C(g,R) integral|p| for every real test p in that window.
Both pole moments, prime terms and Gamma are retained. Smoothness supplies Gamma integrability.

The source section floor then gives W(P_F g,P_F g) <= 2 R C(g,R)^2 uniformly over all finite
section families F in the window, including redundant families. This is an actual source
upper bound on Schur cost, with window dependence. Uniformity as R and arithmetic
resolution grow remains a separate research question.

## Fixed-window source completion: checked construction

For each actual compact real C2 ambient test g, source averaging gives a continuous complete
kernel K_g. Its bound on a fixed window controls |W(p,g)| by C times L1(p). Combining the
arithmetic section floor and support Cauchy–Schwarz gives a uniform bound for W(P_F g,P_F g)
over every finite section family F in fixed (N,w), with no coefficient conditioning assumption.
`TheSourceKernelIsLocallyBounded.lean` has passed its dependency-producing check with standard
endpoint axioms. `TheProjectionCostIsBoundedOnEachWindow.lean` also passed its first
dependency-producing check, with a standard endpoint axiom list. Both are wired; final direct
audits remain.

Direct the finite subsets of the entire narrow section space by
inclusion. Their actual projection energies increase and are uniformly bounded. The difference
of two nested projections has Weil energy equal to the energy increment and square mass at most
that increment. The finite projections form a Cauchy net in square mass, and every
finite mixed residual Gram converges to a canonical source complement. Polarization of
the limiting energies supplies all mixed entries and a symmetric positive semidefinite bilinear
removal form. The residual annihilates the entire old section space on both sides. Each limiting
negative square is detected at sufficiently large finite refinements. These statements passed
the dependency-producing check of `TheSectionProjectionHasACanonicalLimit.lean`, with standard
endpoint axioms; it is wired and needs its direct final audit. Existing generic Hilbert monotone-projection
convergence and finite-Gram index stability are tools, not new arithmetic results.

This target completes a fixed positive arithmetic source space. It does not establish a bound
uniform under growing N, identify the resulting complement as positive, or exhaust the
fixed-spline integer-log tests. Those remain distinct producer problems.

The checked `TheCompletedSourceComplementIsPaidByWork.lean` transfers the completed finite index
through actual smooth residual witnesses into the strict transverse-energy and ordered finite
source-work bounds. Its direct final check passed with standard endpoint axioms; it is wired.
Exact eventual index equality and sharper compact-support dual-energy estimates are now proved
below. An explicit L2 limit object remains a further construction.

## Source cost and width: current formalization targets

The exact-cell kernel-energy bound has passed its dependency-producing Lean check and is wired.
The fixed-pattern shrinking, retained-reserve and exact-index theorems have passed their direct
final checks and are wired.

- `TheSourceKernelEnergyBoundsTheSchurCost.lean` retains the exact cell union
  `U = union_{1<=n<=N} [log n,log n+w]`. Compact-support Cauchy–Schwarz gives
  `W(p,g)^2 <= integral(p^2) * integral_U |K_g|^2`. For the actual projection,
  `W(p,g)=W(p,p)>=integral(p^2)`, hence finite and completed removal cost at most
  `integral_U |K_g|^2`. The residual is bounded below by `W(g,g)` minus this cost.
  This is an upper estimate from the combined full source kernel, with cancellation retained
  before squaring. All printed endpoint axioms are standard; its direct final audit remains.
  It does not control growth in `N`.
- `ShrinkingCellsRemoveVanishingEnergy.lean` uses `volume(U)<=N*w` and a common kernel bound
  on `[0,log N+1]` to prove completed removal is `O(w)` at fixed `N`. The residual therefore
  returns to the original diagonal as widths shrink. The quantified statement covers the
  entire profile space, independently of presentation dimension. It is not an obstruction to
  a programme that also grows or translates its arithmetic pattern. Direct final check passed;
  all three printed endpoint axiom lists are standard.
- `ThePolePaymentRetainsTheUnusedWidthReserve.lean` keeps the unrounded pole charge
  `w*N*(exp(w)+1)`. At width at most fraction `a` of the full allowance, the full form retains
  `(1-a)/8` of the weighted profile reserve beyond square mass. Positive retained reserve
  requires a reduced width; the full-width source floor alone supplies no such surplus.
  Direct final check passed with standard endpoint axioms; wired and explained in the README.
- `TheCompletedIndexIsReachedAtAFiniteStage.lean` uses actual quadratic order to bound every
  finite residual index by the completed index. Combined with the existing eventual reverse
  comparison, this gives exact eventual equality for each fixed finite probe family. Direct
  final check passed with standard endpoint axioms; wired and explained in the README.

The base index-energy module has now passed its required direct final audit. Remaining final
audits and individual draft checks are tracked in `logs/arithmetic-index-descent-checks.json`.

## Adaptive source extension: established

For fixed narrow `V(N,w)` and any centre `b` outside its exact compact cell union,
the source constructs `delta0>0` such that every smaller new width and every pair
of old/new independently chosen profiles satisfy

`W(p+g,p+g) >= (1-epsilon)*mass(p)+mass(g)`.

Old widths remain fixed. The theorem covers the entire infinite old profile space,
not merely a selected finite basis. `AnAdditionalCellPreservesTheOldSections.lean`
passed its direct final audit79528 with standard axioms and is wired.

The mechanism is fully source-derived:

1. Separation removes all short Gamma cross jumps; the remaining Levy tail is integrable.
2. A common bounded window gives a profile-independent finite prime horizon.
3. Window Cauchy–Schwarz pays both pole moments.
4. The combined bound is `|W(p,g)|<=C*(mass(p)+mass(g))`, with actual
   `C=2R*exp(R)+sum_{2<=n<N} Lambda(n)/sqrt(n)+integral_d^infinity omega`.
5. Rescaling yields `2|W(p,g)|<=epsilon*mass(p)+4(C+1)^2/epsilon*mass(g)`.
6. The inherited single-cell logarithmic gain pays any fixed new charge, uniformly
   under translation. The exact extension retains `W(p,p)` before using the old floor.

`SeparatedSupportsRemoveTheGammaSingularity`, `BoundedWindowsHaveFinitePrimeInteraction`,
`TheSeparatedMixedSourceIsBounded`, `EveryShortCellPaysAnyFixedMassCharge`, and
`AShortNewCellPaysItsOwnInteraction` passed their necessary dependency checks with
standard endpoint axioms and are wired. Their mandatory direct final audits remain.
No new discovery of the inherited single-cell logarithmic gain is claimed.

Stronger inherited tools remain relevant: the actual Gamma boundary operator has
norm at most `2*pi`; `CHMDSharpSpatialCut` supplies uniform full-graph sharp-cut
bounds and exact aperture admission. A vanishing support gap is not itself a Gamma
wall. Cumulative signed assembly and exhaustive approximation remain separate.

## Fixed-width iteration: established

`FixedCellWidthsSupportNestedPositiveSections.lean` passed its direct final audit31715,
with standard axioms for both generic and arithmetic endpoints, and is wired. One
unused simp-argument warning remains; no linter was disabled.

For any strictly increasing centres `b_n`, construct one sequence `0<w_n<=1` such
that every finite prefix of arbitrary independent real compact C² profiles supported
in those cells satisfies `W(sum,sum)>=mass(sum)`. In particular this holds at
`b_n=log(n+1)`, with all previously chosen widths fixed forever.

Canonical envelopes `e_n=min(1,(b_(n+1)-b_n)/2)` give compact old unions excluding
the next centre. Their window and gap determine the source extension threshold
independently of the actual width choices. Choose each actual width below its
envelope, gap and threshold. The decreasing reserve `a_n=1+1/(n+1)` pays every
old-mass loss, and exact disjoint mass addition preserves the prefix floor `a_N`.

This discharges the iteration positivity input rather than assuming it. No lower
bound comparable to local spacing is obtained. No fixed-spline exhaustion follows;
the theorem also works for arbitrary increasing real centres, so its mechanism does
not by itself supply new critical prime cancellation.

## Actual completed projection

The corpus already has the complete CHMD source graph and a literal C² lift.
`testLift_energy`, `testLift_add`, `testLift_sub` identify its signed Markov energy
and linear operations. `weilForm_compactLift` identifies the full Weil diagonal,
poles included, after inverse Doob conversion. The graph norm identity and
Cauchy–Schwarz on its global polar directions give a fixed-window bound
`||testLift(f)||^2 <= W(f,f)+C(R)*mass(f)`. The theta kernel is continuous and
strictly positive, so the weighted source mass is bounded by ordinary mass on
the fixed window. On arithmetic sections, `mass<=W`; hence projection-energy
increments control the actual complete graph norm.

Construct the literal graph limit of the existing finite-section net, identify
its full Weil energy with `sectionCompletionEnergy`, and its polarized pairing
with `sectionCompletionPair`. This is stronger than a square-mass Cauchy claim
and uses no global positivity assumption. The general compact C² CCM admission
and actual aperture norm comparison are also inherited; they can subsequently
identify the same limit in the exact aperture domain. No such new limit theorem
is claimed until formalization is complete.

The graph norm bridge `TheGraphNormIsControlledBySectionEnergy.lean` passed its
necessary dependency check4350 with standard endpoint axioms and is wired. Its
direct final audit remains. The actual graph limit, closed-carrier coercivity,
residual identification and closure orthogonality are fully drafted in
`TheSectionProjectionConvergesInTheSourceGraph.lean`; first direct check is running.
Those limit conclusions are not yet promoted.

### Retained-reserve dual payment — proof target

For width fraction a≤1, the proved full source floor is the sum of cell masses with weights A_n=1+(1-a)*sectionReserveWeight(N,n)/8. Apply the exact combined source-kernel representation separately to each literal shifted profile. Local Cauchy–Schwarz followed by Young gives 2W(p,g)≤Σ A_n M_n+Σ D_n/A_n, where D_n is kernel square energy on the exact n-th cell. For the actual finite projection p, W(p,g)=W(p,p) and the weighted floor is at most W(p,p), hence W(p,p)≤Σ D_n/A_n. Take the existing energy supremum for the completed projection and retain the resulting signed residual lower bound. No mixed-bound premise or inverse coefficient Gram is introduced. This is a draft target until Lean passes.

### Literal graph completion — established

TheSectionProjectionConvergesInTheSourceGraph passed direct final audit38472 with only standard axioms. The net over all finite subsets of the actual arithmetic section space converges in the existing complete SourceGraph. Its original full Weil diagonal and mixed readings equal sectionCompletionEnergy and sectionCompletionPair; literal graph residuals realize completedSectionResidualForm and are orthogonal to the entire closed old source carrier. Coercivity also extends to that closure. This resolves fixed-space realization, not growing-window exhaustion.

### Bounded projection on the entire original graph — proof target

Use the literal C² lift as a linear map and let K be the closure of its arithmetic-section range. The already proved arithmetic graph coercivity makes the compression of the actual bounded Weil operator to K invertible by the inherited real Hilbert coercive-inverse theorem. Define P=incl_K*(compression)^(-1)*orthProj_K*T. Prove range in K, Weil-orthogonality of x-Px to K, identity on K, idempotence and exact residual pairing. Uniqueness from the arithmetic coercivity identifies P(Jg) with the existing finite-subset graph limit for every compact C² test g. No ambient positivity is assumed; the global signed residual remains. This is a source-domain extension of existing Hilbert machinery, not a new abstract inversion theorem. Status: target only.

### Retained-reserve dual payment — established

TheUnusedReserveReducesTheSourceCost direct audit79428 passed with standard axioms. The actual finite and completed removal cost is at most Σ_n D_n/[1+(1-a)*sectionReserveWeight(N,n)/8]. The completed residual retains W(g,g) minus that explicit cost. Exact disjoint-cell integration proves the new cost is no larger than the previous exact-union energy; at a=1 they coincide. All kernels combine primes, Gamma and both poles before squaring.

### Concrete complete-cell index capture — proof target

ACS CompleteWeilSourceTransfer already supplies one common logarithmic cell system recovering all mixed Weil entries of every finite compact C² family. Identify its polarized real limit with realWeilForm, complexify entrywise, and apply the established finite-index persistence theorem. The result should be unconditional: every finite smooth Weil negative index is at most the complete-cell index at all sufficiently late stages, on the actual common cell system. No source upper index is supplied or assumed. The distinction from generic descent is that the full arithmetic convergence premise is discharged by the existing cell source theorem. Status: draft target.

### Complete-cell index capture — established

TheCompleteCellsCaptureEveryFiniteIndex passed direct audit80785 with standard axioms. One actual common logarithmic cell system recovers all mixed full Weil entries of every finite compact C² family, and at every sufficiently late stage its complexified complete-cell Gram has at least the original Weil negative index. The convergence premise is discharged by the actual source transfer. This does not provide the missing upper index budget or exclude extra vanishing negative directions in approximants.

### A strict reserve at the original full width — proof target

Put r=fullSectionRatio, C=r*(exp(r)+1), rho=1/8-C. Existing geometry gives r<1 and r*(exp(1)+1)<=1/8, hence rho>0. For every originally allowed width, w*N<=r and w<=r, so the actual pole charge is <=C. The unrounded source theorem then gives W>=mass+rho*sectionReserve even at full width. Since sectionReserve>=mass on disjoint cells, this supplies the uniform actual mass floor W>=(1+rho)*mass without shrinking the space. Exact source Cauchy–Schwarz should improve finite/completed removal to D_U/(1+rho). This is a proposed sharpening of the previously rounded pole payment, not an independent positivity assumption. Corpus searches found the definition and existing rounded/unrounded estimates but no strict full-width statement. Status: unproved target.

### Bounded full-graph projection — established

TheClosedSectionHasABoundedWeilProjection passed direct audit48797 with standard axioms. The actual closed arithmetic carrier admits a unique bounded Weil projection on all SourceGraph vectors. It fixes that carrier, is idempotent, agrees with sectionGraphProjection on literal compact C² tests and retains exact full signed Schur subtraction. The coercivity premise of generic Hilbert inversion is discharged by the actual arithmetic source floor. Global residual sign/index remains open.

### Strict reserve at original full width — established

TheFullWidthStillRetainsArithmeticReserve passed direct audit81963, standard axioms. rho=1/8-r*(exp(r)+1)>0 with r=fullSectionRatio; no extra width shrinkage. The original complete source form retains rho*sectionReserve beyond mass and hence a uniform mass floor1+rho. Every finite and completed old-profile projection costs at most D_U/(1+rho). This improves the previously rounded full-width bound; aperture-dependent graph constants and the exhaustive critical-sign problem remain.

### Real-scale work and increment classification — proof target

Use the proved monotonicity of the actual completed source work and its natural-scale ENNReal limit to show every scale is bounded above by total copied energy. On the finite-energy stratum, convert the natural-scale limit to a real limit and squeeze all real scales. Therefore doubled-scale increments vanish. Conversely the existing annular quantum escape forces infinite off-line support to have arbitrarily high increments at least21/100. Aim to prove finite off-line support iff increments tend to zero iff eventually increments are below21/100. This is an unconditional classification, not a proof of a source upper estimate.

Further target: retain all sixteen ordered pairs in the four-copy off-line conjugate/reflection packet. At its own height, the exact source increment should be at least39/50 times one plus its positive diagonal angle. This would give a closed local quantum and distinguish eventual control from all-scale exclusion. No result claimed until Lean passes.

### Moving arithmetic bands and source decoupling — proof target

Take profiles supported in [0,w], vanishing for n<N/2, with original full allowed width. Translate their arithmetic section by -log N. The carrier lies in the fixed window [-log2,1]. The strict source reserve rho gives the growing mass floor A_N=1+rho*(1+(1+log N)/2). Apply the exact combined source-kernel square bound on this fixed window: A_N*W(p,g)^2 <= D_window(g)*W(p,p). Consequently every energy-normalized band section couples uniformly to a fixed compact probe by O((log N)^(-1/2)); an actual orthogonal projection costs O((log N)^(-1)). This would describe a growing arithmetic family, unlike fixed-N support shrinkage. The positive survivor is the explicit source coupling estimate and its rate. It does not rule out wider signed overlap families or other exhaustions. Status: proof target, not yet Lean formalized.

### Real-scale increment classification — established

VanishingScaleIncrementsCharacterizeFiniteSupport passed direct19465, all endpoints standard axioms, wired. Every real-scale source reading is at most total copied energy; finite off-line support gives the real-scale limit equal to that energy. Finite support iff doubled increments tend to zero iff they are eventually below21/100 at every real scale. This is a classification, not an arithmetic upper estimate.

### Quadratically rescaled work increments — proof target

Normalize the exact rational damping difference by R^2. Its fixed-height limit is3*gamma^2/2. The full quartet payment should then force eventual R^2*DeltaW>48 whenever any off-line zero exists, using height gap4 and its strictly positive diagonal angle. Arbitrarily high off-line zeros should force this rescaled work to infinity. On finite off-line support, use the actual finite Laurent-source rows to obtain a finite source moment limit, with all exterior fields retained. Aim for a three-way rate law: zero under RH, finite limit>48 for nonempty finite exceptions, infinity for infinite exceptions. This is a proposed source forcing/classification theorem, not a source upper estimate. Status: unproved; corpus searches and formalization required.

### Full quartet scale quantum — established

EveryOffLineQuartetCostsAStrictScaleQuantum passed direct21606, standard axioms, wired. All sixteen ordered pair interactions of the four conjugate/reflection copies give exact lower payment2*(hS-hR)*(1+angle). At own height the source increment is strictly above39/50. Eventual closed control at39/50 iff finite off-line support; all-scale closed control iffRH. No source upper estimate supplied.

### Moving-band source decoupling — established

MovingArithmeticBandsDecoupleFromFixedTests passed direct7896, all three endpoints standard axioms, wired. Actual upper-half band translated by-logN lies in[-log2,1], retains A_N=1+rho*(1+(1+logN)/2) times mass, and satisfies A_N*W(p,g)^2<=D_I(g)*W(p,p). Energy-unit coupling to every fixed compact probe vanishes uniformly. The source estimate covers growing dimension and arbitrary profiles; no completed band projection or exhaustive positive span is asserted.

### Finite critical-rate source moment — proof target

The critical-rate draft now has a separate actual finite-source continuation. For finite off-line copies F, W(R) equals the finite sum of depth*h_R(gamma)*xiSourceField over F. Every field is the full Laurent/Gamma source field, including all exterior critical zeros. Therefore Q(R)=R^2*(W(2R)-W(R)) should converge to M_2=(3/2)*sum_F gamma^2*depth*xiSourceField. Source coefficients can be signed. The fixed-quartet lower payment forces M_2>=3gamma^2*(1+angle)>48 at every exception, and hence3gamma^2<M_2. Together with infinite-support divergence, this yields the exact zero/finite exceptional/infinite critical-rate trichotomy and bounded-Q iff finite-support classification. Both new source files remain unchecked and unwired.

Further concrete target: every finite packet s of right-hand multiplicity copies has critical-rate charge(3/2)*sum_s gamma^2. The inherited source increment theorem gives this before the limit, with all exterior pairs nonnegative. The zero-free height gap makes this at least24*card(s), so every finite smooth Weil negative index should cost24 per negative square in Q's eventual lower bounds. This would connect the new rate invariant to index descent directly. No upper estimate is available.

### Inverse-square source curvature — proof target

Set a=R^-2 and h_a(t)=(1+a*t^2)^-2. Its second a-derivative is6*t^4/(1+a*t^2)^4. For actual heights >=4, this second profile is relatively Lipschitz in the exact sense needed to absorb the reflected mixed term. Proposed mechanism: each reflected pair is convex in a; convex secant comparison makes R^2*(pairWork(2R)-pairWork(R)) nondecreasing. Sum only after the already proved absolute convergence, avoiding differentiated infinite sums.

The candidate intrinsic endpoint is E_2=(3/8)*sum_{p,q} reflectedWork(...,gamma_p^2,gamma_q^2), interpreted as a nonnegative extended sum. Pairwise scaled limits would prove nonnegativity. Monotonicity would dominate each finite-scale kernel by its limit, giving convergence of actual source Q to E_2 even when infinite. On finite off-line support, E_2 must equal the finite full-source moment by uniqueness of the proved limits. Critical exterior rows are essential: when q is critical the pair kernel is exactly2gamma_p^2*angular(p,q), not a divergent symmetric height majorant. Status: no source theorem yet; scalar relative and secant scratch drafted, awaiting check.

### Critical-rate threshold uses the existing optimized arithmetic height floor

Corpus research exposed the stronger actual off-line certificate H=431349/2000 in PrimeArchLogHeightDefectOrderTwentyThreeEndpointOptimization. The critical-rate drafts now use this theorem, with all its analytic premises already discharged. Thus the draft exclusion quantum is3H=1294047/2000 and each negative square costs3H/2, superseding the elementary48/24 targets. The height-dependent quartet charge remains3gamma^2*(1+angle), so its positive angle makes the threshold closed. This is reuse of an existing arithmetic source budget, not a newly claimed height theorem. Both rate classification and index payment still await direct checks.

### Global spectral budget and quadratic index payment — proof target

The existing strip-edge source sum has total mass at most3/50. A finite packet of k right copies plus its disjoint reflections spends twice the packet mass; the per-copy floor is1/(gamma^2+1). Thus the packet reciprocal sum is at most3/100. Cauchy–Schwarz forces sum gamma^2 >=(100/3)k^2-k. At the critical source rate this becomes50k^2-(3/2)k. Together with the optimized height-floor payment, this gives the maximum of a linear and a quadratic index charge, provided formalization succeeds. It uses an actual arithmetic upper budget for a different, positive resolvent quantity to strengthen forcing of the signed normal work. It does not identify the two quantities or prove an upper bound for normal work.

### Critical-rate exception detector — established

TheQuadraticScaleWorkDetectsEveryException passed direct95103; all four endpoint axioms are standard. Wired and foundational README updated. Q=R^2DeltaW retains fixed quartet charge3gamma^2(1+angle), source-derived closed exclusion quantum3H with H=431349/2000, cofinal RH equivalence, ordered finite Laurent-source detection, and divergence for infinite support. Finite-moment classification and index payments remain unchecked.

### Exact finite source moment and rate trichotomy — established

TheCriticalRateClassifiesAllOffLineSupport passed direct76302; all five endpoint axioms standard, no warnings. Every finite off-line copy is retained with its full exterior Laurent/Gamma source field. W(R) is its exact finite damped sum; Q tends to M2=(3/2)sum gamma^2*depth*sourceField. Every exception satisfies3gamma^2(1+angle)<=M2 and3gamma^2<M2. Under nonRH, finite M2 exceeds3H. Eventual boundedness of Q and existence of a finite Q limit are both equivalent to finite support. The zero/finite>3H/infinite rate trichotomy is unconditional. No source upper estimate. Wired/README updated.

### Critical-rate index payment — established

TheCriticalRatePaysEveryNegativeSquare direct6213 PASSED, all four endpoints standard axioms, no warnings. Actual Pontryagin packets force critical-rate charge and finite source moment pays lambda times every finite smooth Weil index, lambda=3H/2. Ordered finite-source detection retains all exterior rows. Wired and README updated. No arithmetic upper budget.

### Quadratic arithmetic index cost — established

TheSourceBudgetMakesTheIndexCostQuadratic direct73888 PASSED, all four endpoint axioms standard, no warnings. Full strip-edge arithmetic budget gives sum_right 1/(gamma^2+1)<=3/100; weighted Cauchy forces packet charge and each finite smooth Weil index k to cost50k^2-3k/2 in eventual Q and finite M2. Together with lambda*k this gives the maximum of linear and quadratic charges. It is not an upper bound on normal work. Wired and foundational README updated.

### Inverse-scale curvature and source monotonicity — established

TheCriticalSourceRateIsMonotone direct33517 PASSED, all four endpoints standard axioms, no warnings. Inverse-scale reflected pair convexity, pointwise critical pair monotonicity, full completed Q monotonicity and exact height-square pair limit established. Source order uses absolute summability, not infinite differentiation. Wired/README/card/checks updated. Scratch19343 removed after final source pass.

### Fixed carriers paying an unbounded source-graph weight — proof target

The completed projection currently has graph coercivity on each fixed arithmetic window. Seek one fixed unbounded logarithmic carrier with a graph coercivity constant independent of the finite prefix. This is a source construction on a restricted carrier; no density or exhaustive signature bound is claimed.

First target: for every continuous real weight omega with omega>=1 and every strictly increasing centre sequence b_n, construct one positive width sequence w_n<=1 such that every finite independently profiled sum f, supported in those cells, satisfies integral omega*f^2 <= W(f,f). The exact diagonal-extension theorem already pays any prescribed new square-mass charge. On each fixed canonical cell envelope choose a bound c_n for omega. In the induction retain a_N=1+1/(N+1) times weighted mass. Spend epsilon_n=a_n-a_(n+1) on old ordinary mass, which is at most old weighted mass; the new diagonal pays a_(n+1)c_n. Weighted mass is exactly additive across the separated old/new supports. All old widths remain fixed.

Then instantiate omega(u)=1+2(1+||tanhL||^2)*cosh(u/2)/riemannKernelReal(u). The literal graph identity gives ||Jf||^2 <= W(f,f)+2(1+||tanhL||^2)||Jf.source||^2 <=2W(f,f). The resulting unbounded sparse carrier can be completed with one global coercivity constant. The graph mass identity and polar rows must be proved on actual C2 tests, not assumed. Existing private cell-envelope helpers should be exposed through a reusable construction rather than silently treated as imported public facts. No existing olean may be rebuilt.

Status: research target; no new source yet. Preliminary corpus query did not locate this weighted fixed-carrier theorem. The inherited aperture graph-norm equivalence has constants depending on the aperture and does not supply this result. Curvature/canonical-energy final checks take priority before this construction.

### Canonical height-square source energy — formalized

`TheCriticalSourceRateHasACanonicalEnergy.lean` identifies the real-scale limit of
`ofReal (R²(W(2R)-W(R)))` with the extended nonnegative sum of the exact limiting
reflected kernels. Every finite-scale rate is bounded above by this canonical energy.
Its finiteness is equivalent to finite off-line support; on that stratum it equals
the full Laurent-source moment. Global linear and quadratic finite-index charges
hold, including the infinite-energy stratum. Critical exterior rows retain only
the off-line height weight after exact cancellation. Nonnegative entries are not
asserted to be a positive semidefinite Gram kernel.

Direct final audit8646 passed, five printed endpoints depend only on propext,
Classical.choice and Quot.sound. Wired into own umbrella; foundational README
updated. Canonical/API scratch files removed. No independent upper energy bound
has been obtained, so the source-payment question remains open.

### Uniform graph closure of a fixed unbounded carrier — next proof target

After the arbitrary-weight induction, specialize to
`omega_epsilon = 1 + (2(1+||tanhL||²)/epsilon) cosh(u/2)/riemannKernelReal(u)`.
The exact inverse Doob source-mass identity and full polar graph identity should
then prove `||Jf||² <= (1+epsilon) W(f,f)` for every prefix of one fixed
width sequence. No aperture-dependent norm constant is permitted in this target.

Construct the literal linear space of finitely supported independent profiles on
these chosen cells, take its range closure in the existing source graph, and
transfer this uniform coercivity to the closure. Compress the actual bounded
Weil operator to this closed carrier; the existing coercive inverse then constructs
a bounded original-form projection. Prove the exact signed Schur identity on the
whole graph. This removes the fixed-aperture restriction from the current
projection construction. The residual sign, a comparable-spacing width bound,
and exhaustive transfer remain independent open arithmetic questions.

### Fixed carriers pay the complete graph mass — formalized

`FixedCellsControlTheCompleteSourceGraph.lean` proves one fixed width sequence
for every continuous spatial weight omega>=1 and every increasing centre sequence.
Every independently profiled prefix satisfies weighted square mass<=full Weil
energy. Specializing omega to `1+(B/epsilon)*rho`, with the exact inverse Doob
mass density rho and the proved full polar graph charge B, gives
`||Jf||²<=(1+epsilon)W(f,f)` uniformly across all prefixes. Integer-log centres
have an unconditional factor-two realization. No hidden source norm, mixed bound,
width comparability or density assumption is present.

Full scratch7493 and mandatory actual direct74617 passed; four printed endpoints
use only propext, Classical.choice and Quot.sound. Actual source wired; foundational
README/checks updated. Removed weighted scratch. The uniform-closure/projection
target above remains in its separate draft until checked.

### Touching-cell source payment — research target

The existing source extension uses a positive gap only for the Gamma cross term.
The corpus already supplies a sharp Carleman boundary operator. Investigate the
literal mixed Weil form for old profiles supported to the left of a boundary and
new profiles supported to its right, allowing their supports to meet at that
boundary. A uniform half-line Gamma L² bound, combined with the already proved
finite prime horizon and global pole mass bounds, should remove gap dependence
from the adjustable old/new mass payment. The short-cell logarithmic diagonal
could then absorb the new charge. This target assumes no favorable mixed sign.

A touching-cell extension alone would still spend old mass at every step;
contiguous exhaustion would require a summable spatial allocation of those losses
or a signed arithmetic improvement. It must not be inferred from merely positive
new widths. Search and inspect the exact sharp-cut source statements before
formulating a claimed theorem.

### Unbounded arithmetic carrier and exact signed projection — formalized

`TheUnboundedCellCarrierHasAWeilProjection.lean` constructs the actual finitely
supported independent-profile space, its graph range closure, and a bounded
original-Weil projection onto this fixed unbounded logarithmic carrier. Uniform
coercivity survives closure. Exact signed Schur subtraction holds on every graph
vector, with removed energy at most twice the squared norm of the actual Weil
operator applied to that vector. The actual cusp escape proves this closed carrier
proper. Every inherited theta critical mode has zero projection; an infinite
independent zero-energy family therefore survives in the residual.

Mandatory actual direct audit45786 passed with persisted output in
`logs/arithmetic-index-descent-unbounded-carrier-audit.txt`; all seven printed
endpoints use only propext, Classical.choice and Quot.sound. No warnings. Wired
into own umbrella and explained in the foundational README. Earlier audit handle
was lost at pause, so no success was inferred from it. No residual sign or
exhaustive upper index bound follows from this restricted-carrier construction.

### Exact Gamma boundary normalization — research target

The inherited Carleman comparison gives operator norm at most2pi. For the actual
Gamma density k(t)=exp(-t/2)/(1-exp(-2t)), test the positive Schur weight
w(t)=exp(-t/2)/sqrt(1-exp(-2t)). For s>0, the candidate exact row identity is
integral_0^infinity k(s+t)w(t)dt=(pi/2)w(s). The substitution
x=sqrt(exp(2t)-1) reduces the integral to
exp(-s/2) integral_0^infinity dx/(x^2+1-exp(-2s)). Equivalently use the
arctangent primitive directly, avoiding a new change-of-variable interface.

If formalized, weighted Schur would improve the boundary operator upper bound
fourfold and the adjacent-cell Gamma charge by the same factor. A matching lower
norm bound would require a separate boundary-concentration argument. Neither
claim is currently formalized here. This estimate does not control cumulative
prime/pole assembly or eliminate the signed residual. Complete the literal C2
touching-cell transfer before relying on this sharper target.

### Literal touching Gamma transfer — formalized

`TouchingSupportsHaveBoundedGammaInteraction.lean` passed mandatory actual
direct99370, four standard endpoint dependency prints and no warnings. It
identifies the actual ordered half-line L2 pairing, transfers its bound to signed
continuous compact profiles, and proves the C2 spectral cross term equals the
negative literal collar for every disjoint pair. The resulting ordered Gamma
bound is pi times the sum of ordinary square masses, independent of gap, boundary,
width and derivatives. Existing sharp-boundary operator supplies the estimate;
no new mixed-sign or source-domain premise is introduced. Wired and README updated.

`TouchingCellsPayTheFullMixedSource.lean` is the actual importer, still unchecked:
full prime/pole payment and the adjacent short-cell extension await its final audit.
The sharper pi/2 Schur row remains a separate untested research draft.

### Retained pole cancellation and localized Gamma loss — research target

For supports ordered about b, write left and right distance profiles
F(s)=f(b-s), G(t)=g(b+t), s,t>0. The exact Gamma density splits as
k(s+t)=exp(-(s+t)/2)+exp(-2s)k(s+t)exp(-2t).
Its first rank-one pairing is A(f)B(g), with the b factors canceling. In the
full Weil cross term this should cancel precisely the A(f)B(g) pole contribution,
leaving B(f)A(g), the actual signed prime Hankel contribution, and the faster
Gamma tail. Check the literal source normalizations before formalizing.

The remaining Gamma tail should then cost only the boundary-local masses
integral_{u<b} exp(-4(b-u)) f(u)^2 and
integral_{u>b} exp(-4(u-b)) g(u)^2. This could prevent spending the whole old mass
at every extension. The remaining global polar row must be retained as part of
the completed form; neither its sign nor its cancellation against the prime
Hankel term may be assumed. A signed prime-discrepancy estimate is still required
for an exhaustive index bound. No theorem about this split has been claimed here.

Rank one here describes a single ordered cross block. Assembling many cuts does
not make the surviving ordered kernel one global rank-one quadratic form. Index
accounting must retain the original global pole form and every mixed entry.

### Full touching-cell source payment — formalized

`TouchingCellsPayTheFullMixedSource.lean` passed mandatory actual direct85405,
three standard endpoint dependency prints and no warnings. The actual Gamma
import olean66915 passed first, unchanged after direct99370. The full source now
has an ordered-window mass bound independent of the touching boundary, an
adjustable epsilon old-mass payment with explicit reciprocal new cost, and an
adjacent short-cell extension retaining the exact old Weil diagonal and any
prescribed new-mass charge. No old positivity or mixed sign is assumed.

Wired, foundational README and check record updated. The geometric positive-gap
restriction is removed. Cumulative whole-old-mass losses, useful width lower
bounds and the exhaustive signed index remain open. Exact Gamma Schur weighting
and retained pole cancellation are separate research targets, not inputs to this
formalized result.

### Exact Gamma Schur weight — formalized

`GammaBoundaryHasAnExactSchurWeight.lean` passed mandatory actual direct92764.
All three endpoint dependency prints contain only propext, Classical.choice and
Quot.sound; no warnings. The exact weighted row is (pi/2)w(s), and weighted
Cauchy–Schwarz/Tonelli improves the norm bound of the existing actual Gamma
boundary operator from 2pi to pi/2. This proves an upper bound, not norm equality.
No L2 eigenvector or sign of the full source is inferred. Wired into the own
umbrella; foundational README and checks updated.

The next actual cancellation module requires the full touching-source olean.
Its emission is running as sole owned Lean session56263; no existing olean was
rebuilt. The ordered-block pole cancellation remains unchecked until its own
mandatory direct audit.

### Ordered source discrepancy — next research target

The actual ordered mixed source after first-Gamma cancellation is
B(f)A(g) minus the actual prime source minus the exponentially localized Gamma
tail. Put C(h)=integral f(u)g(u+h)du and q(h)=exp(-h/2)C(h). For compact C2
profiles ordered about b, q is C1, compactly supported and zero for h<=0.
The surviving pole is integral_0^infinity exp(h)q(h)dh; the ordered prime source
is sum Lambda(n)q(log n), with no factor2. Lag Abel summation gives their
difference as integral (psi(exp(h))-exp(h))q'(h)dh. All finite horizons and
regularity must be derived from the actual profiles. The full Weil cross term
should therefore equal this signed discrepancy minus the localized Gamma tail.

Corpus lead inspected: ArithmeticIncidencePositivity/LagChebyshevAbelSummation
provides generic exact lag Abel summation, integrability, one-pole error split,
constant/affine centering and autocorrelation derivative calculus. The proposed
contribution is transfer to the literal ordered C2 mixed Weil source, not a new
generic Abel identity. CHMDStage6 supplies exact exponential mixed-moment
factorization. The actual prime normalization was read in
BoundedWindowsHaveFinitePrimeInteraction. Ordered crossCorr must retain its
orientation; mixed profiles cannot be replaced by a diagonal model.

The centered defect bound depends on variation against q', not an assumed
critical-scale estimate. It will not by itself bound the global negative index.
No proof or new positivity result is claimed before the actual Lean audit.

### Ordered pole cancellation and localized Gamma charge — formalized

`TheOrderedGammaTailRetainsPolarCancellation.lean` passed mandatory actual
direct59426, four standard endpoint dependency prints and no warnings. The first
Gamma exponential equals A(f)B(g), cancels that exact polar term, and leaves
W(f,g)=B(f)A(g)-prime(f,g)-GammaTail(f,g). Conjugating the tail by boundary
distance weights bounds it by pi times the two exponentially localized square
masses. The statements retain actual signed compact profiles; no sign input
is added. Wired and foundational README/checks updated.

The rank-one description applies to one ordered cross block, not a global
rank-one correction after many cuts. Cumulative signed source payment remains
open. Actual importer TheOrderedWeilSourceIsACenteredChebyshevDefect.lean is
complete but unchecked/unwired; its required cancellation olean is next.

### Gamma boundary reserve and saturation — research target

For k(s+t), w(t)=exp(-t/2)/sqrt(1-exp(-2t)), and C=pi/2, the now formalized
exact row suggests the ground-state identity
 C*integral |f|^2 - Re< f,H_Gamma f >
 = (1/2)*double_integral k(s+t)w(s)w(t)|f(s)/w(s)-f(t)/w(t)|^2.
This would identify the retained Schur slack, not merely bound it by zero.
Integrability and transfer to the existing L2 operator must be proved. The
actual public inner_ccmGammaBoundaryCLM and integrable_ccmGammaBoundary_pair
were inspected and provide its mixed kernel representation.

Sharpness is a separate target: w^2=1/(2*sinh(t)) is not integrable at zero.
Truncations on [epsilon,1] have diverging mass while the omitted cross-boundary
interaction should stay bounded by a Carleman comparison, forcing norm pi/2.
This is a proposed argument, not a formal theorem or a claim of an L2 eigenvector.
An exact slack could support mixed source estimates, but no uniform strict gap
or prime-sign control follows from its existence. Corpus searches found the
existing general Schur upper calculus, not this exact actual-Gamma lower result.

### Centered ordered arithmetic source — formalized

`TheOrderedWeilSourceIsACenteredChebyshevDefect.lean` passed mandatory actual
direct3416. Its three endpoint dependency prints contain only propext,
Classical.choice and Quot.sound, with no warnings. The actual ordered Weil
cross term is minus the centered Chebyshev discrepancy against its own lag
derivative, minus the exponentially localized Gamma tail. Regularity, support
horizon, integrability and the prime normalization are derived from the actual
compact C2 profiles. No critical arithmetic estimate is assumed or proved.
Wired into the own umbrella and recorded in README/checks. The weighted signed
discrepancy and its cumulative index payment remain open.

### Exact mixed Gamma reserve — candidate implementation

Actual source `TheGammaBoundaryReserveIsAnExactSquare.lean` now contains the
stronger two-input identity
 pi/4*(norm(f)^2+norm(g)^2)-Re<g,H_Gamma f>
 = (1/2)*integral k(s+t)w(s)w(t)|g(s)/w(s)-f(t)/w(t)|^2.
The integrable diagonal pieces come from exact Schur rows; the cross term uses
the existing absolutely integrable complex kernel pairing. This retains all
shape-dependent slack. API18144 passed. Necessary previously absent Schur
olean emission55733 is running; actual reserve module remains UNVERIFIED and
UNWIRED until its own direct audit. This does not establish a uniform strict
gap, sharpness, nonattainment, or the signed prime surplus.

### Gamma equality rigidity — candidate, not yet checked

A second candidate source, TheGammaBoundaryBoundHasNoNonzeroEqualityCase.lean,
proves w(t)^2 >= exp(-1)/(2t) on (0,1), hence the exact weight is not L2.
A zero quadratic reserve would give f(s)/w(s)=f(t)/w(t) almost everywhere on
its product carrier. Fubini fixes the ratio, and square integrability forces
its constant to vanish. The proposed conclusion is strict quadratic deficit
for each nonzero actual L2 vector. This is not a uniform gap or norm sharpness.
The source and its API scratch remain UNVERIFIED, UNWIRED; the reserve dependency
must pass its own actual audit first. No arithmetic upper estimate is inferred.

### Exact mixed Gamma reserve — formalized

Mandatory actual direct60654 passed. All three endpoint dependency prints show
only propext, Classical.choice and Quot.sound; no warnings. The full two-input
square identity and product integrability now hold on the original half-line
L2 carrier. Wired into the own umbrella, foundational README and checks updated.
The equality-rigidity candidate remains unchecked. Scalar sharpness and the
actual signed arithmetic payment are separate remaining questions.

### Retaining the Gamma reserve in the actual arithmetic block — next target

The exact mixed Gamma square can be transported through the actual shifted,
reflected half-line profiles used in the touching-support theorem. Applying it
to the exponentially tilted profiles after first-pole cancellation should give
 W(f,g) = -integral(E-c)q' -pi/4*(leftBoundaryMass+rightBoundaryMass)
          + integral GammaPairReserve(F,G).
Here F,G must be the literal translated/reflected restrictions of those same
profiles, with square norms equal to their actual boundary masses. The source
identity and all profile maps/norms must be proved; no abstract Gram replacement.
This would retain a nonnegative shape-dependent reserve inside the original
arithmetic cross block. It would neither prove a cumulative signed payment nor
permit spending one global pole or one old mass independently at many cuts.
No implementation or formal theorem for this transfer exists yet.

The actual-source reserve transfer is now implemented in candidate
`TheOrderedWeilSourceRetainsItsGammaSquareReserve.lean`, including exact
profile maps, norm preservation, literal collar transfer, exponential tilt,
nonnegative reserve and the original centered-source identity with that reserve.
It remains UNVERIFIED/UNWIRED. The reserve dependency passed direct60654 and
necessary olean29082. The centered-source dependency passed direct3416 but needs
its first olean for this actual importer. Equality-rigidity direct20296 is the
sole running owned compiler; the transfer check must follow sequentially.

### Gamma quadratic equality — formalized

Mandatory actual final97625 passed without warnings. All three endpoint
dependency prints contain only propext, Classical.choice and Quot.sound.
The exact weight has reciprocal upper/lower square bounds and is not L2;
vanishing quadratic reserve forces the zero L2 profile. Every nonzero profile
has a strict quadratic deficit. Wired, foundational README/checks updated,
completed rigidity API scratch removed. No equality-module olean is needed.
Uniform gaps, norm sharpness and mixed equality classification are not claimed.

### Gamma square reserve on the original arithmetic source — formalized

Mandatory actual direct22913 passed without warnings. Four endpoint dependency
prints show only propext, Classical.choice and Quot.sound. The literal shifted,
reflected and tilted C2 profiles preserve their actual square masses; their
Gamma pairing equals the original ordered collar. Consequently
 W=-integral(E-c)q'-pi/4*(leftBoundaryMass+rightBoundaryMass)+reserve,
with the reserve nonnegative and defined by the same actual L2 profiles.
The resulting signed lower bound retains the Chebyshev discrepancy. Wired,
foundational README and checks updated. No transfer olean needed yet. Cumulative
allocation, the arithmetic upper/sign budget and exhaustive index remain open.

### Quantitative Gamma boundary calibration — in progress

Actual indicator truncations of the exact Schur weight have a candidate
logarithmic mass theorem. Four power rectangles give a proposed uniform
reserve bound of 16 and hence sharp norm pi/2 on the original half-line
operator. The two candidate sources remain unverified and unwired.
This would rule out uniform one-cut improvement while retaining explicit
near-critical profiles as the positive survivor.

A complementary target is mixed equality rigidity: zero mixed reserve forces
both profiles to vanish. Applied to the pair ((pi/2) f, H f), this should prove
strict norm inequality for every nonzero f, while sharpness would show the gap
is not uniform. A two-cut compact-product argument remains a later research
target, with the actual compactness and arithmetic source assembly still missing.

### Literal truncated Gamma weights — formalized

Actual final52260 passed without warnings, with three standard endpoint
dependency prints. The compact indicator of the exact weight is an actual
half-line L2 vector, its norm is exactly its interval square integral, and
its mass is at least exp(-1)/2 times log(1/a). Exponential inner cutoffs give
a linearly growing sequence of masses. Wired; the reserve bound and sharp norm
remain unverified candidates. The separate mixed equality/strict norm source
is also complete but unverified and unwired.

### Mixed Gamma equality and norm rigidity — formalized

Actual direct87656 passed without warnings; both endpoint dependency prints
contain only propext, Classical.choice and Quot.sound. Zero mixed reserve
forces both actual L2 inputs to vanish. The pair ((pi/2)f,Hf) therefore
excludes equality in the norm bound for every nonzero f. Wired and foundational
README/checks updated. This is pointwise strictness, not a uniform gap. The
revised sharpness candidate remains unverified while its direct check runs.

### Arithmetic mixed detail/average payment — next concrete target

The corpus now gives simultaneous Gamma detail, mean-graph and exterior
payment for arbitrary complete cells (ACS CompleteCellMeanGraph), and the
coarse-to-detail prime orientation vanishes (HaarCellCoarseSplitting).
The reverse prime-two orientation should equal the actual weighted sum
 sum_a haarMass(a)*d(a)*(q(2a)-q(2a+1)),
with finite-horizon coefficients extended by zero. Its adjacent mean-graph
conductance is haarMass(a)*h_a*k(h_a), where h_a=logCellWidth(a). The elementary
lower bound h*k(h)>=exp(-1/2)/2 for 0<h<=1 would control this mixed term by
detail mass and the already retained mean graph. Preserve the literal factor
2*vonMangoldt(2)/sqrt(2) from the original prime energy.

This is a proposed arithmetic estimate, not a formal theorem. No source has
been written yet. The complete all-prime payment and iterative signed Schur
cost remain open; summing fixed-prime scalar bounds loses the required control.

### Sharp Gamma boundary norm — formalized

Mandatory actual final84870 passed without warnings; all four endpoint
dependency prints contain only propext, Classical.choice and Quot.sound.
Four power rectangles bound the actual cutoff square reserve by 16, while
logarithmic mass diverges. The existing operator norm is exactly pi/2, and
explicit nonzero cutoff vectors approach its Rayleigh value. Together with
passed mixed equality rigidity, the sharp norm is never attained by a nonzero
vector. Wired and foundational README/checks updated; no olean needed.

Scope and survivor: a uniform scalar L2 improvement is impossible, but the
exact square reserve and concrete near-critical sequence survive. Joint
bounds retaining full diagonal Gamma energy are not ruled out. No uniform
arithmetic source upper, exhaustive index bound or individual-defect
exclusion follows from this calibration.

### Exact prime-two mixed differences — formalized

Actual direct19391 passed clean. All four endpoint dependency prints contain
only propext, Classical.choice and Quot.sound. The literal shift2 sends one
balanced detail to two complete coarse atoms, giving haarMass times their
coefficient difference. The full two-orientation original prime coefficient
has the same identity; the other orientation vanishes. An odd common horizon
retains all mixed contributions, and adjustable Young payment charges only
that actual coarse variation. Wired and foundational README/checks updated.

Three continuation sources are candidates, not established results: Gamma
mean-graph payment, literal physical-integral transfer, and arbitrarily small
Gamma-relative high-detail tails. The all-prime mixed source and cumulative
full-form Schur payment remain open.

### Actual Gamma mean-graph payment of prime two — formalized

Mandatory actual final86354 passed clean. All four endpoint dependency prints
contain only propext, Classical.choice and Quot.sound. The retained mean graph
controls exactly the adjacent variation read by the surviving prime2 orientation.
With ell=vonMangoldt(2)/sqrt(2), one graph payment yields the explicit constant
C2=1+4*ell^2/exp(-1/2). Gamma energy minus the entire absolute mixed block retains
sum(log(a)*mass(a)*d(a)^2)-C2*sum_(a<=Y)mass(a)*d(a)^2 at full odd horizon2Y+1.
A fixed lower detail index therefore makes Gamma pay the block while all coarse
coefficients remain arbitrary. Wired; foundational README/checks updated.

The original physical-integral transfer, arbitrary relative tail smallness and
uniform negative-dimension bound remain unverified candidates. The current
proved theorem compares actual half-line prime vectors and actual complete BV
Gamma profiles with identical coefficients. It does not pay the other primes,
pure coarse prime form or poles. Main programme objective remains open.

### Arbitrarily small mixed prime-two tails — formalized

Mandatory actual88991 passed clean, three standard endpoint dependency prints.
An arbitrary positive graph share delta gives detail charge C2/delta. A single
A>exp(C2/delta^2) makes the high-detail mixed block at most delta times the
ORIGINAL UNTRUNCATED complete-profile Gamma energy, uniformly in odd horizon
and arbitrary coarse/detail coefficients. Exact additivity identifies the tail
with the difference from the finite low-detail head. This proves uniform finite
coordinate approximation in the actual Gamma form. Wired/docs/checks updated.

The physical polarized-integral transfer and uniform real negative-dimension
bound for Gamma minus prime2 mixed are candidates pending direct checks.
Translated-block variance could sharpen the tail rate and extend fixed lag,
but remains research rather than a proved general integer-lag theorem.

- Formalized `TheCoarseDetailPrimePairIsTheLiteralSource`: actual coarse/complete representatives, both mixed physical correlations, literal polarized prime-two source identity, and physical Gamma-tail payment. Direct actual-source audit16150 passed with standard dependencies. Full all-prime/index questions remain open.

- Formalized `ThePrimeTwoMixedFormHasUniformFiniteIndex`: one fixed low-detail readout bounds every strictly negative real subspace for original Gamma minus signed prime-two mixed source, uniformly in odd horizon and finite complete-profile family. Direct actual-source audit63538 passed with standard dependencies. This is an actual partial-source upper index bound; full Weil index remains open.

- In progress: translation-uniform actual detail probe payment. Target: for original complete profile `F=completePairProfile q d X`, `Y<=X`, `A>=1`, every real translation `t`, `log(A)*abs(integral haarSectionProfile(d_ge_A,Y)(u)*F(u-t)) <= levyEnergy F`. Mechanism: zero Haar mean, local integral Young, logarithmic Gamma variance on disjoint pairs, exact Gamma translation invariance. This should extend the actual prime-two payment to all even integer lags and then the complete fixed Euler factor. No all-prime summability claimed; no theorem yet verified.

- Formalized `MergedCellVariancePaysCoarseDifferences`: exact adjacent-mean square lower bound inside merged variance; original complete-profile variance retains `haarMass(a)*(q(2a)-q(2a+1))^2`; disjoint merged intervals yield its full log(a)-weighted Gamma bound. Direct actual-source audit21559 passed with standard dependencies. Independent detail and coarse bounds are not additive shares of one energy.

- Formalized `ThePrimeTwoMixedTailHasLogarithmicDecay`: full odd-horizon actual mixed tails and exact finite-head error satisfy `log(A)*abs(error)<=(1+ell^2)*Gamma(original)`; dividing gives explicit inverse-log rate and cutoff exp(O(1/delta)). Direct actual-source audit66377 passed with standard dependencies.

- Formalized `TranslatedDetailsAreUniformlySmallInGammaEnergy`: original complete-profile Gamma energy pays high detail against every real translate, with positive monotone reciprocal-width weight kappa_A>=log A, including an entire-detail A=1 bound. No odd-horizon restriction; all original q,d retained. Direct actual-source audit32939 passed with standard dependencies. Whole fixed Euler-factor mixed payment is next; full prime source remains open.
