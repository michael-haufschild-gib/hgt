# PM centered-divisor dyadic energy budget

- **ID:** pm-centered-divisor-dyadic-energy-budget
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** PM-31; pm-centered-divisor-haar-criterion
- **Statement:** For every 0<epsilon<1/2, the actual centered divisor
  discrepancy has a summable geometric bound on its dyadic weighted energies.

## Goal

Let c_epsilon(n)=sum_{d|n} mu(d)d^(-epsilon),
C_epsilon(x)=sum_{1<=n<=floor(x)} c_epsilon(n),
alpha_epsilon=1/zeta(1+epsilon), and
R_epsilon(x)=C_epsilon(x)-alpha_epsilon*x.
The new centered-energy leaf identifies canonical PM admission exactly with
integrability of |R_epsilon(x)|^2/x^2 over x>0. The open producer is that
integrability at positive dampings arbitrarily close to zero.

Conjecture, with no numerical experiments:

`for each 0<epsilon<1/2 there exists C_epsilon>0 such that, for every j>=0,`

`integral_[2^j,2^(j+1)] |R_epsilon(x)|^2/x^2 dx
   <= C_epsilon * 2^(-epsilon*j).`

This is stronger than the needed energy admission. It is not established by
the criterion, coefficient positivity, the summatory mean, or the existing
epsilon>=1/2 theorem. No bound uniform in epsilon is requested.

## Conditional consequence, not the missing proof

For fixed positive epsilon, the proposed dyadic bounds sum geometrically.
For 0<x<1, C_epsilon(x)=0, so the weighted integrand is the constant
|alpha_epsilon|^2. Finite dyadic intervals have finitely many summatory
jumps. Hence the conjecture supplies full weighted integrability. The
already proved cofinal-energy receiver then supplies RH if the bound is
proved for dampings arbitrarily close to zero. That producer remains open.

## Approach and prior-research audit

The parent card records exhaustive review of the displayed results from
searches1060,1062,1064,1065,1066. None supplies this estimate. The existing
finite cumulative covariance has kernel 1/max(j,k)-1/(T+1), including all
unequal pairs. The lcm quadratic formula and Graham bounds control unsummed
coefficients; they do not control this accumulated discrepancy.

First identify the literal centered remainder with the convergent
fractional-part series

`R_epsilon(x) = -sum_{d>=1} mu(d)d^(-epsilon) frac(x/d)`.

For fixed x>=0, the head is finite and the tail has absolute majorant
x*d^(-1-epsilon). The identity follows from the finite divisor-floor sum
and the absolutely convergent density series. At x=1/t it identifies the
centered physical source with the actual damped Nyman series. Audit the
corpus for an existing exact statement before adding Lean code (search1067
is audited below).

The next estimate must retain signed off-diagonal cancellation. Absolute
generator norm summation only reaches epsilon>1/2. Canonical prime-aperture
budgets are already disproved throughout 0<epsilon<1/2; they are not a viable
approximation mechanism for this bound. Pointwise absolute convergence of
the fractional-part series does not authorize a global L2 interchange.

## Gates

- [x] Well-posed actual carrier and explicit sufficient budget
- [x] Existing displayed corpus candidates audited on parent card
- [x] Exact fractional-part carrier identity audited/formalized
- [ ] Actual small-positive dyadic bound proved on paper
- [ ] Dependency-closed proof formalized and leaf/axiom/lint audited

## Exact discrete target (paper bridge)

The density is real. Put b_epsilon(n)=c_epsilon(n)-alpha_epsilon and
D_epsilon(N)=sum_{1<=n<=N} b_epsilon(n). Then

`R_epsilon(x)=D_epsilon(floor x)-alpha_epsilon*frac(x)` for x>=0.

On x>=1 the correction belongs to L2(dx/x^2), since |frac(x)|<=1.
On 0<x<1 the full weighted remainder energy is the finite constant-density
contribution. Nonnegative countable additivity over the unit cells gives

`integral_[1,infinity) |D_epsilon(floor x)|^2/x^2 dx
   = sum_{n>=1} D_epsilon(n)^2/(n*(n+1))`,

where the equality is first an extended nonnegative integral statement;
ordinary finite integrals require the summability conclusion. Consequently
the PM admission criterion is also exactly this weighted sequence's
summability. No global boundedness of D_epsilon may be assumed.

For each finite T, the existing cumulative covariance identity rewrites
the partial weighted energy as

`sum_{j,k<=T} b_epsilon(j)*b_epsilon(k)
   * (1/max(j,k)-1/(T+1))`.

Thus a finite upper bound on these actual signed partial covariances, for
cofinally small positive epsilon, is a sufficient arithmetic producer.
This bound is not supplied by positivity of c_epsilon or positivity of the
covariance kernel. The signed coefficients b_epsilon and all cross terms
must remain present.

## No-go closure

No obstruction to this exact budget has been proved. If the proposed rate
fails, extract the sharp surviving rate, an energy decomposition, or an
arithmetic classification before retiring it. Do not treat failure of an
absolute-value estimate as failure of the signed budget itself.

## Log

- 2026-10-01 — Opened after the centered-energy equivalence passed its
  scratch check; predecessor leaf build/final audit still underway. RH and
  its negation remain unproved.
- Search1067 (`damped Mobius fractional part centered summatory remainder`,
  deep): reviewed all20 candidate/all20 source statements and both proposed
  ingredient groups. Finite undamped residue identities do not provide the
  infinite real-damping identity. The generated Euler/Fisher step changes
  carrier and keeps an absolute-convergence parameter greater than one.
  The modulus-normalized remainder inversion was inspected directly; its
  weighted ordinary power-sum error is a different source. No exact PM
  fractional-part identity or dyadic energy producer returned. Partial=false;
  63869 files; generation1173984,coverage/current1173988; semantic coverage
  unmeasured, background refresh incomplete. No novelty claim follows from
  this bounded search.
- The predecessor centered-energy leaf is fully audited (24 PM-31 leaves /
  5821 lines /428 declarations). Scratch1068 now checks11 declarations for
  the literal floor/fract sum, pointwise absolutely summable damped Nyman
  representation, prefix convergence, and realness of the density. This
  does not yet give a global L2 estimate or the proposed dyadic budget.
- Search1069 (`signed cofactor Mobius divisor discrepancy dyadic energy
  bound`, deep): all20 candidate/all20 source statements and both proposed
  ingredient groups reviewed. Cofactor parity identities and finite clock
  cancellations retain useful signs, but no cofinal PM energy bound follows.
  The displayed Heath-Brown medium-Mobius estimate is on c>=1 and saves
  logarithms; the CGL detector bound controls a different finite coefficient
  energy. Direct inspection of `MobiusHalfDecayFromSubpower` confirms that
  its half-power decay theorem assumes the explicit mixed-convolution
  coefficient bound; it is a receiver, not a producer. The proposed chain
  supplies neither that hypothesis nor the PM centered discrepancy bound.
  Partial=false;63871 files; generation1174066,coverage/current1174067;
  semantic coverage unmeasured, background refresh incomplete.
- Scratch1068 passed with empty Lean output after explicit real/complex
  casts and `HasSum.congr_fun` fixed the initial elaboration errors.
  Promoted `PMPowerDampedMobiusNymanSeries` (95 lines /11 declarations),
  wired its import, and started targeted build/audits. The centered source
  is exactly the pointwise absolutely summable damped Nyman series, with
  convergent integer prefixes; the density is proved real. Pointwise
  absolute convergence is not a global L2 bound.
- Search1070 (`centered summatory inverse square energy discrete cumulative
  kernel`, deep): reviewed all20 candidate/all20 source statements and both
  proposed ingredient steps. Inverse-square summability does not control
  the unbounded cumulative coefficient. The other energy statements use
  different carriers or retain their energy hypotheses. No exact PM
  discrete bridge or missing arithmetic bound returned. Partial=false;
  63873 files; generation1174119,coverage/current1174126; semantic coverage
  unmeasured, background refresh incomplete.
- Direct inspection of `StepFunctionCarrier` found `integral_tailCell_stepGramIntegrand`
  and the disjoint unit-cell partition. Its existing global `hasSum_stepGram`
  assumes a bounded sequence and cannot be applied to the actual D_epsilon.
  The paper bridge above needs the unrestricted integrability/summability
  equivalence, with cellwise integrability proved before countable assembly.

- PM-31 literal Nyman-series leaf fully audited:
  `PMPowerDampedMobiusNymanSeries` (95 lines /11 declarations), targeted old
  build34s, final actual leaf empty, every exact-body/name/API/unique-import/
  standard-axiom gate passed. The centered discrepancy is the negative
  damped fractional-part series, pointwise absolutely summable at every
  positive damping and positive physical time. Its natural integer prefixes
  converge pointwise to the actual centered source; the density is real.
  Combined: twenty-five leaves /5916 lines /439 audited declarations.
  Global lint: eleven unrelated unwired modules and three concurrently stale
  generated files; no owned/proof-debt finding. The actual small-positive
  dyadic/cumulative energy bound remains open. Next: exact unrestricted
  discrete weighted-energy/covariance bridge, then the signed arithmetic
  bound. No global L2 interchange or RH/negRH proof is asserted.

- Scratch1071 formalizes the unrestricted step-energy bridge: prove each
  unit-cell integrable using a bounded constant comparison, then assemble
  cells by summable integrals of norms. No bound on the actual cumulative
  sequence is assumed. The centered divisor remainder is exactly the
  floor-indexed cumulative discrepancy minus density times fractional
  part; the latter divided by x is L2 on x>1. The interval 0<x<1 has finite
  energy separately. This gives the exact actual-source admission iff
  summable weighted cumulative squares, equivalently a uniform bound on
  finite signed covariance. The bound itself remains open below 1/2.
  Final scratch check running; no new audited leaf claimed yet.

- Scratch1071 passed with empty diagnostics. Promoted and wired
  `PMPowerDampedMobiusDiscreteEnergy` (224 lines /18 declarations); exact
  source bodies, exhaustive name/API entries, unique import and proof-debt
  checks passed. Targeted build and final leaf/axiom gates pending.
- Search1072 (`damped divisor centered cumulative covariance signed
  cancellation`, deep): reviewed all20 candidate/all20 source statements
  and both generated ingredient steps. Existing cumulative covariance is
  an exact finite identity, already used here. Probabilistic covariance
  sum formulas assume input L2 and give no bound; Deninger prime Gaussian
  Mellin facts concern a different carrier. Damped-Mobius zero-free
  results retain the required summatory bound. No actual energy producer
  returned. Partial=true: filter_and_judge returned incomplete/malformed
  local-model JSON. 63884 files; generation1174334,coverage/current1174350;
  semantic coverage unmeasured; background refresh incomplete. Follow-up
  lexical cumulative/covariance search started.
- Search1073 (`"cumulative" "covariance"`, lexical, uncapped per module):
  all7 hits in2 modules read. Five are the known cumulative energy/kernel
  or finite deletion error identities; the modular centered-divisor identity
  also retains finite deletion cutoffs. The Gamma valuation primitive
  covariance concerns a different carrier. No bound on the PM sequence;
  lexical output has no coverage/freshness fields.
- Targeted `--old` leaf build passed (143s). Global formal lint reports
  eleven unrelated unreachable modules, including the concurrent
  `WeilFullConeHorizontalPotential` leaf; no PM leaf or proof-debt finding.
  Final actual-leaf Lean audit running, followed by all-declaration axioms.

- PM-31 unrestricted discrete-energy leaf fully audited:
  `PMPowerDampedMobiusDiscreteEnergy` (224 lines /18 declarations), targeted
  old build143s, final actual leaf empty, every exact-body/name/API/unique-
  import/standard-axiom gate passed. Unit-cell integrability and countable
  assembly remove the old bounded-sequence premise. For every epsilon>0,
  actual canonical admission is equivalent to summability of
  D_epsilon(n)^2/(n(n+1)), where D is the cumulative centered divisor
  coefficient. Equivalently, its exact finite signed maximum-index
  covariance has a common bound in the cutoff. The epsilon>=1/2 range is
  unconditional; cofinal small-positive budgets would imply RH but remain
  unproved. Combined: twenty-six leaves /6140 lines /457 audited declarations.
  Global lint reports eleven unrelated unreachable modules; no owned or
  proof-debt finding. No RH/negRH proof is claimed.
- Search1074 (`Mobius weighted fractional part Gram off diagonal
  cancellation integer cutoff`, deep): all20 candidate/all20 source
  statements and both generated ingredient steps reviewed. The off-diagonal
  large-sieve estimate carries an N log N cost; finite weighted cutoff
  diagonals and factorial-period formulas are identities, not uniform
  bounds. The proposed zeta-Mobius interpolation cancellation has different
  inputs; the paired physical conditional quotient explicitly leaves its
  signed numerator unbounded. Partial=false; 63884 files;
  generation1174371,coverage/current1174376; semantic coverage unmeasured,
  background refresh incomplete.
- Search1075 (`"predictableDrift" "energy"`, lexical, uncapped per module,
  offset20 follow-up): all28 hits in15 modules read, including all4
  exploration hits. High-clock drift layers have unconditional vanishing
  tails, but low-clock projection bounds retain the arithmetic source.
  Reverse-tail, beta-resolvent, and truncated-divisor formulas are exact
  identities, not producers. Direct inspection of
  `EulerDeletionResidueMartingaleL2Limit` confirms the stronger existing
  unconditional signed-innovation strong L2 limit even at zero damping.
  Re-proving damped innovation admission would not advance this frontier.
  The undamped predictable drift is not uniformly integrable in L2;
  this does not refute actual positive-damping admission. Lexical output
  has no coverage/freshness fields.
- Search1076 (`"Chebyshev" "sign"`, lexical): all21 displayed hits read.
  They concern polynomial Chebyshev identities, conditional prime-error
  estimates or different signed sources; none gives a sign bound for the
  actual dyadic tangent. No sign/pointwise-order claim made.
- Search1077 (`power damped Mobius source derivative vonMangoldt dilation
  flow`, deep): all20 candidate/all20 source statements and both proposed
  ingredient steps reviewed. Projective Mobius derivatives are unrelated;
  vonMangoldt prime identities do not supply a canonical energy estimate.
  Known PM generator/prime-aperture estimates retain the half-damping
  threshold. Partial=false; 63889 files; generation1174482,
  coverage1174488/current1174489; semantic coverage unmeasured and refresh
  incomplete. A formal damping-flow wrapper would not close the producer.
- New direct paper obstruction/survivor: the actual positive-divisor Haar
  prefixes have a deterministic concentration near t=0 and unbounded L2
  energy at every epsilon>0. Their rescaled profile and exact leading
  energy are recorded in
  [pm-positive-divisor-haar-boundary-profile.md](../5-failed/pm-positive-divisor-haar-boundary-profile.md).
  This rejects an approximant budget, not actual-source admission; the
  centered discrete energy producer above remains open.

- PM-31 positive-divisor Haar prefix leaf fully audited:
  `PMPowerDampedMobiusPositiveHaarPrefix` (239 lines /21 declarations),
  targeted old build64s, final actual leaf empty, all exact-body/name/API/
  unique-import/proof-debt/standard-axiom gates passed. The exact clipped
  counts give stabilization to the actual source and the initial plateau
  -C_epsilon(N), with energy contribution C_epsilon(N)^2/(2N). Rescaled
  prefixes converge pointwise to alpha_epsilon times the universal boundary
  profile beta, with common 3min(1,1/u) envelope. Each finite prefix has zero
  integral. Combined: twenty-seven leaves /6379 lines /478 declarations.
  Strong L2 profile/leading energy is checking in scratch1080; do not retire
  this cutoff candidate until that positive survivor is fully audited.
  Actual small-positive source admission and RH remain open. Global lint:
  eleven unrelated unwired modules and concurrent generated-document
  staleness, no owned or proof-debt finding.

- PM-31 universal boundary profile fully audited: `PMPowerDampedMobiusHaarBoundaryProfile`
  (292 lines /19 declarations), targeted old build46s, final actual leaf
  empty, all exact-body/name/API/unique-import/proof-debt/standard-axiom
  gates passed. Rescaled raw positive-Haar prefixes converge strongly in
  L2 to alpha_epsilon*beta; integral beta^2=2-2log2 and integral beta=-log2.
  Their energy divided by the cutoff tends to the strictly positive
  |alpha_epsilon|^2*(2-2log2), so raw-prefix common budgets fail at EVERY
  positive damping. Their L1 error is at least |alpha_epsilon*log2|.
  This does not refute actual-source admission. The exact positive survivor
  closes this no-go; the raw cutoff card is retired. Combined: twenty-eight
  leaves /6671 lines /497 audited declarations. Follow-up: centered Haar
  cutoff/endpoint-trace criterion; the small-positive signed energy
  producer and RH remain open. Global lint: eleven unrelated unwired
  leaves and concurrently stale generated docs, no owned/proof-debt finding.

- PM-31 clipped Haar source fully audited: `PMPowerDampedMobiusClippedHaarSource`
  (242 lines /22 declarations), targeted old build49s, final actual leaf
  empty, all exact-body/name/API/unique-import/proof-debt/standard-axiom
  gates passed. Subtracting alpha_epsilon*N*beta(Nt) gives exactly the
  dyadic difference of R_epsilon(min(N,1/t)); every finite corrected
  prefix is admitted and stabilizes pointwise to the actual source.
  Its primitive energy is exactly truncated divisor energy plus
  |R_epsilon(N)|^2/N. Generic dyadic difference norms lie between
  (sqrt2-1)||f|| and (sqrt2+1)||f||. Combined: twenty-nine leaves /6913
  lines /519 audited declarations. The endpoint convergence and cofinal
  selection proofs are in scratch, not yet certified. Small-positive
  arithmetic admission remains open. Global lint: ten unrelated unwired
  modules and stale LEAN_GAPS/LEAN_OVERVIEW, no owned/proof-debt finding.

- Search1085 (`renormalized positive divisor Haar covariance density
  subtraction signed energy bound`, deep): all20 candidate/all20 source
  statements, both proof ideas and both generated ingredient steps
  reviewed. No repaired-PM covariance bound returned. The product-fibre
  theorem is an exact finite Gamma-Hankel identity, not a uniform estimate;
  Suzuki's nonnegative divisor log kernel has different coefficients.
  The generated N1 signed-energy and Xi-zero divisor chain mismatches
  this carrier and supplies no bound. Partial=false; 63926 files;
  index1175345,coverage1175361/current1175362; semantic coverage
  unmeasured and background refresh incomplete. This search does not
  justify an arithmetic admission claim.
- Search1086 (`"haarWeight"`, lexical) returned exactly two declarations
  in one module; both statements and the entire 89-line
  `MobiusHaarRamareCoprimalityBudget` source reviewed. Its correction
  bound is at most the cofactor cutoff R, obtained from normalization by
  one plus the number of prime divisors. It controls only the coprimality
  correction, not the full signed prime-cofactor source or centered
  energy. No coverage snapshot supplied in this lexical result.
- Search1087 (`generalized totient summatory Mobius weighted remainder
  square energy`, deep, excluding PMPowerDampedMobius): all20 candidate/
  all20 source statements and both generated ingredient steps reviewed.
  Totient normalization identifies only the known epsilon=1 coefficient;
  physical source energy increments and GCD-Gram factorizations are exact
  identities with the signed cross term still present. The generated
  angular-forcing remainder chain uses a different carrier. No actual
  small-positive discrepancy energy bound returned. Partial=false;
  63929 files; index1175414,coverage1175432/current1175435; semantic
  coverage unmeasured and background refresh incomplete.
- Full 129-line `LogarithmicCoprimeEnergy` source audit: its Möbius
  reconstruction theorem is a signed coprime-pair identity. The endpoint
  square is accompanied by the complete off-diagonal cross term; no
  positivity or bound for that cross term is proved. It supplies no
  additional estimate for the PM centered energy.

- PM-31 cutoff trace/cofinal criterion fully audited:
  `PMPowerDampedMobiusHaarCutoffTrace` (324 lines /16 declarations),
  targeted old build15s, final actual leaf empty, all exact-body/name/API/
  unique-import/proof-debt/standard-axiom gates passed. Under actual
  admission, both clipped-primitive and density-repaired-prefix L2
  convergence are equivalent to |R_epsilon(N)|^2/N tending to zero.
  Actual admission supplies a strict cofinal trace-zero sequence, and is
  equivalent to a common cofinal repaired-prefix norm budget. The exact
  criterion card moves to formalized. Combined: thirty leaves /7237 lines
  /535 audited declarations. Full-sequence endpoint-atom correction is
  the next paper-proved conjecture; actual small-positive energy admission
  and RH remain open. Global lint: ten unrelated unwired leaves, all three
  generated docs concurrently stale, no owned/proof-debt finding.
- Search1090 (`predictable drift density boundary correction power damped
  Mobius source`, deep, module EulerDeletion): all20 candidate/all20
  source statements and both generated ingredient steps reviewed.
  High-clock bounds retain an N^2/clock factor and leave the low-clock
  source projection unbounded. Physical norm comparisons transfer the
  same missing drift estimate; the generated chain does not produce it.
  Composite increments are exactly predictable. Existing drift non-L2
  convergence statements concern the undamped natural prefixes, not the
  new endpoint-corrected positive-damping family. No actual damped drift
  bound or identification with only the removed endpoint packet returned.
  Partial=false; 63935 files; index1175601,coverage/current1175617;
  semantic coverage unmeasured and background refresh incomplete.
- Search1091 (`generalized totient pair correlation centered cumulative
  discrepancy variance`, deep, excluding PMPowerDampedMobius): all20
  candidate/all20 source statements and both generated ingredient steps
  reviewed. The returned prime-log aperture discrepancies, fixed-core
  divisor correlation blocks and Fourier-window correlations use other
  carriers. The square-prime-window subpower result explicitly assumes
  RH. The generated variance/discrepancy chain does not establish the
  needed identification or estimate. No centered c_epsilon pair-correlation
  bound returned. Partial=false; 63939 files; index1175693,
  coverage1175705/current1175706; semantic coverage unmeasured,
  background refresh incomplete. Lexical follow-up1092 narrows totient
  correlation before choosing an arithmetic covariance conjecture.
- Search1092 (`totient correlation`, lexical, no per-module cap) returned
  five declarations in four modules; all five complete source statements
  reviewed. The phase sum is bounded by a totient, the character L1
  moment retains its full diagonal cost, the theta Hankel transform has
  a different analytic carrier, and the cofactor identity leaves a literal
  reduced-residue discrepancy. None estimates centered c_epsilon pairs.
  No coverage snapshot supplied. Follow-up1093 checks the coefficient's
  second-moment density as a calibration of any covariance argument;
  such a density is not an anchored-prefix energy estimate.

- Endpoint correction fully audited: `PMPowerDampedMobiusEndpointHaar`
  (215 lines /17 declarations), targeted old build294s, final actual-leaf
  check with empty diagnostics, all17 standard-axiom reports, exact body,
  exhaustive names/API, unique import and proof-debt checks passed. Its
  exact truncated-source identity removes the endpoint trace, giving
  full-integer-cutoff L2 convergence under actual admission and an exact
  full-sequence energy-budget criterion. Global lint still reports twelve
  unrelated unwired leaves, no owned/proof-debt issue. Combined: thirty-one
  leaves /7452 lines /552 audited declarations. The actual small-positive
  signed energy bound remains open. Next: divisor second-moment density.

- Search1093 (`power damped divisor coefficient second moment density`,
  deep, excluding PMPowerDampedMobius): all20 candidate statements, all20
  source arguments and both generated ingredient steps reviewed. No exact
  arithmetic mean-square density returned. Divisor-polynomial fourth
  moments retain the full off-diagonal; the proposed chain does not bound
  it. The finite-gcd divisor-moment result uses an lcm pair kernel and may
  inform finite-prime means, but is not the requested signed density.
  Other hits concern different damping carriers. Partial=false;63941files;
  index1175738, coverage/current1175759; semantic coverage unmeasured,
  background refresh incomplete. No exhaustive novelty claim.
