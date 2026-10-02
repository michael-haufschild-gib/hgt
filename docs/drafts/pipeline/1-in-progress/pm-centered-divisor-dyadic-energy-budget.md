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

- Second-moment density fully audited: `PMPowerDampedMobiusSecondMoment`
  (268 lines /18 declarations), targeted old build36s, final actual-leaf
  check with empty diagnostics, all18 standard-axiom reports, exact body,
  exhaustive names/API, unique import and no-proof-debt checks passed.
  It proves the literal coefficient square's summatory mean and Euler
  product, the centered mean-square gamma-alpha^2>=0, and gamma<=alpha.
  Combined: thirty-two leaves /7720 lines /570 audited declarations.
  Strict positivity, small-damping variance and the logarithmic signed
  covariance calibration remain on the second-moment card. The actual
  small-positive cumulative-energy bound and RH remain open. Global lint
  has eleven unrelated unwired leaves and three generated freshness
  findings; no owned or proof-debt finding, no global pass claimed.

- Signed covariance calibration fully audited:
  `PMPowerDampedMobiusCovarianceCancellation` (269 lines /17 declarations),
  targeted old build7.8s, final actual-leaf check with empty diagnostics,
  all17 standard-axiom reports, exact body, exhaustive names/API, unique
  import and no-proof-debt checks passed. The variance is strictly positive
  at every positive damping. The actual centered diagonal/log N tends to
  this variance and has no common finite budget, including the admitted
  safe range. The exact off-diagonal/log N tends to its negative under
  actual admission, unconditionally at epsilon>=1/2. Combined: thirty-three
  leaves /7989 lines /587 audited declarations. Small-damping variance
  asymptotic is drafted; the canonical small-positive energy bound and RH
  remain open. Global lint has twelve unrelated unwired leaves and stale
  API/overview, no owned/proof-debt finding; no global pass claimed.

- Search1101 (`power damped divisor Ramanujan expansion anchored cumulative
  covariance`, deep, excluding PMPowerDampedMobius): all20 candidate/all20
  source statements and both generated steps reviewed. No matching
  anchored coefficient expansion/control returned. The sieve damped
  correlation Euler bound concerns a finite absolute correction factor;
  Li even-cross damped endpoints use another clock source. The generated
  chain combines these different carriers and supplies no PM bound.
  The character-level ramSum expansion also has a different coefficient
  family. Partial=false;63963files;index1176517,coverage/current1176525;
  semantic coverage unmeasured and background refresh incomplete. Refine
  the expansion query without damping terms before choosing a new producer.

- Search1102 (`Ramanujan expansion mean square coefficients`, deep)
  returned no candidates or source arguments: the semantic engine failed
  with `sqlite3.OperationalError: database is locked`. Partial=true;
  two stages unfinished and no usable coverage. This is no evidence of
  absence. Search1103 broadens to `Ramanujan mean square coefficients`
  with `--any`; no new producer is accepted from the failed search.

- Search1103 (`Ramanujan mean square coefficients`, deep, `--any`):
  all20 candidate/all20 source statements, lexical summaries and both
  proposed ingredient steps reviewed. The literal Ramanujan divisor
  convolution is applicable arithmetic infrastructure. The separate
  quadratic-phase, Kloosterman, Jacobi, and short-window variance bounds
  retain different sources or correlation hypotheses. Bohr mean-square
  approximation does not bound energy at the fixed integer origin. The
  generated chain leaves its norm bound unresolved; no PM producer follows.
  Partial=true; text/source retrieval and judging unfinished; background
  refresh incomplete. Search1104 narrows to the divisor expansion itself.

  Coverage for1103:63965files; index1176648, coverage1176693/current1176695;
  semantic coverage unmeasured. Retrieval was interrupted and the local
  judge returned incomplete/malformed JSON. Candidate applicability was
  assessed from the actual displayed statements, not the judge's verdict.

- Next explicit candidate:
  [natural-denominator Ramanujan energy](pm-ramanujan-denominator-energy.md).
  First audit and prove the actual
  coefficient expansion with absolute rearrangement. The proposed common
  anchored energy budget remains unproved; finite-prime and averaged
  substitutes are explicitly excluded. Search1104 is still running.

- Small-damping variance refinement fully audited:
  `PMPowerDampedMobiusSmallDampingVariance` (251 lines /17 declarations),
  targeted old build76s, final actual-leaf check with empty diagnostics,
  all17 standard-axiom reports, exact body, exhaustive names/API, unique
  import and no-proof-debt checks passed. The exact Euler correction
  tends to one; gamma_epsilon/epsilon and v_epsilon/epsilon both tend to
  1/2 as epsilon->0+. All pole identities use positive damping.
  Combined: thirty-four leaves /8240 lines /604 audited declarations.
  The coefficient second-moment card is now formalized; the actual
  small-positive cumulative-energy bound and RH remain open. Global lint
  reports ten unrelated unwired leaves, no generated freshness error and
  no owned/proof-debt finding; no global pass claimed. Next candidate:
  natural-denominator Ramanujan expansion and its anchored energy budget.

- Actual Ramanujan expansion fully audited:
  `PMPowerDampedMobiusRamanujanExpansion` (245 lines /21 declarations),
  targeted old build37s, final actual-leaf check with empty diagnostics,
  all21 standard-axiom reports, exact body, exhaustive names/API, unique
  import and no-proof-debt checks passed. The literal coefficient has an
  absolutely convergent Ramanujan expansion; centered natural-denominator
  prefixes converge, as do every fixed cumulative sum and finite energy.
  A common cutoff-energy budget would give actual PM admission, but that
  budget remains unproved. Combined: thirty-five leaves /8485 lines /625
  audited declarations. Global lint reports eleven unrelated unwired
  leaves and stale API/overview, no owned/proof-debt finding; no global
  pass claimed. The explicit multiple-weight Euler formula has a paper
  proof and a draft Lean proof, not yet checked. RH remains open.

- Actual Ramanujan weights fully audited:
  `PMPowerDampedMobiusRamanujanWeights` (230 lines /17 declarations),
  targeted old build160s, final actual-leaf check with empty diagnostics,
  all17 standard-axiom reports, exact-body/exhaustive names/API/unique
  import/no-proof-debt checks passed. The coefficient is exactly
  alpha*mu(q)/product_(p|q)(p^(1+epsilon)-1), is real with Mobius-aligned
  sign, and has total absolute mass one. These are unconditional for
  every positive damping, including nonsquarefree vanishing and q=0.
  Combined: thirty-six leaves /8715 lines /642 audited declarations.
  Global lint reports twelve unrelated unwired leaves, no owned or
  proof-debt finding; no global pass claimed. The finite cofactor rewrite
  is checking next. No small-positive anchored energy budget or RH proof.

- Actual Ramanujan cofactors fully audited:
  `PMPowerDampedMobiusRamanujanCofactors` (286 lines /18 declarations),
  targeted old build49s, final actual-leaf check with empty diagnostics,
  all18 standard-axiom reports, exact-body/exhaustive names/API/unique
  import/no-proof-debt checks passed. Natural-denominator cumulative
  prefixes are exactly finite cofactor-weighted fractional-part sums,
  with exact density cancellation. Absolute multiples inversion gives
  the exact mass on squarefree multiples; cofactors preserve Mobius
  signs and have norm at most d^(-epsilon). Combined: thirty-seven
  leaves /9001 lines /660 audited declarations. Global lint has ten
  unrelated unwired leaves and no owned/proof-debt finding; no global
  pass claimed. A proposed logarithmic coefficient-square comparison
  remains unproved; its summable coefficient side is being checked.
  No small-positive anchored energy budget or RH proof.

- Actual Ramanujan logarithmic square mass fully audited:
  `PMPowerDampedMobiusRamanujanLogMass` (59 lines /5 declarations),
  targeted old build47s, final actual leaf empty, all5 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. Pointwise |a(q)|<=q^(-1-epsilon); the proposed
  logarithmic square mass is dominated by
  (2^epsilon/epsilon)*q^(-1-epsilon), hence summable for every positive
  damping. Combined: thirty-eight leaves /9060 lines /665 audited
  declarations. Global lint has eleven unrelated unwired leaves, no
  owned/proof-debt finding; no global pass claimed. The energy
  comparison remains unproved. The actual primitive-period mean is
  the next check; no small-positive energy bound or RH proof.

- Actual Ramanujan primitive fully audited:
  `PMPowerDampedMobiusRamanujanPrimitive` (206 lines /18 declarations),
  targeted old build37s, final actual leaf empty, all18 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. The primitive is periodic and bounded for q>1. Its
  exact period mean is -phi(q)/2, also its Cesaro and logarithmic
  harmonic limits. Combined: thirty-nine leaves /9266 lines /683
  audited declarations. Global lint has twelve unrelated unwired
  leaves, no owned/proof-debt finding; no global pass claimed. The
  fixed-q prime Gram asymptotic is checking next. No common cutoff
  energy comparison, small-positive admission or RH proof.

- Actual primitive Gram fully audited:
  `PMPowerDampedMobiusRamanujanGram` (188 lines /13 declarations),
  targeted old build9.9s, final actual leaf empty, all13 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. Every fixed pair is absolutely summable; for fixed
  q>1, K(p,q)/log(p)->phi(q)/2 along primes. The exact harmonic head
  has a tail error bounded by the finite-period primitive norm bound.
  Combined: forty leaves /9454 lines /696 audited declarations.
  Lint1129 has fourteen unrelated unwired modules and two shared
  generated-file staleness findings after concurrent changes; no owned
  or proof-debt finding and no global pass claimed. Finite signed Gram
  reduction draft1128 is next; common quadratic bound, small-positive
  admission and RH remain unproved.

- Actual finite signed Ramanujan quadratic fully audited:
  `PMPowerDampedMobiusRamanujanQuadratic` (107 lines /12 declarations),
  targeted old build238s, final actual leaf empty, all12 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. Each fixed natural denominator cutoff has finite
  total energy equal to its exact signed primitive Gram quadratic.
  The common Q,T energy budget is equivalent to a common Q bound
  on those literal quadratic forms. Combined: forty-one leaves
  /9561 lines /708 audited declarations. Lint1132 has ten unrelated
  unwired modules and three shared generated-file staleness findings;
  no owned/proof-debt finding and no global pass claimed.
  First-moment/centering draft1133 is checking. Uniform quadratic
  upper bound, small-positive admission and RH remain unproved.

- Actual primitive reciprocal first moment fully audited:
  `PMPowerDampedMobiusRamanujanMoment` (200 lines /17 declarations),
  targeted old build43s, final actual leaf empty, all17 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. The primitive first moment under reciprocal energy
  weights is exactly -Lambda(q), and their mass is1. Period centering
  yields the explicit totient/Lambda correction; energy centering
  R_q+Lambda(q) has weighted mean0 and splits K into Lambda(p)*Lambda(q)
  plus its centered Gram. Combined: forty-two leaves /9761 lines /725
  audited declarations. Lint1135 has eleven unrelated unwired modules
  and two shared generated-file staleness findings; no owned/proof-debt
  finding and no global pass claimed. Actual finite variance reduction
  and centered mixed-Gram law draft1136 are checking. No uniform actual
  variance bound, small-positive admission or RH proof.

- Actual finite energy-centered variance fully audited:
  `PMPowerDampedMobiusRamanujanVariance` (129 lines /12 declarations),
  targeted old build43s, final actual leaf empty, all12 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. Actual weighted mean M has a common finite bound at
  each positive damping; G=M^2+V with V>=0, and common Gram/variance
  budgets are equivalent. Centered prime Gram/log(p) tends to
  phi(q)/2-Lambda(q), so logarithmic cross terms survive centering.
  Combined: forty-three leaves /9890 lines /737 audited declarations.
  Lint1139 has twelve unrelated unwired modules and two shared
  generated-file staleness findings; no owned/proof-debt finding and
  no global pass claimed. Absolute natural-cutoff control for damping
  above1/2 is checking in draft1140. Uniform small-positive variance
  upper bound, admission and RH remain unproved.

- Strict absolute natural-denominator budget fully audited:
  `PMPowerDampedMobiusRamanujanAbsolute` (111 lines /7 declarations),
  targeted old build103s, final actual leaf empty, all7 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. Common Q,T energy, Gram and centered-variance bounds
  hold for epsilon>1/2 by the exact cofactor fractional-part bound and
  two convergent power sums. No assertion at epsilon<=1/2.
  Combined: forty-four leaves /10001 lines /744 audited declarations.
  Lint1144 has ten unrelated unwired modules; no owned/proof-debt
  finding and no global pass claimed. Endpoint transfer via finite
  Dirichlet convolution remains a paper candidate. Small-positive
  admission and RH remain unproved.

- Exact finite Ramanujan-to-Mobius prefix transfer fully audited:
  `PMPowerDampedMobiusRamanujanTransfer` (132 lines /14 declarations),
  targeted old build55s, final actual leaf empty, all14 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. Cofactor Fermi prefix equals the triangular sum of
  actual dilated Mobius prefixes with the explicit convolution kernel;
  no norm bound inferred before the kernel-mass audit.
  Combined: forty-five leaves /10133 lines /758 audited declarations.
  Lint1150 has ten unrelated unwired modules and three shared generated
  file staleness findings; no owned/proof-debt finding, no global pass.
  Kernel prime-factor formula is checking in draft1149. Endpoint and
  small-positive natural-cutoff budgets remain open; RH unproved.

- Exact transfer kernel prime-factor/norm formula fully audited:
  `PMPowerDampedMobiusRamanujanKernel` (196 lines /14 declarations),
  targeted old build62s, final actual leaf empty, all14 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. The norm kernel equals |A(m)|*r^(-epsilon) times
  product_(p|r)(if p|m then 1 else 1/(p^(1+epsilon)-1)); the finite
  product lies in [0,1]. No squarefree premise on m is needed.
  Combined: forty-six leaves /10329 lines /772 audited declarations.
  Lint1156 has ten unrelated unwired modules and three shared generated
  file staleness findings; no owned/proof-debt finding, no global pass.
  Combined mass/Euler/budget draft1157 is checking. Uniform transfer
  norm and endpoint natural-cutoff energy remain unproved; RH unproved.

## Direct producer audit — 2026-10-01

Route PM's hard target remains finite cumulative discrepancy energy at
cofinally small positive damping. The kernel-mass extension on the Ramanujan
card does not lower the admitted damping threshold. A half-damping endpoint
extension was withdrawn before compilation because it would not attack this
hard target. No new receiver or equivalent reformulation will be counted as
producer progress.

The existing coprime/gcd head results were checked at their literal source
statements. `DeletionGcdHead.exists_total_initialEnergy_harmonic_remainder_subpower`
controls the initial head only after retaining
`headMass(N)*deningerHarmonicPartial(N)^2`. Its final theorem is a LOWER
bound for complete primitive energy, not the missing upper bound.
`DeletionMobiusGlobal.primitiveEnergy_le_of_mertens` retains the complete
cost `N/L` and `N*L*(|H_N|+2*eta*L)^2`. Making `N/L` subpower requires
polynomial L, which fixed logarithmic savings for eta do not support.
Consequently no exponent improvement follows from composing these results.
This rejects this proof attempt, not the direct PM energy conjecture.

Search07 (deep, full corpus) was partial: reranking deadline; all 20 displayed
candidates and 20 source entries reviewed. Its Fourier-inversion ingredient
has an unrelated carrier and no cutoff energy bound. Search10 (PM filtered)
completed: all 20 candidates and 20 source statements reviewed. It returns
exact covariance, mean/variance, and conditional admission statements, not
an unconditional small-damping upper bound. Semantic coverage unmeasured.

### Next conjecture: descent in damping, tested before formalization

For each `0<epsilon<1/2`, conjecture a finite-cutoff signed estimate comparing
the actual epsilon source with the actual 2epsilon source, with a finite
constant depending on epsilon but independent of cutoff. A family that
preserves L2 admission under halving would descend from the established
one-half endpoint to a cofinal sequence and reach the existing RH receiver.
It must apply to the full source, including the cutoff-complement terms.

Exact coefficient algebra gives the proposed starting point:
`w_(2epsilon) = w_epsilon * g_epsilon`, where
`w_epsilon(n)=mu(n)n^(-epsilon)` and
`g_epsilon(n)=n^(-epsilon)c_epsilon(n)>=0`.
At a prime-power variable X the inverse factor is
`(1-p^(-epsilon)X)/(1-p^(-2epsilon)X)`.
For k>=1 its coefficient is
`(1-p^epsilon)*p^(-2epsilon*k)`.
The absolute dilation-norm sum therefore has prime terms
`(p^epsilon-1)*p^(-2epsilon-1/2)`, so an absolute-value inverse estimate
again meets the half-damping barrier. Positivity of g alone does not prove
operator coercivity. A valid descent must exploit signed interaction with
the actual doubled-damping source. These are paper calculations only;
no new Lean theorem or established descent law is claimed.

Search11 (PM energy/doubling query) completed: all 20 candidate and 20 source
entries reviewed. It returned no descent estimate. Existing covariance
limits under admission cannot establish the admission premise. Next inspect
the exact signed inverse applied to the complete doubled-damping source;
reject any argument that exchanges unadmitted global L2 sums or assumes
zero-free shifted zeta to bound that inverse.

- Damping-descent check: for a fixed positive epsilon, the inverse prime
  term in the L2 dilation-norm sum is
  `p^(-epsilon-1/2)*(1-p^(-epsilon))`. For epsilon<=1/2 it dominates
  a constant multiple of 1/p at all sufficiently large primes. Thus
  a triangle-inequality inverse cannot start the descent. This is a
  paper diagnosis of the attempted bound, not a refutation of signed
  descent and not a new formalized no-go.
- Exact remaining test: retain the full quadratic cross terms in the
  inverse convolution on the actual doubled-damping prefixes. A useful
  estimate must bound their total independently of N in terms of the
  doubled-damping prefix norm, without assuming an epsilon-prefix norm.
  Merely bounding coefficient-square mass repeats the already-known
  diagonal-only failure. No supporting inequality has been found.
- Search15 (zeta quotient/inverse multiplier) completed; all 20 candidate
  and 20 source entries reviewed. Available inverse bounds concern Re(s)>1,
  a narrowing zero-free neighborhood of Re(s)=1, or other carriers. None
  bounds the required shifted inverse through the critical half-plane.
  A Mellin proof that assumes such a bound would leave the hard step
  unproved. No new lower-damping admission or RH conclusion.

### Producer loop: cutoff descent, windows, and logarithmic feedback

2026-10-01. No improvement to the admitted damping threshold in this loop.
The tests below eliminate proposed proof mechanisms; they do not establish
small-positive admission or refute RH.

1. **Prime-aperture-uniform damping descent is false.** At damping 3/4,
   every finite-prime source norm is at most
   `pmPrimeApertureAbsoluteBudget (3/4)`. At damping 3/8, canonical
   finite-prime source norms have no bounded cofinal subsequence.
   Consequently there is no nonnegative real C such that, for all N,
   `norm(F_(3/8,N)) <= C*(1+norm(F_(3/4,N)))`.
   A scratch theorem combining the two existing exact threshold results
   passed `lake env lean /tmp/pm_descent_prime_test18.lean`; its axiom
   report contained only `propext`, `Classical.choice`, `Quot.sound`.
   No duplicate leaf was added: the positive survivor is the already
   formalized sharp finite-prime threshold in
   `PMPowerDampedMobiusPrimeThreshold`. This rejects generic prime-product
   descent, not descent for the actual natural-cutoff source.

2. **Fixed-start window extraction does not supply the missing exponent.**
   `DeletionFirstTail.incrementEnergy_eq_signed_pair_kernel` and
   `strictOffDiagonalPairKernel_eq_shiftedOffDiagonalPairKernel` retain
   exactly the required signed correlations. Extracting one start from
   `dyadicMeanSquare` loses the averaging gain. The literal harmonic
   transfer has endpoint cost `2*l^4/(z+1)^2` at one start; with `l=z=N`
   this is of order N^2 before the reciprocal energy weight. Summing
   such costs over long windows does not give a subpower first-tail
   energy. The available Menon receiver also retains that cost and its
   frequency-head hypothesis. No pointwise cancellation follows by
   composing these statements.

3. **Positive/absolute logarithmic renewal does not close descent.**
   The candidate coefficient identity is
   `c_epsilon(n)*log n = sum_(d|n) Lambda(d)*(1-d^(-epsilon))*c_epsilon(n/d)`.
   Positivity of this kernel alone supplies no contraction at the
   critical energy weight. More concretely, the corpus's compensated
   Mobius renewal is `logSource = -dilationPackets-forcing`, and
   `DeletionLogPrimeForcing.linear_energy_bounds` proves the retained
   forcing has squared norm comparable to N. Removing it as a subpower
   error is invalid. A new recurrence must estimate its joint signed
   interaction, not the separate positive pieces.

**Next direct candidate: one-sided damping derivative, with the actual
spatial cutoff retained.** Let
`E_N(epsilon)=integral_(1/N)^1 |A_epsilon(t)|^2 dt`, N>=1. Finite
coefficient differentiation and the Mobius/von Mangoldt convolution
suggest the exact finite-domain identity
`E_N' = 2 sum_(q<=N) Lambda(q)*q^(-epsilon)*
Re integral_(1/N)^(1/q) conj(A_epsilon(t))*A_epsilon(q*t) dt`.
The identity is a paper calculation, not a new audited Lean result.
The proposed producer is: on every compact interval `[a,1/2]`, a>0,
find a cutoff-independent C_a with
`E_N'(epsilon) >= -C_a*(1+E_N(epsilon))`.
Backward Gronwall from the existing half-damping admission would then
give the required bound for every positive epsilon. No such lower form
bound has been proved. Cauchy--Schwarz separately at each dilation
again incurs `sum_(q<=N) Lambda(q)*q^(-epsilon-1/2)` and cannot close
the small-damping range. The next test must retain signed prime-scale
correlations and endpoint terms. Do not formalize only this receiver
and count it as progress.

Search audit: search16/17 (damping descent / signed Gram) completed;
20 candidates and 20 source statements each reviewed. Search19
(fixed-origin windows, deep full corpus) was partial with a semantic
deadline and malformed local-model response; its 20+20 available hits
were reviewed, then lexical search20 supplied the exact window and
Menon declarations. Search21/22 (PM covariance / von Mangoldt renewal)
completed with 20+20 each. Search23 (derivative form bound) was partial
at decomposition, with 12 candidates and 13 source statements; its
proposed ingredient group changes to a deleted-prime carrier and does
not establish a lower derivative bound. Search24/25 (prime feedback /
source lower sign) completed with 20+20 each. No listed result proves
the proposed source-specific lower form bound. Semantic coverage was
unmeasured; search19 and search25 also reported older coverage snapshots.

Search26 (Mellin moment cancellation) completed with 20+20 hits. The
existing unconditional transform requires `Re(s)+epsilon>1`; the cleared
identity throughout `Re(s)>1/2` assumes L2 admission. Therefore substituting
`s=1-epsilon` into the latter before proving admission would be circular.
Search27 (one-sided autocorrelation / Landau) was partial at reranking;
20+20 hits and its proposed ingredient group were reviewed. Its CCM
estimate assumes `PsiRemainderSquareRootBounded` and concerns a different
test family. Neither a uniform negative-part bound for the actual source
nor a `1/q` lower bound for its individual dilation correlations has been
proved or disproved here. The working target remains the complete signed
sum in `E_N'`; no termwise sign is assumed.

### Signed derivative attempt: zero endpoint versus positive damping

2026-10-01. The lower derivative estimate is still unproved. No new
source-tree theorem, admission, or exponent improvement in this turn.

The known Hilbert-tangent obstruction does not itself refute this
candidate. At each fixed N>=2, finite-sum differentiation is valid on
`[1/N,1]`. Since `A_0=Haar`, `D=A'_0` vanishes on `(1/2,1]`, and Haar
equals -1 below 1/2, it gives the paper identity
`E_N'(0)=-2*Re integral_(1/N)^(1/2) D(t) dt`.
The existing `integrable_pmDyadicChebyshevSource` and
`pmDyadicChebyshevSource_integral` therefore bound these derivatives
uniformly and give limit `-2*log 2`. This is a scalar first-variation
calculation, not an assertion that D is in L2. The latter is already
disproved. No new Lean audit of this calculation was performed.

The tempting positivity argument fails to deliver the required estimate:
`K_epsilon f=sum_q Lambda(q)*q^(-epsilon)*f(q*t)` has finite L1 operator
majorant `sum_q Lambda(q)/q^(1+epsilon)`, but the same dilation argument
in L2 costs `sum_q Lambda(q)/q^(1/2+epsilon)`. Thus L1 control or positive
coefficients cannot be used as the claimed cutoff-independent lower
quadratic bound. No semiboundedness of the actual-source form follows.

**Current stronger test, still open:** convexity of `E_N` on `[0,1/2]`,
uniformly for all N. Its endpoints are bounded (the Haar endpoint and
the established half-damping source), so convexity would close admission
at every intermediate damping. The exact finite-domain second variation
to sign is
`E_N''(epsilon)=2*integral_(1/N)^1 (|A'_epsilon|^2 +
Re(conj(A_epsilon)*A''_epsilon)) dt`.
Finite positive diagonal terms do not establish this sign; the mixed
term is retained. Neither convexity nor its negation was proved. Ordinary
log-convexity for positive Laplace coefficients does not apply to the
signed Mobius source. Do not add a conditional convexity receiver as a
substitute for proving this inequality.

A separate applicability test of the existing prime-window bounds also
fails to close the source estimate. The complete-source identity
`truncatedDivisorBlockKernel_sub_sourceEndpoint_eq_upperHalfPrimePackets`
requires `N<=2*(l+1)`. The unresolved low-clock projection retains small
l, of logarithmic size, where this condition fails for growing N. Its
general prime-packet bound alone does not cover the omitted composite
cofactors or endpoint source. No full-source estimate was inferred.

Search28 (derivative form) and search29 (convexity) completed with 20
candidate and 20 source statements each reviewed. They supplied no
applicable lower form or curvature bound. Lexical search30 located the
existing dyadic Chebyshev source and L1/non-L2 declarations. Search31
(low-clock/prime-window composition) completed with 20+20 hits, exposing
the incompatible upper-half condition above. Semantic coverage remained
unmeasured; the completed hybrid searches reported older snapshots.

### Curvature test: the signed prime-power term remains unpaid

2026-10-01. **No progress on the hard admission bound this turn.** No
new Lean module, lower damping threshold, or unconditional upper energy
estimate. Convexity is neither proved nor refuted; this attempt is not a
no-go theorem.

For the finite integration interval `[1/N,1]`, put
`K_epsilon(n)=Lambda(n)*n^(-epsilon)` and
`J_epsilon(n)=Lambda(n)*log(n)*n^(-epsilon)`. Finite differentiation and
the exact Mobius/logarithmic convolution identity give the paper formulas
`A'_epsilon=K_epsilon*A_epsilon` and
`A''_epsilon=(K_epsilon*K_epsilon-J_epsilon)*A_epsilon`, where convolution
acts by `f(t) -> f(n*t)` and terms with `n*t>1` vanish.
Consequently the curvature to control is the complete signed form
`||K_epsilon*A_epsilon||_N^2 +
Re <A_epsilon,(K_epsilon*K_epsilon-J_epsilon)*A_epsilon>_N`.

The arithmetic coefficient in the second term has an exact sign split:
at `n=p^a`, `a>=1`, it is `-(log p)^2*n^(-epsilon)`; at
`n=p^a*q^b`, distinct primes and positive exponents, it is
`2*log p*log q*n^(-epsilon)`; it vanishes with three or more distinct
prime factors and at 1. The existing
`HTGeometry/VonMangoldtSelfConvolution.lean` already proves the required
one-prime, two-prime, and support formulas. Positive two-prime
coefficients multiply signed source correlations, so their positivity
does not pay the negative prime-power term. No new compensation
inequality was found. Taking absolute values again gives the known
half-damping barrier.

Applicability checks: the retrieved causal multiplier derivative bounds
are on `Re z>=0`, where their zeta arguments have real part at least 1;
they do not supply a bound on the PM critical line. The corrected coarea
mass balance retains a nonnegative variance term, but gives no upper
bound for this PM form. A statement only at each fixed epsilon would
also leave the moving regime `epsilon*log N` bounded untreated.

Search32 was partial (semantic deadline); search33 completed without
reported errors; search34 was partial (semantic deadline). All returned
candidate/source statements and proposed ingredient groups were checked
for applicability; none supplies the missing signed inequality.
Search35, for an actual-source unit budget, was partial at reranking and
returned no applicable producer. Its residue-prediction and reflected
zero-energy suggestions concern different carriers. Compiler coverage
was mostly pending or stale, so retrieval is not a Lean audit.

**Next actual-source test:** on `[1/N,1]`, bound the squared Haar error by
`2*alpha_epsilon*log 2`, for `0<epsilon<=1/2`, uniformly in N. This is a
stronger, unproved candidate, not an available estimate. For N>=2 the
finite-interval paper identity is
`error_N = E_N - 1 - 1/N + 2*Re integral_(1/N)^1 A_epsilon`.
The known L1 mean limit would then give a unit full energy bound. Do not
invoke the existing full-error identity before admission: it explicitly
requires `MemLp`. The next mechanism to inspect is the literal
finite-cutoff Gram expansion grouped by the common divisor of its two
Mobius labels, keeping the coprime signed terms and cutoff remainder.
No new receiver or coefficient-independent Gram bound is requested.

### Common-divisor and complete-row tests

2026-10-01. The small-positive admission threshold is unchanged. The
following are paper deductions checked against the current source, not
new Lean-audited producer theorems. No tree Lean changes in this turn.

Write `P(t)=-fermiNymanGen 1 t`, a real 0/1-valued function, and
`H_R(r,s)=integral_(1/R)^infinity P(r*t)*P(s*t) dt`. For positive N,
grouping the actual finite integration energy by `g=gcd(d,e)` gives
`E_N(epsilon)=sum_(g<=N) mu(g)^2*g^(-1-2*epsilon) *
sum_(r,s<=N/g; gcd(r,s)=1; gcd(g,r*s)=1)
mu(r)*mu(s)*(r*s)^(-epsilon)*H_(N/g)(r,s)`.
The scaled integration endpoint `g/N` is essential: this is not the
full raw-prefix Gram with a separable Euler factor. Extending a positive
common-divisor mass inside a signed coprime sum is not an upper-bound
operation. The retrieved product-fibre law also shows why grouping by
product does not create cancellation: every nonzero Mobius pair on a
fixed product has that product's Liouville sign. Its Gamma--Hankel
variation result concerns a different kernel and was not substituted
for a PM estimate.

There is a more specific nonlinear identity. Finite weighted Mobius
inversion gives `sum_n n^(-epsilon)*A_epsilon(n*t)=P(t)` for t>0.
The existing `LogarithmicCoprimeEnergy` identity, applied after the
weight change `f(T)=exp(epsilon*T)*A_epsilon(exp(-T))`, and `P^2=P`,
give the paper formula
`sum_(gcd(r,s)=1) (r*s)^(-epsilon)*A_epsilon(r*t)*A_epsilon(s*t)
=A_(2*epsilon)(t)`.
All sums at a fixed positive t are finite. The unique coprime diagonal
is `(1,1)`, so this is `A_epsilon(t)^2 + cross_epsilon(t)`.
Known L1 admission of the right side does not bound the square before
the integrated cross term has a lower bound.

The complete-row proposal fails in its uniform-norm form. Exact finite
inclusion-exclusion gives, for a>=1,
`sum_(gcd(a,n)=1) n^(-epsilon)*A_epsilon(n*t)
=sum_(d|a) mu(d)*d^(-epsilon)*P(d*t)`.
This is precisely the finite-prime source on `a.primeFactors`, using
the definition in `PMPowerDampedMobiusPrimeGrowth`. Taking a to be the
product of a canonical prime aperture recovers the sources whose norms
diverge for each `0<epsilon<1/2`, by the existing
`pmCanonicalPrime_no_bounded_cofinal_subsequence`. Thus no uniform L2
row estimate can close this proposal. The positive survivor is the exact
finite-prime row identification and the already formalized finite-prime
admission/threshold classification; no duplicate leaf was added. This
does not rule out the actual weighted aggregate of rows.

The harmonic row bound in `MobiusCoprimeHarmonicUniform` controls
`sum_(d<=N; gcd(r,d)=1) mu(d)/d`. It does not include the Fermi Gram
weight. The CCM complete-row decay theorem instead uses its own source's
constant limit and decaying transient; the Fermi indicator does not have
that limit at zero. Neither is an applicable PM upper bound.

**Next signed target, still unproved:** for N>=2 and `0<epsilon<=1/2`,
`integral_(1/N)^1 cross_epsilon >= -1`. At epsilon=0 the exact baseline
is `-1+2/N`. The displayed floor, if proved, would give
`E_N <= 1 + integral_(1/N)^1 A_(2*epsilon)` and hence admission by the
known L1 mean limit. This is a proposed actual-source inequality, not a
new receiver to formalize. Its possible mechanism is a signed damping
variation of the complete coprime form, retaining both `A_(2*epsilon)`
and every cross term. Pointwise lower bounds and independent row norm
bounds are not substitutes.

Search36 was partial at reranking, search37 at decomposition, search38
at semantic retrieval/filtering. All returned candidate/source
statements and ingredient groups were inspected. No applicable signed
upper-energy or lower-cross estimate was retrieved. Source inspections
confirmed the coprime identity, finite-prime definition, harmonic bound,
and domain restrictions above. Compiler coverage was mostly pending or
stale; no new formal verification is claimed.

### Signed cross variation and reflected-line check

2026-10-01. **No progress on small-positive admission this turn.** The
current source and frontier map still supply admission only at and above
half damping. No new Lean file or unconditional producer was added.

Let `D_eta=partial_eta A_eta` and
`C_N(epsilon)=integral_(1/N)^1 (A_(2*epsilon)-A_epsilon^2)`.
The exact finite-interval derivative is
`C_N'(epsilon)=2*integral D_(2*epsilon)
-2*integral A_epsilon*D_epsilon`.
For fixed positive epsilon, the first term has an unconditional L1
majorant from `sum log(d)/d^(1+2*epsilon)`; this does not control the
second, quadratic term. Substituting `D_epsilon=Lambda_epsilon*A_epsilon`
retains the signed prime-dilation correlations. Absolute estimates
again charge `sum Lambda(q)/q^(epsilon+1/2)`.

At zero, the paper derivative is `4*integral_(1/N)^1 D_0`, tending to
`4*log 2`. Its nonnegativity follows from the existing positive
von-Mangoldt/Haar convolution: the integral of Haar over `[a,1]` is
`min(a,1-a)>=0` for `0<=a<=1`. This favorable initial slope supplies no
cutoff-independent interval of positive derivative. Neither
`C_N(epsilon)>=-1` nor monotonicity on `[0,1/2]` was proved or refuted.
The retrieved `pmDampingDerivativeMajorant_le` controls an L1 Abel
difference-quotient error; it is not a bound for this quadratic pairing.

A separate functional-equation attempt also does not give admission.
On `Re s=(1-epsilon)/2`, the two zeta arguments `s` and `s+epsilon`
are related by conjugate reflection. A modulus comparison for the
meromorphic quotient on that line is not identification with the Mellin
transform of the actual supported source. Moving from the known initial
strip must still justify continuation and any intervening poles. The
existing PM cleared identity on `Re s>1/2` explicitly assumes admission.
`ZetaHardyQuotient` controls the renormalized zeta numerator, while the
retrieved signed Schur multiplier and causal bounds retain their
`sigma>1` or `Re z>=0` restrictions. No reciprocal Hardy bound or
source-support transfer was obtained. No boundary L2 claim is made.

Search39 completed without reported errors; search40 was partial at
reranking. Candidate statements, source arguments and proposed groups
were inspected; the proposed cross-sign and Mellin-symmetry compositions
do not discharge the actual-source obligations. Compiler coverage was
mostly pending/stale. No new Lean audit was run because there is no new
Lean proof to audit.

Next test: a uniform weak-L2 level-set bound for the actual source,
`measure {0<t<=1 : |A_epsilon(t)|>lambda} <= B_epsilon/lambda^2`,
at cofinally small positive epsilon. This remains an unproved producer
candidate. Such a bound would give Lp admission for every p<2 on this
finite carrier and Mellin analyticity on `Re s>1/2`; no weaker success
criterion replaces the unconditional RH goal. Search existing weak-type
source estimates before attempting it, and do not add another receiver.

### Weak-type split and complete-column cancellation

2026-10-01. **No improvement of the small-positive admission frontier.**
The weak-L2 conjecture was not proved or refuted. No new Lean theorem,
admission claim, or RH conclusion was produced.

For fixed `0<epsilon<1/2`, split the source at its literal denominator
cutoff N. Outside `(0,1/N)`, it equals the finite power-damped prefix.
The existing raw-prefix logarithmic energy savings and Abel identity
give, on paper, a prefix-square upper bound of size
`C_epsilon*N^(1-2*epsilon)` (with arbitrary fixed logarithmic savings).
Chebyshev therefore gives the level-set upper bound
`1/N + C_epsilon*lambda^(-2)*N^(1-2*epsilon)`.
Balancing the powers yields exponent `1/(1-epsilon)`, strictly below 2.
Thus this split does not establish the proposed weak-L2 estimate.
The existing L1 estimate alone gives only an inverse-first-power tail.
This diagnoses the attempted proof, not a counterexample to weak L2.

Search41 (weak physical-source level sets), search42 (weak-type Mobius
summatory estimates), and search43 (signed natural-prefix Fermi Gram)
returned no applicable unconditional improvement. All candidate and
source statements and proposed ingredient groups were inspected.
Search41 was partial at semantic retrieval, search42 at filtering/source
retrieval, and search43 at reranking. Coverage reported 64,071 inventoried
files, mostly pending/stale compiler metadata; these are source checks,
not new Lean audits. The retrieved large-value energy estimate concerns
Dirichlet polynomials in height. The retrieved Mobius window estimate
still contains its block-cost and global summatory-error inputs. Neither
was substituted for the physical-source estimate.

The signed transfer kernel exposes a more specific remaining issue.
Write `w(m)=|a_epsilon(m)|` and `k(m,r)` for the existing Ramanujan
transfer kernel. Its complete signed column has paper sum
`sum_m k(m,r)=1` for r=1 and 0 for r>1: commute the finite divisor
convolution with the absolutely convergent m-sum, apply the existing
multiple-inversion identity, then `UnitAF*MobiusAF=1`.
This is a consequence of the existing identities, not an energy bound.

The actual triangular transfer multiplies k(m,r) by
`F_epsilon,Q/(m*r)(r*t)`. This depends on m, so the complete column
cancellation does not cancel that sum. Even the finite column itself
is not centered: for a prime p and `1<=M<p`, its sum over `1<=m<=M`
is exactly
`-p^(-epsilon)/(p^(1+epsilon)-1) * sum_(m<=M) w(m) < 0`.
In particular, the actual cutoff `M=floor(Q/p)` has this issue when
`sqrt(Q)<p<=Q`. Replacing the triangular cutoff by a product probability
space would lose the term requiring proof.

Search44 checked signed-column/prime-divisibility orthogonality. It was
partial at semantic retrieval; all returned candidate/source statements
and its proposed group were inspected. Character orthogonality and the
positive incidence-column bounds returned there do not control the
m-dependent physical prefix. No estimate was obtained from them.

Next hard test: retain the m-dependent prefixes and bound their pairing
with these centered signed columns, using finite summation by parts in
m. Check whether the cumulative signed kernel gives a genuine power
gain after the moving-prefix differences are included. A proof only of
the complete column sum, or another absolute kernel norm, does not meet
this target and should not become a new leaf.

### Moving-prefix Abel test and finite phase windows

2026-10-01. **No new small-positive admission bound.** Rechecked the
current PM frontier: the actual unconditional producer remains
`epsilon>=1/2`. No new Lean file was added.

For fixed r, put `M=floor(Q/r)`, `S_j=sum_(m<=j) k(m,r)`, and
`b_j(t)=F_epsilon,floor(Q/(j*r))(r*t)`. Finite Abel summation retains
the exact boundary term:
`sum_(j=1)^M k(j,r)b_j = S_M b_M
+ sum_(j=1)^(M-1) S_j*(b_j-b_(j+1))`.
The differences are signed Mobius sums over the intervening denominator
intervals. For prime p the cumulative column has the sharper paper law
`S_M(p)=-p^(-epsilon)/(p^(1+epsilon)-1)
 * sum_(M/p<n<=M, p does not divide n) w(n) <= 0`.
It follows by separating m divisible by p and using the existing
prime-multiplication formula for w. The same formula has p^(-a*epsilon)
in place of p^(-epsilon) for r=p^a, a>=1.
This sign does not control the pairing with the moving-prefix
differences. Composite columns need not share it: if r=p*q with distinct
primes and `1<=M<min(p,q)`, every nonzero summand is positive. Thus no
all-column one-sign inequality was obtained. Taking norms after Abel
restores unsigned prefix increments instead of the needed cancellation.

A second test inserts an imaginary damping parameter tau into each
literal coefficient, multiplying it by `exp(-i*tau*log d)`. For every
finite prefix, the infinite tau-average of its physical square norm is
exactly `log 2 * sum_(d<=N) mu(d)^2/d^(1+2*epsilon)`; the complete
diagonal is finite for each epsilon>0. This is a finite-prefix
time-average statement, not an admission theorem for any fixed tau.
For a fixed finite tau window, the inspected sharp mean-value theorem
`Sieve.dirichlet_meanValue_sharp` has error `104*sum d*|coefficient_d|^2`.
Applying it pointwise and then integrating the Fermi generator gives
the unpaid cost `104*log 2*sum_(d<=N) mu(d)^2/d^(2*epsilon)`.
The infinite-window and infinite-prefix limits therefore cannot be
exchanged using that bound. No local-window upper bound was proved.

Search45 was partial at reranking; search46 completed without reported
errors. All candidate/source statements and ingredient groups were
inspected. The retrieved first-tail pair kernel retains its signed
off-diagonal obligation; the retrieved Abel identities supply no upper
estimate. Source inspection of `DirichletMeanValueSharp` confirmed the
extra d cost. Compiler metadata remains mostly pending/stale; no new
formal audit is claimed.

Next actual-source conjecture to test: a common finite bound, at one
fixed T>0 and cofinally small epsilon>0, for
`integral_(-T)^T integral_0^1 |F_(epsilon+i*tau),N(t)|^2 dt d tau`.
Keep the exact signed off-diagonal kernel
`G(m,n)*sin(T*log(n/m))/log(n/m)` and the natural denominator cutoff.
The diagonal, Bohr mean, character orthogonality, and generic
Montgomery--Vaughan bound alone do not prove this conjecture. Do not
formalize another conditional receiver before obtaining the upper
estimate itself.

### Fixed-window primitive-ratio test

2026-10-01. **The fixed-window upper bound is still open.** No actual
small-positive admission theorem, new Lean leaf, or RH conclusion was
obtained. The previous phase-average diagnosis was rechecked against
the current working card and exact corpus statements.

Let `P(t)=-fermiNymanGen 1 t` and
`G(m,n)=integral_0^infinity P(m*t)*P(n*t) dt`. The finite symmetric
phase-window energy has diagonal
`2*T*log 2*sum_(d<=N) mu(d)^2/d^(1+2*epsilon)` and strict
off-diagonal
`4*sum_(m<n<=N) mu(m)*mu(n)*(m*n)^(-epsilon)*G(m,n)
 * sin(T*log(n/m))/log(n/m)`.
This paper expansion retains the natural cutoff and every sign.

The corpus's primitive-ratio reindexing applies, but its general
description of possible inner-sign cancellation does not supply it for
these coefficients. With m=g*r, n=g*s and coprime r,s, homogeneity of G
and the Mobius product law leave the inner scale factor
`sum_(g<=N/max(r,s), coprime(g,r*s)) mu(g)^2/g^(1+2*epsilon) >= 0`.
The outer sign `mu(r)*mu(s)` and sinc factor remain. Thus common-divisor
grouping itself gives no cancellation gain in this phase-window test.
The sine factor stays positive near ratio one, so oscillation at distant
ratios does not remove the nearby signed correlation obligation.

Search47 returned the exact primitive-ratio identity, conditional
correlation-to-window bounds, and squarefree/divisor decompositions.
All candidate/source statements and ingredient groups were inspected;
the search was partial at reranking. In particular the proposed
`sum_normSq_window_moebius_le_of_correlation` explicitly requires the
unproved signed correlation bound. `MoebiusPairVariance` uses unsigned
squarefree pair counts. `MoebiusSeriesPolySaving` is a logarithmic saving
at abscissa `1+1/log z`, and `CofactorLowFreqBound` supplies a stretched-log
envelope, not a fixed-power improvement. No such hypothesis was inserted
into a PM proof. Compiler metadata remains mostly pending/stale.

Next test returns to the actual real-damping source, rather than adding
another phase-window receiver: seek a source-derived finite floor
`integral_(1/N)^1 (A_(2*epsilon)-A_epsilon^2) >= -C_epsilon`,
uniform in N, for cofinally small positive epsilon. The earlier unit
floor would suffice but is stronger than needed. Test whether the
positive squarefree cofactor weights provide an applicable variance
identity for this *integrated signed cross term*, retaining the cutoff
and verifying integrability before any Jensen or conditional-expectation
step. No bound or admissible random-source realization is assumed.

### Positive cofactor expectation and adjacent-damping checks

2026-10-01. **No advance in actual small-positive admission.** Tested the
proposed positive-probability route to the integrated coprime floor.
The obstruction below concerns the direct Jensen estimate, not the
signed energy conjecture. No route is retired and no new Lean theorem
is claimed.

Write `a_epsilon(q)=pmPowerDampedRamanujanWeight epsilon q` and
`w(q)=|a_epsilon(q)|`. The existing exact normalization is `sum w=1`;
the actual coefficients are `mu(q)*w(q)`, not w(q). For the cumulative
carrier, the corresponding signed feature is
`X_q(N)=mu(q)*pmRamanujanPrimitive(q,N)`, q>1. Setting the q=1
centered feature to zero gives the pointwise expectation representation
of the actual centered divisor sum, by the existing absolutely
convergent Ramanujan expansion. This does not establish square
integrability of the feature family.

In fact its proposed positive Jensen cost already fails on prime
features. The inspected exact theorem `pmRamanujanPrimitive_prime`
gives `X_p(N)=N mod p`. For `1<=N<p`, the reciprocal-energy summand
is `N/(N+1)>=1/2`. Therefore, on paper,
`pmRamanujanPrimitiveGram(p,p)>=(p-1)/2>=p/4`.
The inspected Euler weight law gives
`w(p)=alpha_epsilon/(p^(1+epsilon)-1)>=alpha_epsilon*p^(-1-epsilon)`.
Consequently the positive average of these prime energies dominates
`(alpha_epsilon/4)*sum_p p^(-epsilon)`, which is infinite for
`0<epsilon<=1` by comparison with the corpus's prime reciprocal
divergence. Thus this Jensen route cannot supply the desired finite
upper energy bound. No infinite interchange was used to infer a finite
norm. The surviving signed mean may have finite energy despite this
infinite positive feature-energy cost; its cross cancellations remain
the hard question.

Also checked whether adjacent damping supplies a different inequality.
The finite coefficient identity extends the already logged doubling
identity: `A_(epsilon+delta)(t)=sum_n n^(-epsilon)*c_delta(n)*A_epsilon(n*t)`
for t>0, with only finitely many nonzero terms. Its nonnegative
coefficients do not make the signed dilation quadratic coercive.
This returns to the earlier unpaid actual-source inverse comparison,
so it is not a new producer or a reason to repeat absolute inverse
estimates.

Search48/49: all20 candidate and all20 source statements, methods, and
ingredient groups inspected for both requests. Both were partial at
reranking; compiler coverage remains predominantly pending/stale.
The returned `ChronologicalDampedResponseEnergy_bound` concerns the
different rational response `exp(-t)/(1+epsilon*exp(-t))`, and its source
explicitly leaves finite arithmetic residual convergence open. The PM
endpoint energy bound returned by search49 assumes the very L2 admission
being sought. Neither was used as an unconditional PM producer.

Next focused test: retain the Mobius signs while grouping Ramanujan
features by a chosen small-prime part before estimating their anchored
energy. The prime-only Jensen cost shows that estimating each complete
feature separately is too expensive. Check whether summing all paired
features q and p*q before taking a norm yields a summable bound for the
actual natural-denominator cutoff, including unmatched boundary terms.
Do not replace that cutoff by a finite-prime product or assume those
boundary terms vanish. Only a resulting bound for the full signed
source would advance admission.

### Small-prime pairing test; return to the witness half-mass producer

2026-10-01. **No lower-damping admission or witness-positivity result.**
Previous turn supplied evidence against direct Jensen, not an advance
in the hard energy bound. This turn checked signed pairing rather than
repeating that estimate.

For a prime p not dividing q, q>1, finite divisor algebra gives on paper
`R_(p*q)(N)=p*R_q(floor(N/p))-R_q(N)`, where R_q is the Ramanujan
primitive, not the actual centered divisor remainder. The exact Euler
weight recurrence then yields
`a(q)*R_q(N)+a(p*q)*R_(p*q)(N)
 = a(q)/(1-p^(-1-epsilon))
   *[R_q(N)-p^(-epsilon)*R_q(floor(N/p))]`.
At denominator cutoff Q this pairing covers only q<=Q/p; the terms
Q/p<q<=Q with p not dividing q remain. They cannot be silently dropped.
For the reciprocal step profile f(t)=R_q(floor(1/t)), the normalized
paired operator is `(I-p^(-epsilon)*D_p)/(1-p^(-1-epsilon))`,
where `D_p f(t)=f(p*t)` and its L2 norm is p^(-1/2). The reverse triangle
bound therefore gives a strictly positive lower comparison factor
`(1-p^(-epsilon-1/2))/(1-p^(-epsilon-1))`. A fixed finite prime grouping
does not remove the divergent positive feature-energy cost diagnosed
above.

Growing complete prime groups also fail to justify a groupwise Jensen
bound. This follows already from the inspected finite-prime source
obstruction. Let P(t)=-fermiNymanGen(1,t) and use the uncentered Fermi
feature `Y_q(t)=sum_(d|q) mu(d)*d*P(d*t)` for squarefree q. Under mass
w(q), its pointwise expectation is the actual A_epsilon, by the exact
squarefree multiple-mass law. For a finite prime set E, the group with
no prime outside E has probability
`alpha_epsilon/product_(p in E)(1-p^(-1-epsilon))>=alpha_epsilon`.
Its normalized mean feature is precisely
`product_(p in E)(I-p^(-epsilon)*D_p)P`, the existing finite-prime
power-damped Fermi source. Thus a positive groupwise energy estimate
includes at least alpha_epsilon times that source's squared norm.
The inspected theorem `pmCanonicalPrime_no_bounded_cofinal_subsequence`
already excludes a common bound for canonical E at 0<epsilon<1/2.
This diagnoses the positive grouping estimate; it does not refute
natural-cutoff signed cancellation or actual A_epsilon admission.

Search50 completed without errors; search51 was partial at reranking.
All candidate/source statements and ingredient groups were inspected.
The proposed energy chain in search51 starts with a LOWER bound for
physical energy and a bound for one high-clock layer, not a full upper
estimate. Direct inspection of the Matomaki--Teravainen grid-free and
aggregate dilation leaves gives logarithmic error savings and retains
source-data certificates; it supplies no PM boundary cancellation or
fixed-power improvement. No new Lean module was added.

Because these attempts do not advance the admission gap, the next PM
attack returns to the frontier map's original producer: nonnegative
dyadic half-mass for every actual Fermi witness. Search52 and the exact
source files confirm bounded witnesses are already self-similar; no
bounded approximation preserving all witness constraints was returned.
The search was partial at reranking; all20 candidates, all20 source
arguments, and the ingredient group were inspected. Its half-mass
statements are RH equivalences/receivers, not positivity proofs.

Two elementary regularization tests expose the unpaid condition.
Freezing w below a>0 gives a bounded continuous function, but at every
b>=1/a its source pairing is
`-conj(w(a))*log(2)/b`, by generator support and the exact generator mean.
This is nonzero for the existing spurious power witnesses, whose values
never vanish. So this regularization fails actual orthogonality even
without assuming any off-line zero. A cutoff to zero instead leaves the
small-tail pairing error. Cauchy--Schwarz makes that error small as the
cutoff tends to zero, but does not make it exactly zero or prove a
bounded correction exists.

Next concrete conjecture: derive upper-shell energy control directly
from the literal annihilation equations, retaining their full lower
tail. With P=-phi_1 and W(x)=integral_0^x conj(w(t)) dt, those equations
give for 0<x<=1 the absolutely interval-summed relation
`integral_(x/2)^x conj(w(t)) dt
 = -sum_(k>=1) integral_(x/(2*k+2))^(x/(2*k+1)) conj(w(t)) dt`.
It bounds a moving shell average; the hard new estimate must control
the full shell L2 energy, including oscillation. Merely applying
Cauchy--Schwarz to this averaged relation is insufficient. Test a
source-native shell operator estimate before adding any new receiver,
and do not assume the bounded-witness class is dense in all witnesses.

### Moving-shell differentiation and the oscillation cost

2026-10-01. **Witness half-mass positivity remains open.** Last turn's
failures changed the attempted mechanism, but did not improve PM
admission. This turn tested whether the moving-shell relation supplies
an energy estimate, rather than another formal receiver.

Let `H_w(x)=integral_(x/2)^x w(t) dt`. Known spurious witnesses already
rule out a frequency-independent recovery of full energy from this
average. For `w_k(t)=t^(-i*omega_k)`,
`omega_k=2*pi*k/log(2)`, k nonzero, the existing spurious mode law gives
on paper
`H_(w_k)(x)=x^(1-i*omega_k)/(2*(1-i*omega_k))`.
Thus `integral_0^1 |H_(w_k)(x)|^2/x^2 dx
 =1/(4*(1+omega_k^2))`, while `integral_0^1 |w_k|^2=1`.
Their vanishing shell-average norm is compatible with exact witness
membership and exact half-mass. Cauchy--Schwarz on the shell equation
cannot recover the missing oscillatory energy with a uniform constant.

Differentiating must keep paired endpoints. Define on a sufficiently
regular profile
`T_M w(x)=sum_(k=1)^M [w(x/(2*k+1))/(2*k+1)
                     -w(x/(2*k+2))/(2*k+2)]`.
For C1 profiles with `g(x)=w(x)+x*w'(x)` in L2(0,1), parameter
differentiation of `u^(-1)*w(x/u)` and dilation scaling give the paper
tail bound
`||sum_(k>=K) [w(x/(2*k+1))/(2*k+1)
              -w(x/(2*k+2))/(2*k+2)]||_2
 <=2/sqrt(2*K+1)*||g||_2`.
Indeed each paired difference is the integral of
`u^(-2)*g(x/u)` over [2k+1,2k+2], whose L2 norm is at most
`u^(-3/2)*||g||_2`. This permits the paired derivative limit for this
regular class, yielding `w-(1/2)*w(x/2)+T w=0` for witnesses.
It is not a bound on arbitrary witnesses with only the existing
continuity/L2 hypotheses. Even on spurious witnesses, `||g||_2` grows
like |omega_k|, so discarding this cost is invalid. No such Sobolev
premise was added to a claimed RH proof.

Also tested the stronger profile-wide coercivity estimate
`||(I+T)w||_2 >= (1/2)*||w||_2`, which would imply half-mass when
combined with the witness equation. It fails outside the constrained
witness class. Take a known spurious mode s and a nonzero nonnegative
smooth bump h supported in (1/2,1), and put `v=(1-delta*h)*s`.
Every lower-tail evaluation in T misses h, so `T(h*s)=0` and
`T s=-(1/2)*s`. Hence, on paper,
`||(I+T)v||_2^2-(1/4)*||v||_2^2
 =-(delta/2)*integral h+(3*delta^2/4)*integral h^2 < 0`
for sufficiently small positive delta. The perturbed v is not a
witness: it is bounded but fails dyadic self-similarity, contradicting
the inspected bounded-witness classification if membership were assumed.
Thus the attempted unrestricted operator estimate fails, not the
actual witness half-mass conjecture.

Search53/54 were partial at reranking. All candidate/source statements,
methods and ingredient groups were inspected. Search53 returned the
existing source correlation, bounded classification and RH receivers;
the unrelated Xi shell identity supplies no PM inequality. Search54
returned dilation scaling and scalar monotone alternating-series tools.
Those scalar hypotheses do not apply to general complex witness values
along dilations. Compiler coverage remains predominantly pending/stale.
No Lean file changed, so no new build or formal proof is claimed.

Next attack must use the exact annihilation constraints in the signed
quadratic pairing, rather than replace them by smoothness or bound each
tail norm. With `S w=w(x/2)`, the differentiated equation gives
`q(w)=2*||w+T w||_2^2-(1/2)*||w||_2^2` on its justified domain.
Seek a source-derived sign for this complete expression, including
mixed terms with the neutral spurious modes. Those mixed terms cannot
be discarded by passing to a quotient: the corpus explicitly shows
that the neutral spurious space need not be a form radical. Establish
the sign and passage to all witnesses before formalizing any receiver.

### Mixed source averaging and a scalar-tail correction test

2026-10-01. PM witness half-mass positivity remains open. Search55 returned
the exact spurious/zero mixed coupling and existing correlation receivers,
not a law making the spurious sector a form radical. Its suggested sums
and majorants do not supply that law.

For a fixed nonzero dyadic frequency omega, the modulated Haar target
`t^(-i*omega)*H(t)` has Mellin transform
`(1-2^(1-s))/(s-i*omega)`. Dividing by the literal P-source transform
still leaves `s/((s-i*omega)*zeta(s))`. Cancellation of the dyadic factor
has not produced the required source approximation.

The concrete scale-average attempt also retains the old error floor.
On L2(0,1), let `V_z f(t)=integral_1^infty a^(z-1)*f(a*t) da`, extending
f by zero above one. For purely imaginary z, dilation scaling gives
`||V_z||<=2`. Finite-scale averages preserve the closed Fermi-source
span, and their norm tails tend to zero. Thus V_z preserves that span.
The resolvent identity gives mutually inverse bounded operators
`R=I+z*V_z` and `R^(-1)=I-z*V_0`. For `z=i*omega` with `2^z=1`,
`R H=t^(-z)*H`. Hence R transforms raw approximations into source
averages, but `||R(A_N-H)|| >= ||A_N-H||/(1+2*|omega|)`.
The already formalized raw error floor survives. This is a paper test
of this construction, not new witness positivity.

The next concrete construction subtracts `N*h_N*P(N*t)` from the raw
source to cancel its auxiliary harmonic tail exactly. Its first omitted
interval is still `M(x)-M(N)+N*h_N`, N<=x<2N. The resulting paper argument
shows why even optimal scalar centering cannot erase the critical
Mertens window variance. Full derivation, positive survivor and pending
Lean bridge are in `pm-mertens-window-variance-floor.md`.

Search56/57/58 were partial at their reported retrieval/reranking stages;
all candidate/source statements, methods and ingredient groups were
inspected. Source freshness remains predominantly pending/stale.
`MobiusCenteredMertensLimit` was checked as a possible producer: its
critical vector uses mu(n)/n and the zeta line Re=1, not the PM half-line
energy. No endpoint promotion was inferred. The compact tent Mellin pair,
its nonvanishing for Re(s)>0 and measurability passed a scratch Lean check.
Their active source is saved under the new card's `pending-lean` directory;
the boundedness and Mertens-window bridge remain to be proved. No finished
module or formal advancement of RH is claimed.

### Scalar correction closed; return to the signed covariance producer

2026-10-01 continuation. The last-scale correction is now ruled out in
Lean. `PMMertensLogTent` proves, without RH or a zero simplicity premise,
that for every fixed q>1 there is C>0 such that cofinally many integer N
satisfy `C <= integral_(N,q^2*N] ((M(floor(x))-a)/x)^2 dx` for every scalar
a simultaneously. Its logarithmic tent has Mellin transform
`(1-q^(-s))^2/s^2`, nonzero for Re(s)>0. Exact Abel summation connects its
actual Möbius source to the two adjacent logarithmic Mertens integrals;
constant centers cancel. The cofinal critical source floor, Cauchy--Schwarz
and Lipschitz rounding yield the positive invariant in the canonical weight.

`PMCorrectedMobiusWindow` uses coefficients
`mu(d)-1_(d=N)*N*h_N` and proves the exact first omitted window formula
`E_N(1/x)=M(floor(x))-M(N)+N*h_N`. Reciprocal substitution retains the
full auxiliary energy, and finite-coefficient coercivity transfers the
positive floor to the literal Fermi error. Its final theorem is
`not_tendsto_pmTailCorrectedMobiusFermiErrorEnergy_zero`.

Both targeted `lake --old build` calls passed. Both final audits used
`lake env lean` on the real formal files and passed without diagnostics.
All 47 exported declarations were axiom-audited through /tmp files:
only propext, Classical.choice and Quot.sound. Both modules are wired.
Global lint still fails for 11 unrelated unwired RHTower modules; neither
new leaf is among those failures. The closed construction and positive
survivor are recorded in `../5-failed/pm-scalar-tail-correction.md`.

Evaluation: this creates an unconditional source obstruction and a
centering-invariant oscillation theorem. It supplies no witness half-mass
positivity or small-damping admission. The next attack must control the
full actual signed covariance. A scalar subtraction has been exhausted.

Search61 was partial at reranking; candidate/source statements and the
returned proof/ingredient groups were inspected. The current corpus also
has the finite absolute transfer mass bound
`pmPowerDampedRamanujanTransfer_finite_mass_le`. Its exact transfer identity
still multiplies prefixes at Q/(m*r), whose norms have no small-damping
budget. The finite kernel mass cannot be treated as that missing budget.
The actual Ramanujan logarithmic square mass is summable, and bounded
actual signed Gram variance implies L2 admission. The unresolved producer
is a bound for that actual Möbius-aligned quadratic form, retaining all
cross terms. No such bound or new premise is asserted here.

Next conjecture is recorded in `pm-paired-cutoff-gram-budget.md`: dominate
the actual signed Ramanujan Gram quadratic by its summable logarithmic
square mass, with a constant depending on positive damping. The attempted
mechanism pairs the exact Euler-recursive coefficients while retaining
every natural product-cutoff boundary term. Completing all prime products
before estimating is excluded by the existing aperture-divergence theorem.
Search62 supplied the exact prime primitive, coefficient recursion, Gram
decompositions and admission receiver, but no missing signed upper bound.
The new card is an unproved research target, not a formal advancement of RH.

### Prime pairing: exact covariance solved, termwise dissipation rejected

`PMPairedRamanujanGram.lean` proves the exact primitive prime recursion,
reciprocal-weight dilation, full four-term Gram relation and fixed-channel
mixed limit `G(p*q,r)->phi(r)*Lambda(q)/2-G(q,r)`. The mixing proof uses
periodic centering, bounded prefixes, finite Abel summation on every
quotient block, and absolute summation. Every diagonal G(q,q) is strictly
positive. This strengthens the paper sign conjecture to every
non-prime-power q>1, without squarefreeness: G(p*q,q) is eventually
negative. For squarefree q the actual coefficient product is negative,
so the actual paired cross energy is eventually strictly positive.

This is new signed-covariance information, not a small-damping upper
budget. It rejects the proposed termwise cancellation justification;
the precise mixed limit and exact Gram identity are the formal positive
survivors. The full natural-cutoff conjecture remains active in
`pm-paired-cutoff-gram-budget.md`; the local no-go is closed in
`../5-failed/pm-prime-pair-termwise-dissipation.md`. Next attack must retain
different-cofactor cross terms and every cutoff boundary, since a fixed
channel limit cannot be used uniformly for growing channels.

Validation completed: targeted `lake --old build` (only the new leaf
built), final actual-file `lake env lean`, all ten exported declarations
with only `propext`, `Classical.choice`, `Quot.sound`, umbrella wiring.
No computations, added axioms, proof holes, heartbeat increases or full
umbrella builds. Global formal lint reports twelve unrelated unwired
leaves: CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MobiusDivisorCriticalAbelSignedBoundaryMoments,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
ThetaMovingShellFirstOrderPhase, ThetaTailEndpointCommutatorObstruction,
ZetaZeroDensityPowerSaving. No lint error names this new leaf.

## 2026-10-02 — Exact signed cutoff balance

Route PM remains on the actual natural-denominator Gram budget. Corpus
search67–71 tested signed transfer orthogonality, cutoff differences and
uniform prime/cofactor estimates. Auxiliary orthogonality cannot treat
F_(Q/(m*r)) as independent of m. The new leaf
`PMRamanujanCutoffPrimeBalance.lean` proves the complete prime cutoff mean
and quadratic identities for arbitrary real source inputs, retaining both
the source change H(p*m)-H(m) and the band Q/p<m<=Q. On invariant inputs
the cutoff cross form is negative semidefinite, including products of
the other actual prime factors.

This creates exact signed boundary knowledge, not the missing physical
energy ceiling. Eleven exports passed final targeted build, direct-file
and standard-axiom audits; only the new leaf built. The umbrella is wired.
Global lint has fourteen unrelated unwired leaves, listed in the active
`pm-paired-cutoff-gram-budget.md` card. A completed-prime-aperture
normalization was proved on paper and awaits Lean: it would transfer
known finite-Mobius-aperture divergence to completed Ramanujan apertures.
The natural cutoff estimate remains open and must retain its order.

## 2026-10-02 — Completed-support obstruction closed; ordered boundary retained

`PMRamanujanCompleteAperture.lean` now proves that a completed actual
Ramanujan prime aperture equals its finite Mobius source times the retained
absolute weight mass. This mass lies in [alpha_epsilon,1]. For every fixed
0<epsilon<1/2, canonical completed-aperture norms diverge, although the
logarithmic coefficient-square masses stay bounded. Every fixed multiple
of that mass is eventually exceeded by squared source energy. The exact
normalization, its probability-mass interpretation, and divergence are
the positive survivors; the support-independent energy conjecture is
closed in `../5-failed/pm-ramanujan-completed-support-budget.md`.

All 21 exports passed targeted `lake --old build`, final actual-file
`lake env lean`, and standard-axiom audits; only this new leaf built.
The umbrella is wired. Formal lint reports twelve unrelated unwired
leaves, listed in the active paired-cutoff card. No own build remains live.

Evaluation: the result closes a false proof mechanism, not the actual
natural-denominator energy budget or small-damping admission. Search73
was partial (coverage pending, generation1181925); all returned
candidate/source statements were inspected. No unconditional ordered
producer was returned. The parity-defect alternative was checked against
its literal source: it concerns square-root Abel channels of the
prime-free divisor defect. Late-prime head neutralization permits one
further prime contraction, but does not bound complete prime processing
or the PM source. Its first-defect estimate remains quadratic. No parity
premise is imported into PM.

Search74 completed, with full inventory and largely pending/stale
compiler metadata (generation1182015); candidate/source statements and
ingredient groups were inspected. Its fixed-period primitive bounds do
not control growing cofactors. Next attack keeps the literal PM cofactor
fractional-part formula and the source-change term in the natural-cutoff
prime balance. Search75 checks support localization of the actual Mobius
prefix differences before attempting their full signed physical energy.

Search75 (partial) supplied no physical orthogonality: support differences
overlap near zero. Search76/77 completed and supplied no ordered-band upper
estimate; all candidate/source statements and ingredient groups inspected.
The aperture-divergence proof is qualitative Mellin uniqueness, so it does
not currently compare the omitted-product norm with the natural prefix.
These investigations added no admission theorem. The active paired-cutoff
card now records a direct dyadic denominator-band conjecture and its exact
cofactor form, with zero density and retained Mobius signs. The next task
is to prove its signed upper energy estimate, not add another receiver.
Own searches73–77 are all terminal. No new Lean edit after the successful
complete-aperture audit; documentation whitespace checks passed.

## 2026-10-02 — Complete-period diagonal; anchored variance still open

Search78 completed;79–84 were partial. All returned candidate/source
statements and ingredient groups were inspected; none supplied an actual
small-damping signed upper producer. Existing finite residue covariance
and gcd-power diagonalization expose a new exact cancellation law.

`PMRamanujanPeriodDiagonal.lean` proves finite multiples inversion of the
Ramanujan cofactor, then the complete-period centered diagonal
`(sum_q J_2(q)*a(q)^2-a(1)^2)/12`. It retains both the density drift and
the signed totient mean, and specializes the exact second moment to the
actual complete denominator band. Ten exports passed standard-axiom
audit and targeted old-mode build; only the new leaf built. Umbrella wired;
final direct-file audit exited 0 without diagnostics. Full proof and certificate are in
`../3-formalized/pm-ramanujan-period-diagonal.md`.

Assessment: arithmetic period covariance is now solved exactly; the actual
anchored upper estimate is not. Treating period weights as uniform loses
the required band-scale factor. Paying the period mean separately leaves
an unproved Mobius–totient cancellation problem. The next producer
conjecture compares actual reciprocal-centered band variance with the new
diagonal divided by the band scale (a logarithm is allowed). The exact
reciprocal mean is the existing summable Mangoldt coefficient sum.

The alternative fixed-cofactor prime limit does not pay the moving-factor
cost: its proof contains error `2*A*B*zeta(2)/p`, with B the whole centered
prefix bound. Full smooth and balanced-factor regions must remain. No
conditional RH receiver was added and no admission claim is made. The
active paired-cutoff card records the new conjecture, its precise source,
failed inferences, and all fourteen unrelated global lint wiring errors.


## 2026-10-02 — Source-derived band profile and coprime residue

New profile: `g(p)=p/(p+1-p^(-epsilon))`,
`f(n)=prod_(p|n)(1-g(p))`, `F(N)=sum_(n<=N)f(n)`.
`PMRamanujanBandProfile` proves its exact Mobius/floor identity, weighted
summability at every positive exponent, subpower growth, and anchored
energy admission. Thirteen exports; old-mode targeted build, standard
axioms, and final actual-file audit passed. Umbrella wired.

`PMRamanujanBandResidue` proves literal actual-cofactor reconstruction from
positive coprime squarefree h_d, prime/prime-square residue values,
reciprocal residue admission, fixed-mask density, exact local source
factor g, and the full weighted residue expansion with cutoff retained.
Its 18-export targeted build, standard-axiom audit, and final actual-file
audit all passed, the final audit without diagnostics.
No full or umbrella build. No numerical experiments, new axioms, or
heartbeat changes. Search88–91 partial; all candidates, source arguments,
and ingredient groups inspected. Detailed coverage and proof log are in
`pm-ramanujan-band-critical-profile.md`.

Assessment: the actual source-limit ingredients advanced; no small-damping
anchored energy upper bound advanced. The new paper joint-residue identity
`sum_(d|l)mu(d)*h(d)*R_d(l/d)=mu(l)` explains why prime-square signs must be
retained. The hard remainder now has explicit kernel form
`alpha*X^(-epsilon)*sum_l theta(X/l)*T_l(N)/l`, with theta bounded and
zero at infinity but constant on l>2X. The next producer attempt must
bound the whole signed kernel norm by O_epsilon(X^epsilon), retaining
both regions and all cross terms. A fixed-mask density estimate cannot
pay this moving-tail cost. No RH/admission claim or new conditional RH
receiver was added. The scalar band limit and density-product
normalization remain Lean-open, with full paper derivations recorded.


Continuation completed the interrupted residue axiom audit and final
actual-file audit, both exit0; all31 exports across the new leaves have
standard axioms only. Source card and frontier map record the precise
limits. Search92–94 did not provide the signed producer. General Farey
separation and scalar Mellin continuation leave explicit unpaid terms.
The clock-averaged same-source quadratic is now recorded as a possible
weaker producer target, with exact overlap L_eta; no conditional receiver
was formalized. The hard signed upper estimate remains unsolved.

Clock/joint-residue continuation: the finite clock endpoint requires
L_(eta,T), not the all-clock overlap on a denominator rectangle. The
common-prime recursion retains two unpaid single-prime boundary forms.
The joint residue has an exact paper primitive classification
T_(t*u^2)=mu(t)*h(u)*sum_(v|t)h(v)*P_(u*v) for coprime squarefree t,u;
all other prime-exponent patterns vanish. In particular T_l contains the
linear mode mu(l)*N. The periodic remainder U_l=T_l-mu(l)*N is admitted,
whereas every squarefree T_l is not. Hence the fixed-N absolute residue
expansion cannot be estimated term by term in the anchored Hilbert norm.
This classification is paper-only, recorded on the active profile card;
no new formalized theorem or admission advance is claimed.

Search95–99 inspected current candidates, source arguments, and proposed
ingredients. The individual Gram/digamma reductions, damping endpoint,
and generic bilinear bounds do not prove the complete signed estimate.
Search99 was partial with complete inventory1185529. The directly read
MoebiusFinalRangeRoughMeanSquare bound concerns a rough-set logarithmic
polynomial averaged over frequency; its sparse-support saving does not
bound the full PM anchored spatial source. The actual Ramare prime
off-diagonal and natural product-boundary terms remain in the equation.
Next work must estimate that joint signed source, rather than replace it
by generic support mass, period variance, or an assumed prime/cofactor
bound. RH goal remains active and unmet.

The finite joint-residue obstruction is now resolved in the actual
source: PMRamanujanJointResidue proves exact joint drift, bounded
centered atoms, their anchored-energy admission, and reconstruction of
the whole natural prefix/band with product cutoffs. Ten public exports;
targeted old leaf build, standard-axiom audit, and final actual-file
lake env lean all passed. Umbrella wired. P3 card records certificates
and eleven unrelated global-lint missing imports.

Assessment: this closes the invalid termwise-Hilbert interchange and
provides a valid finite source representation. It does not advance the
uniform small-damping upper bound. The first local pairing test leaves
V_(p^2)=-p^(-1-epsilon)*V_p and a positive coprime clock coefficient,
so prime-square pairing alone does not erase the prime channel. The
next hard estimate must retain cross terms involving squarefree
composites. Search100/101 coverage and the paper calculation are on the
active profile card. No conditional RH receiver or final RH claim added.

Continued signed-cross attempt: searches102--107 and direct source reads
showed that the proposed short-interval transfer either supplies only
normalized little-o decay or retains the needed correlation hypothesis.
The general Farey bound still pays denominator-square loss. No new
small-damping upper bound or formal theorem resulted. The active profile
card now records a paper-only exact n,p*n,p^2*n block identity, including
the real-spatial seed U_1=-fract and both coprime clock weights. The
remaining task is the full mixed form between distinct p-free cofactors;
local cancellation alone does not pay it. Do not repeat a conditional
receiver, a generic large-sieve transfer, or the already open damping-flow
proposal as frontier progress. Goal remains active and unmet.


Nearby-prime continuation: PMRamanujanNearbyPrimeResonance now proves the
actual primitive Hilbert realization, its continuous dilation covariance
profile, a quantitative finite prime-pair error bound, and arbitrarily
large centered Gram entries for distinct nearby prime multiples of any
fixed non-prime-power cofactor r>1. This falsifies uniform growing-cofactor
control after reciprocal-mean removal. Positive survivor and paper proof
are on P5:pm-ramanujan-nearby-prime-resonance. All 14 public declarations
passed the targeted old-mode build, standard-axiom audit, and final
actual-file `lake env lean` audit; umbrella wired. Global lint reports
eleven unrelated missing imports, listed on the card.

Assessment: the conjecture loop created a formal covariance law and
removed a false local estimate, but did not improve the full signed
small-damping upper bound. Next attack must combine distinct cofactor
branches with their moving intervals and retained clock boundary before
estimating energy. Same-cofactor positive resonance cannot be discarded.
Search108--113 coverage and exact remaining obligations are preserved on
the card and active profile log. RH goal remains active and unmet.


Coupled-moment continuation: searches114--118 and direct source checks
failed to discharge the hard bound. The current critical mollified moment
retains a polynomial-length cost after separating zeta and Mobius factors;
three-lines does not make its fixed-window error decay in the required
strip. Exact truncated convolution cancels the head but leaves the signed
unequal-index moment. Finite-clock counting dissipation likewise retains
its mixed source term, and CRT/lcm identities retain the moving remainder.
The active profile card records formulas, coverage, and the complete
native Mellin product that must be estimated without separating factors.
No new Lean theorem or small-damping energy bound resulted in this turn.
Do not count another scalar tail estimate, fixed-lag density, transfer
kernel bound, or conditional moment receiver as paying this obligation.
