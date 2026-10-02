# Mean-centered divisor Haar completion

- **ID:** pm-centered-divisor-haar-criterion
- **Stage:** 1-in-progress
- **Type:** NEW CONJECTURE / exact replacement criterion
- **Source:** Route PM / PM-31, after canonical prime-aperture divergence
- **Status:** Paper argument below; interfaces and exact novelty need auditing.
- **Target:** Identify canonical admission with the weighted square energy of
  the mean-centered divisor summatory discrepancy. Then test a producer for
  that actual arithmetic energy at arbitrarily small positive damping.

## Arithmetic representation

For epsilon>0 set

`c_epsilon(n) = sum_{d|n} mu(d) d^(-epsilon)`,
`alpha_epsilon = sum_{d>=1} mu(d) d^(-1-epsilon) = 1/zeta(1+epsilon)`,
`C_epsilon(x) = sum_{1<=n<=floor(x)} c_epsilon(n)`.

For n>0, the finite divisor product gives
`c_epsilon(n)=product_{p|n}(1-p^(-epsilon))`, hence 0<c_epsilon(n)<=1.
Divisor-floor reindexing gives the actual physical identity

`A_epsilon(t)=C_epsilon(1/t)-2 C_epsilon(1/(2t))
             =sum_{n<=floor(1/t)} c_epsilon(n) H_0(n*t)`.

Absolute convergence of the alpha series gives C_epsilon(x)/x -> alpha.
For example, divide the floor-divisor identity by x, pass through any fixed
finite head, and bound the remaining terms by sum_{d>K} d^(-1-epsilon).

The positive Haar representation does not justify an infinite Gram-energy
identity: its dilation norm sum need not converge. Finite Haar prefixes have
zero mean, whereas the actual admitted-in-L1 A_epsilon has nonzero mean
alpha_epsilon*log2. An unproved Hilbert interchange here would lose the
boundary contribution at t=0.

## Exact centered energy candidate

Define `R_epsilon(x)=C_epsilon(x)-alpha_epsilon*x` for x>=0 and
`F_epsilon(t)=R_epsilon(1/t)` for t>0. Then

`A_epsilon(t)=F_epsilon(t)-2 F_epsilon(2t)`,
`t F_epsilon(t)->0` as t decreases to zero.

Iterating backward gives

`F_epsilon(t)=-sum_{k>=1} 2^(-k) A_epsilon(t/2^k)`.

The discarded boundary term is
`2^(-K) F_epsilon(t/2^K)=(1/t) R_epsilon(2^K/t)/(2^K/t)`, which tends to zero.
If A_epsilon is canonically L2, the displayed series converges strongly in
L2 because its term norms have geometric factor 2^(-k/2). Identification
with the actual F_epsilon requires the pointwise telescoping limit, not an
assumed representative equality. Conversely F_epsilon in L2 implies A_epsilon
in L2 by the bounded dilation difference. Both directions have norm constant
1+sqrt2. Reciprocal change of variables therefore yields the candidate

`A_epsilon in L2(dt) iff integral_0^infinity |R_epsilon(x)|^2/x^2 dx < infinity`.

This is an exact criterion, not a proof that the right-hand side is finite.
For x<1, R_epsilon(x)=-alpha_epsilon*x, so that end is harmless. The missing
producer concerns the actual centered discrepancy at infinity.

## Candidate finite approximants and remaining question

Let `D_epsilon(N)=sum_{n<=N}(c_epsilon(n)-alpha_epsilon)` and

`G_N(t)=alpha_epsilon*(-phi_1(t))
        +sum_{n<=N}(c_epsilon(n)-alpha_epsilon) H_0(n*t)`.

These have the exact source mean alpha_epsilon*log2 at every N and stabilize
to A_epsilon for t>1/(N+1). Centering before the coefficient cutoff is the
new feature. Prime-aperture divergence must not be attributed to a missing
mean: the finite prime sources also have nonzero means. No canonical bound
for these centered approximants is asserted.
The paper criterion suggests cofinal cutoffs with D_epsilon(N)^2/N ->0 once
the centered weighted energy is finite; full-sequence convergence requires
its own proof and must not be inferred from mere integrability.

## Corpus audit and plan

- Search1059: all20 candidate/all20 source statements and the damping/decay
  chain reviewed; no actual small-positive admission producer. Partial=true,
  63849 files; generation1173497,coverage1173500/current1173501; semantic
  coverage unmeasured, background refresh incomplete. Detailed log on the
  canonical-prime threshold card.
- Search1060 (`weighted Mobius divisor sum Haar boundary profile`): all20
  candidate/all20 source statements reviewed, including the full factorial-
  period norm statement from source. Partial=false;63852 files;
  generation1173523,coverage1173529/current1173533; semantic coverage
  unmeasured, background refresh incomplete. The generated chain uses integer
  divisor powers and a different Bernstein weight; it supplies no centered
  PM energy bound. No exact criterion above was returned.
- Useful existing interfaces: `DampedMobius.dampedMobius_mul_zeta` and
  `DampedMobius.divisorSum_nonneg`; PM finite divisor-floor summation; exact
  source mean; Haar dilation identities. Existing finite Nyman-error
  coercivity bounds apply after admission and do not by themselves admit the
  actual infinite centered source. Check their generic dilation interfaces
  before introducing new Hilbert lemmas.
- Next: verify arithmetic carrier identities and boundary normalization;
  prove the exact two-way admission criterion; audit possible arithmetic
  energy producers. RH and its negation remain unproved.

- Predecessor threshold is fully audited and retired (22 PM-31 leaves /
  5300 lines /377 declarations). Started scratch1061 with12 declarations:
  actual real power-damped divisor coefficients, their existing damped-Mobius
  product interface, positivity/upper bounds, and exact finite divisor-floor
  identification of the physical Fermi source. No admission premise is added.
  Scratch checking, unpromoted. For the mean normalization, direct mathlib
  inspection found `tendsto_tsum_of_dominated_convergence` and
  `tendsto_nat_floor_mul_div_atTop`; the already-certified L-series at s=1
  supplies the absolutely summable coefficient majorant.

- Scratch1061's expanded18-declaration arithmetic/mean layer passed with
  empty Lean output. In particular C_epsilon(x)/x tends to the explicit
  density 1/zeta(1+epsilon), using the absolutely summable damped-Mobius
  coefficients divided by n. Added11 declarations for the finite positive
  Haar identity, measurable centered remainder/source, exact dyadic
  difference, vanishing backward boundary, finite telescoping, and the
  actual pointwise backward-series limit; this expansion is checking.
  No small-positive admission or energy bound has been assumed proved.
- The existing `Lp.eLpNorm_le_of_ae_tendsto` interface used in the PM dyadic
  resolvent permits the reverse admission proof directly from finite
  backward sums and their geometric norm budget. This avoids constructing
  an additional Hilbert operator solely to prove admission. Exact norm
  constants and representative equality still require verification.
- Search1062 (`dyadic dilation inverse L2 boundary telescoping admission`,
  deep): reviewed all20 candidate/all20 source statements, completing the
  truncated cyclic high-cut statement from its source, plus both generated
  ingredient groups. Existing normalized Sonin inverses operate on already
  admitted Hilbert vectors; Laurent/q-dilation inverses use other carriers;
  the proposed scalar telescope assumes summability. The Route-P Calderon
  argument has a different dilation/amplitude and does not supply actual PM
  admission. Other results concern finite cyclic energy, scale support, or
  existing conditional RH witnesses. No missing arithmetic bound returned.
  Partial=false;63860 files; generation1173767,coverage/current1173772;
  semantic coverage unmeasured, background refresh incomplete. This is a
  bounded corpus audit, not an exhaustive novelty claim.
- Search1064 (`power damped divisor discrepancy square integral inverse
  square`, deep): all20 candidate/all20 source statements and the generated
  two-step proposal reviewed. The inverse-square integral bound plus damped
  power amplitude identity concerns an already decaying explicit function,
  not the arithmetic remainder. DivisorSumMeanSquare supplies an exact lcm
  quadratic identity for coefficients, and EulerDeletionAveragedDivisorCovariance
  bounds a logarithmically smoothed divisor source; neither statement is a
  centered summatory-energy bound. Existing PM diagonal/prime-term results
  do not control the missing off-diagonal cancellation. Partial=false;63864
  files; generation1173873,coverage/current1173880; semantic coverage
  unmeasured, background refresh incomplete. No applicable producer returned.
- Direct inspection completed the generic finite cumulative-energy formula
  in `EulerDeletionAveragedDivisorCovariance`: for real increments b_j,
  `sum_{n<=T}(sum_{j<=n}b_j)^2/(n(n+1))` equals the full double covariance
  with kernel `1/max(j,k)-1/(T+1)`. This includes all unequal pairs. The
  Graham bound there controls the unsummed divisor coefficients; turning it
  into a bound on accumulated centered discrepancy requires an additional
  cancellation argument. Do not infer that missing estimate from the lcm
  coefficient-energy identity.

- PM-31 centered-divisor arithmetic leaf fully audited:
  `PMPowerDampedMobiusDivisorHaar` (295 lines /29 declarations), targeted old
  build24s, final actual leaf empty, all exact-body/name/API/unique-import/
  standard-axiom gates passed. Positive divisor coefficients have exact
  Euler factors; their summatory mean is `1/zeta(1+epsilon)`. The actual
  Fermi source is both a finite weighted Haar sum and the dyadic difference
  of its mean-centered reciprocal summatory remainder. The backward boundary
  vanishes and the finite dyadic sums converge pointwise to that literal
  centered source. Combined: twenty-three leaves /5595 lines /406 audited
  declarations. Global lint has ten unrelated unwired modules and three
  concurrently stale generated files; no owned/proof-debt finding.
  Scratch1063 now checks reverse L2 admission with constant `1+sqrt2`,
  forward admission, and reciprocal weighted-energy equivalence. The actual
  small-positive arithmetic energy bound remains open; RH/negRH unproved.
- Scratch1063's first check identified only explicit carrier/coercion and
  congruence proof errors; the exact geometric prefix budget and Fatou
  transfer elaborated. Fixed those proof interfaces and added the inherited
  unconditional epsilon>=1/2 weighted-energy theorem and the explicit
  cofinal weighted-energy RH receiver. The22-declaration scratch is rechecking;
  its small-positive energy premise is still an obligation, not a result.
- Search1065 (`Mobius fractional part positive damping critical square
  integrable`, deep): reviewed all20 candidate/all20 source statements and
  the generated damping/periodicity chain. The suggested contraction is a
  Fokas-Lenells damping multiplier on another carrier; finite clock-periodic
  identities do not provide a cofinal PM norm budget. Other hits use finite
  cutoffs, assumed transport bounds, or unrelated projective Mobius maps.
  No applicable small-positive producer. Partial=false;63865 files;
  generation1173920,coverage1173929/current1173932; semantic coverage
  unmeasured, background refresh incomplete.
- Scratch1063 passed with empty Lean output (22 declarations). Promoted
  `PMPowerDampedMobiusCenteredEnergy` (226 lines), wired its unique umbrella
  import, and started targeted build/audits. It proves the actual two-way
  L2 equivalence and exact reciprocal energy identity. Its cofinal-energy
  implication does not discharge its energy premise.
- Lexical search1066 (`"centered" "divisor" "energy"`) returned19 hits in15
  modules,17 eligible after module caps. All17 displayed declarations were
  read from their source because lexical JSON omitted statements. They concern
  Xi divisors, root features, or centered spectral energies, not arithmetic
  divisor summation. No producer found. This lexical response supplies no
  coverage/freshness fields; no completeness claim is made.

- PM-31 centered-energy criterion fully audited:
  `PMPowerDampedMobiusCenteredEnergy` (226 lines /22 declarations), targeted
  old build119s, final actual leaf empty, all exact-body/name/API/unique-import/
  standard-axiom gates passed. For epsilon>0, actual Fermi-source canonical
  L2 admission is equivalent to integrability of the literal centered divisor
  discrepancy squared against dx/x^2. Backward finite-sum norms have the
  explicit bound (1+sqrt2) times the source norm; Fatou identifies the actual
  boundary-normalized remainder. The reciprocal energy identity, inherited
  epsilon>=1/2 admission, and cofinal weighted-energy RH receiver are proved.
  Combined: twenty-four leaves /5821 lines /428 audited declarations.
  Global lint has eleven unrelated unwired modules and three concurrently
  stale generated files; no owned/proof-debt finding. The energy receiver's
  small-positive premise remains open. New producer card:
  `pm-centered-divisor-dyadic-energy-budget`; scratch1068 checks the exact
  pointwise absolutely summable damped Nyman/fractional-part representation.
  No RH/negRH proof or small-positive geometric energy bound is claimed.

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
