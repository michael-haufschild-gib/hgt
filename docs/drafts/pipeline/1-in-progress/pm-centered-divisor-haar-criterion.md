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
