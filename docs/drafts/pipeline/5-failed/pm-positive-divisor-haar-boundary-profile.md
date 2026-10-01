# PM positive-divisor Haar cutoff: escaping boundary profile

Type: NO-GO / exact positive survivor formalized
Stage: 5 — failed raw-cutoff budget; positive survivor formalized
Parent: [PM31](../1-in-progress/pm-power-damped-mobius-haar.md)
Producer target: [actual centered divisor energy](../1-in-progress/pm-centered-divisor-dyadic-energy-budget.md)

## Candidate and paper obstruction

Let epsilon>0, c_epsilon(n)=sum_{d|n} mu(d)d^(-epsilon),
C_epsilon(x)=sum_{1<=n<=x}c_epsilon(n), and
alpha_epsilon=1/zeta(1+epsilon). Existing PM31 leaves prove
0<=c_epsilon(n)<=1 and C_epsilon(x)/x -> alpha_epsilon.
The density is real and strictly positive (nonnegative mean, nonzero zeta
reciprocal on Re(s)>1).

Consider the literal finite positive-divisor Haar expansion
P_epsilon,N(t)=sum_{1<=n<=N}c_epsilon(n)H_0(nt).
It converges pointwise to the actual power-damped Fermi source.
Candidate: these natural positive-coefficient Haar prefixes have a common
canonical L2 budget at small positive damping.

Paper counterargument: on 0<t<=1/(2N), every H_0(nt)=-1, hence
P_epsilon,N(t)=-C_epsilon(N). Therefore
integral |P_epsilon,N|^2 dt >= C_epsilon(N)^2/(2N), which tends to infinity.
This obstruction holds at EVERY epsilon>0, including the independently
proved admitted range epsilon>=1/2. It is an obstruction to this sequence
of approximants, not to actual-source admission.

## Positive survivor: universal boundary profile

Define beta(u)=min(1,1/u)-2min(1,1/(2u)) for u>0. Then beta=-1 on
(0,1/2], beta=1-1/u on (1/2,1], and beta=0 on (1,infinity).

Exact finite identity:
P_epsilon,N(t)=C_epsilon(min(N,1/t))-2C_epsilon(min(N,1/(2t))).
Thus for each u>0,
P_epsilon,N(u/N)/N -> alpha_epsilon beta(u).
The mean theorem applies at N*min(1,1/u) and N*min(1,1/(2u)); both
fixed multipliers are strictly positive. This includes all endpoints.

Since 0<=c_epsilon<=1, the rescaled prefix is bounded in norm by
3min(1,1/u), whose square is integrable on the positive ray.
Dominated convergence gives strong L2 convergence to alpha_epsilon beta.
Consequently the exact leading energy is

    (1/N) integral |P_epsilon,N(t)|^2 dt
      -> |alpha_epsilon|^2 (2-2log 2).

The constant follows by integrating beta^2 on (0,1/2] and (1/2,1].
Also integral beta=-log 2. Each finite Haar prefix has mean zero, whereas
the actual source has mean alpha_epsilon log 2: the negative boundary
packet explains the missing mean and prevents L1 convergence of these
uncorrected prefixes. These are analytic identities, with no numerical
experiments.

## Paper audit / limitations

- Keep the exact original physical measure dt.
- Density centering is required to remove the deterministic boundary
  packet before considering a uniform energy budget.
- The scaled profile theorem does not control the residual after removing
  that leading packet; a little-o(N) energy remainder still need not be
  bounded. No implication to small-positive admission is asserted.
- Prior PM31 finite Haar identities and mean asymptotics supply the
  arithmetic input. Search1078 is checking corpus novelty/applicability.
- Do not retire the candidate until the strongest positive survivor has
  passed paper and Lean audits.

## Lean work plan

1. Define finite positive-divisor Haar prefix; prove clipped-count identity,
   pointwise stabilization and exact initial plateau.
2. Prove the rescaled universal profile, its L2 convergence and energy
   asymptotic without assuming actual-source admission.
3. Prove unbounded cutoff energy and exact escaping mean; audit all leaves,
   then retire only this cutoff-budget candidate.

Status: closed. Dependency-closed paper proof and both Lean leaves fully audited; see final audit entry below. Earlier progress entries are historical.

## Research audit

- Search1078 (`positive divisor Haar cutoff boundary concentration energy
  rescaled profile`, deep): all20 candidate/all20 source statements and
  both proposed ingredient steps reviewed. The existing Haar cutoff
  integrals and cutoff representation apply. Other rescaling/packet
  results use different carriers or retain an asymptotic premise.
  Twisted-Mobius prime-product identity duplicates the known coefficient
  factorization; no boundary-profile or cutoff-energy asymptotic returned.
  Partial=false; 63892 files; generation1174501,coverage1174509/current1174510;
  semantic coverage unmeasured, background refresh incomplete.

- Scratch1079 (`/tmp/pm_positive_haar_profile_1079.lean`) now contains the
  finite prefix, clipped-count identity, nonnegative divisor-sum bounds,
  nonzero density, scaled mean theorem, pointwise universal profile and
  its 3min(1,1/u) envelope. Initial compiler issues corrected; current
  check running. Added exact stabilization, initial plateau, energy lower
  bound and zero integral for the next check. No new leaf promoted yet.
- Remaining positive-survivor work: integrate the profile, prove strong
  L2 convergence by the explicit square-integrable envelope, obtain the
  sharp linear energy asymptotic, then retire the failed cutoff budget.
- Scratch1079 passed with empty diagnostics. Promoted and wired
  `PMPowerDampedMobiusPositiveHaarPrefix`; targeted old build and audits
  started. The first leaf contains exact cutoff geometry, pointwise
  rescaled profile with a common envelope, initial-plateau energy lower
  bound, and zero integral of every finite prefix. The strong L2 profile
  and sharp energy asymptotic are the next leaf; scratch1080 prepared,
  awaiting the first leaf's dependency build. Candidate stays in progress.
- First leaf is 239 lines /21 declarations. Targeted old build64s and
  final actual leaf passed with empty diagnostics. Exact-body,
  exhaustive-name/API, unique-import and proof-debt audits passed. All
  declaration axioms currently checking. Global lint: eleven unrelated
  unwired leaves (latest includes ZetaLocalWindowTail), plus concurrently
  stale LEAN_GAPS/LEAN_OVERVIEW; no owned finding.
- Scratch1080 now includes the piecewise universal profile, an integrable
  squared envelope, strong L2 convergence argument via dominated
  convergence, and exact profile energy 2-2log2. Not compiled yet: its
  dependency leaf was being audited. Still needed: exact rescaling of
  finite-prefix energy, sharp asymptotic/divergence, and mean defect audit.

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

## Follow-up exposed by the profile (not yet audited)

Subtracting alpha_epsilon*N*beta(Nt) from the raw prefix gives exactly
R_epsilon(min(N,1/t))-2R_epsilon(min(N,1/(2t))). Thus a candidate repaired
approximation is the dyadic difference of the centered remainder clipped
at N. Its primitive equals the actual primitive for t>=1/N and equals
R_epsilon(N) on the remaining initial interval. Its squared energy is
the truncated centered energy plus |R_epsilon(N)|^2/N.

This suggests a sharper follow-up: along cofinal integer cutoffs, strong
L2 convergence should be controlled exactly by the endpoint trace
R_epsilon(N)/sqrt(N), once actual admission is available. Admission alone
does not immediately give that endpoint control at every cutoff; a
cofinal selection may be needed. This is a new conjecture for a separate
paper/novelty audit, not part of the presently verified profile result.
Search1081 checks existing clipped-boundary/cofinal Hilbert bridges.

- Scratch1080 passed the strong L2 profile and exact energy constant with
  only one sequencing-style warning; that warning was removed. Extended
  scratch now adds profile mean -log2, exact original/rescaled energy
  identity, sharp linear-energy limit and divergence, no common energy
  budget, and a positive lower bound on the L1 error from the exact mean
  defect. Extended check running; no second leaf promoted yet.
- Search1081 (`centered clipped summatory boundary trace cofinal cutoff
  Hilbert convergence`, deep): all20 candidate/all20 source statements
  and both generated ingredient steps reviewed. Plemelj/spectral cutoff
  traces and radial compact-source approximations do not supply the PM
  clipped-remainder theorem. The unsigned divisor square-root channel is
  a separate half-order Abel carrier, not the PM cumulative coefficient.
  Partial=false; 63906 files; generation1174871,coverage/current1174877;
  semantic coverage unmeasured and background refresh incomplete.
- Full scratch1080 passed with empty diagnostics. Promoted and wired
  `PMPowerDampedMobiusHaarBoundaryProfile`; targeted old build and full leaf
  audits started. It includes strong L2 convergence of the rescaled
  prefixes, exact profile energy/mean, the sharp linear energy asymptotic,
  divergence at every positive damping, and failure of unscaled L1
  convergence with its exact positive mean-defect lower bound. The raw
  cutoff candidate will move to failed only after these gates finish.
- Second leaf: 292 lines /19 declarations. Targeted old build46s passed;
  exact-body, all-name/API, unique-import and proof-debt gates passed.
  Final actual leaf running before all-declaration axiom audit. Global
  lint has eleven unrelated unwired leaves and concurrent staleness of
  all three generated docs; no owned or proof-debt finding.
- Final actual second leaf passed with empty diagnostics; all-declaration
  axiom audit running. Follow-up paper bridge now has its own active card:
  [centered Haar cutoff trace](../3-formalized/pm-centered-haar-cutoff-trace.md). The raw
  prefix obstruction and its universal profile remain separate from that
  repaired-prefix criterion and the unproved signed energy producer.

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
