# PM centered Haar cutoffs and the endpoint trace

Type: THEOREM / exact approximation criterion
Stage: 3 — formalized; arithmetic producer remains open
Parent: [PM31](../1-in-progress/pm-power-damped-mobius-haar.md)
Producer: [signed divisor energy](../1-in-progress/pm-centered-divisor-dyadic-energy-budget.md)
Origin: [fully audited raw-prefix no-go and universal profile](../5-failed/pm-positive-divisor-haar-boundary-profile.md).

## Exact candidate

Fix epsilon>0. Use the actual divisor remainder R_epsilon, its density
alpha_epsilon, positive Haar prefix P_epsilon,N, and the universal profile
beta from the boundary-profile leaves. For integer N>=1 define

    B_epsilon,N(t) = P_epsilon,N(t) - alpha_epsilon*N*beta(Nt),
    G_epsilon,N(t) = R_epsilon(min(N,1/t)).

The candidate approximation uses B, not the raw positive Haar prefix.
The arithmetic producer would be a common canonical L2 budget along
cofinal cutoffs at cofinal arbitrarily small positive dampings. This bound
is unproved and must not be inserted as a hidden premise of an RH claim.

## Paper bridge

The clipped-count identity gives, for t>0,

    B_epsilon,N(t) = G_epsilon,N(t) - 2*G_epsilon,N(2t).

The clipped primitive equals F_epsilon(t)=R_epsilon(1/t) when t>=1/N
and equals R_epsilon(N) when 0<t<=1/N. Its exact energy is

    integral |G_epsilon,N|^2 dt
      = integral_0^N |R_epsilon(x)|^2/x^2 dx + |R_epsilon(N)|^2/N.

Every finite clipped primitive is admitted: the remainder is locally
bounded away from infinity, the initial physical interval is constant,
and the t>1 tail is -alpha_epsilon/t.

Assume actual admission for the following classification. Along any
integer cutoffs N_j -> infinity, the actual primitive's L2 mass on
(0,1/N_j] tends to zero. The difference G_Nj-F differs from the constant
box R(N_j)*1_(0,1/N_j] by precisely that vanishing tail. Hence

    G_Nj -> F strongly in L2
      iff |R(N_j)|/sqrt(N_j) -> 0.

The dyadic difference S(g)=g-2g(2t) satisfies

    (sqrt2-1)||g||_2 <= ||S(g)||_2 <= (sqrt2+1)||g||_2,

by the exact dilation norm and the two triangle inequalities. Therefore
the same endpoint-trace condition is equivalent to B_Nj -> A_epsilon
strongly in L2, under actual admission. A real Bochner integral of squared
error must never replace the admission requirement: its junk value for
nonintegrable functions would make that an invalid criterion.

## Cofinal cutoff selection from admission

The discrete-energy leaf gives summability of
w_n=|R_epsilon(n)|^2/(n(n+1)), n>=1. On each block N<=n<2N,
choose an index with w_n at most the block average. Since n+1<=2N,

    |R_epsilon(n)|^2/n <= 2*sum_(N<=m<2N) w_m.

For N=2^j these right sides tend to zero. Chosen indices lie in disjoint
ordered dyadic blocks, so form a strict increasing cofinal sequence with
vanishing endpoint trace. This is a finite averaging argument, with no
numerical experiment or assumption of bounded cumulative coefficients.

Consequently actual admission implies a strongly convergent cofinal
sequence of repaired prefixes and thus a common budget on that sequence.
Conversely a cofinal common budget, together with exact pointwise
stabilization above 1/N, implies actual admission by Fatou. This gives an
exact cofinal repaired-prefix criterion; it does not manufacture the bound.

## Prior research / novelty audit

- PM31 divisor, centered-energy, discrete-energy and positive-prefix
  leaves provide the exact arithmetic identities and carrier transfers.
- Search1081 (`centered clipped summatory boundary trace cofinal cutoff
  Hilbert convergence`, deep): all20 candidate/all20 source statements
  and both proposed steps reviewed. No exact clipped PM bridge returned.
  Other cutoff approximations assume compact inputs or concern spectral
  traces. The unsigned divisor square-root bound concerns a half-order
  Abel sum of a logarithmic-factorial/divisor-summatory defect, not R_epsilon.
  Partial=false; 63906 files; generation1174871,coverage/current1174877;
  semantic coverage unmeasured, background refresh incomplete.

## Status / next

Paper proof and both Lean leaves are fully audited; see the final entries below.
The exact approximation criterion is formalized. The actual signed energy
producer remains open. The stronger endpoint-atom correction has a separate
active card. No RH/negRH proof.

- Paper dependency audit: the exact clipping identity follows from the
  clipped-count leaf and scaled minimum identity; finite admission uses
  |R_epsilon(x)|<=(1+|alpha_epsilon|)x for epsilon>=0 and the admitted
  min(a,1/t) envelope. Reciprocal change of variables yields the exact
  truncated energy plus endpoint trace; splitting the physical ray gives
  the equivalent initial-box plus tail identity. The dyadic difference is
  bounded above and below by sqrt2+1 and sqrt2-1, respectively, directly
  from the already audited dilation norm. No arithmetic estimate is
  assumed in these finite identities.
- Scratch1082 passed these clipping/energy/dyadic-norm proofs with empty
  diagnostics. Added repaired-prefix measurability, exact pointwise
  stabilization and limit; final scratch check running before promotion.
  Endpoint convergence classification and cofinal selection remain to
  formalize. Relevant source follow-up: the corpus Mertens mean-square
  exponent-law proof uses finite dyadic averaging for a different source;
  the same elementary selection mechanism is applicable here, without
  importing its Mertens hypotheses or conclusions. Mathlib's shifted
  series-tail theorem tends to zero, but summability must be retained for
  finite-block domination (otherwise its tsum has a junk value).
- Full scratch1082 passed with empty diagnostics. Promoted and wired
  `PMPowerDampedMobiusClippedHaarSource` (242 lines /22 declarations).
  Targeted old build49s passed; exact-body, all-name/API, unique-import and
  proof-debt audits passed. Actual final leaf audit running; axiom audit
  next. Global lint: ten unrelated unwired leaves, stale LEAN_GAPS and
  LEAN_OVERVIEW, no owned/proof-debt finding. Scratch1083 now contains the
  two-sided error/endpoint energy inequalities, vanishing initial L2
  tails, exact endpoint convergence criterion, and repaired-prefix
  convergence transfer via dyadic coercivity. Awaiting audit completion
  before compiling this next scratch; no convergence claim certified yet.

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
- First convergence scratch check exposed only integrability-wrapper,
  pointwise-function reduction and indicator syntax issues; corrected.
  Consolidated endpoint criterion, finite dyadic averaging, strict
  increasing trace-zero selection, and exact cofinal repaired-budget
  receiver in scratch1083 for one coherent leaf. Current check running;
  no promotion yet. Search1085 returned no actual repaired covariance
  bound (full statement/chain audit logged on the producer card).
- Consolidated scratch1083 reached a single local tactic-sequencing issue
  in the positivity of the dyadic block size; all other statements,
  including the strict cofinal selection and exact repaired-budget iff,
  passed that check. Replaced the ambiguous one-line nested proof with
  an explicit two-line proof; clean scratch check running. Do not promote
  until it exits successfully.
- Stronger survivor exposed by the exact clipping decomposition has a new
  paper card: [endpoint-corrected Haar prefix](pm-endpoint-corrected-haar-prefix.md).
  Subtracting the exact endpoint Haar atom should turn the primitive into
  its zero-truncated tail and remove the cofinal endpoint choice from the
  corrected family's convergence theorem. Targeted search1088 is running.
- Clean consolidated scratch1083 passed with empty diagnostics. Promoted
  and wired `PMPowerDampedMobiusHaarCutoffTrace` (324 lines /16 declarations).
  Targeted old build15s passed. Final actual leaf and exhaustive audits
  are running. The leaf proves both primitive and repaired-prefix trace
  classifications under actual admission, selects a strict cofinal
  trace-zero sequence from the actual discrete energy, and proves exact
  equivalence of actual admission with a cofinal common repaired-prefix
  norm budget. Its RH receiver retains the unproved arithmetic budget
  premise explicitly. No unconditional RH conclusion is claimed.

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
