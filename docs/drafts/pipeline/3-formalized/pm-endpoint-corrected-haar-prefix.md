# PM endpoint-corrected Haar prefixes

Type: THEOREM / exact full-sequence approximation classification
Stage: 3 — formalized
Parent: [PM31](../1-in-progress/pm-power-damped-mobius-haar.md)
Origin: [centered cutoff trace](../3-formalized/pm-centered-haar-cutoff-trace.md)
Producer: [actual signed energy](../1-in-progress/pm-centered-divisor-dyadic-energy-budget.md)

## Formalized classification exposed by the clipping audit

Fix epsilon>0 and an integer N>=1. Let P_N be the raw positive-divisor
Haar prefix, alpha its density, beta the universal boundary profile, and
R the centered divisor remainder. The density-repaired prefix is
B_N=P_N-alpha*N*beta(Nt). Define a second correction

    T_N(t)=B_N(t)-R(N)*H_0(Nt).

Candidate: under actual canonical L2 admission, T_N converges strongly
in L2 to the actual source along EVERY integer cutoff. Conversely, a
common canonical norm bound for T_N forces actual admission. This is an
approximation classification, not an unconditional arithmetic bound.

## Dependency-closed paper argument

Write F(t)=R(1/t), Sg(t)=g(t)-2g(2t), and
G_N(t)=R(min(N,1/t)). The preceding clipping leaf proves B_N=S G_N.
For t>0, let J_N(t)=1_(0,1/N](t). The supported Haar cutoff identity gives
S J_N(t)=H_0(Nt), including the two endpoints. Since

    G_N(t)-R(N)J_N(t)=F(t)*1_(1/N,infinity)(t),

one obtains the exact identity

    T_N = S(F*1_(1/N,infinity))
    T_N-A = -S(F*1_(0,1/N]).

Each T_N is admitted unconditionally at epsilon>0: B_N is admitted by the
finite clipping leaf, and the extra term is one admitted Haar dilation.
For an admitted actual source, F is admitted by the centered-source
criterion. Its initial L2 mass tends to zero. The audited dyadic upper
norm bound sqrt2+1 therefore makes the displayed error tend to zero for
all N. This removes the endpoint trace and any cofinal selection from
this more accurately corrected family.

Every T_N agrees exactly with A for t>1/N. Thus Fatou proves admission
from any bounded cofinal sequence of T_N; a full-sequence common norm
bound is equivalent to admission. Strong convergence supplies the common
bound in the reverse direction, including finitely many initial terms.

## Arithmetic target and limits

The correction uses the exact arithmetic endpoint R(N), not a claimed
small estimate for it. It does not estimate the remaining signed energy
of T_N. No small-positive admission or RH conclusion follows without
that bound. Its value is an explicit full-sequence family whose cutoff
trace is removed exactly, and an error localized by the original source.

## Audit status

The exact identities, finite admission, quantitative bounds, full-sequence
convergence under actual admission and budget equivalence are formalized
in `PMPowerDampedMobiusEndpointHaar`. All215 lines /17 declarations passed
targeted build, final actual-leaf, exhaustive API/import and standard-axiom
audits. The arithmetic small-positive budget remains open. Historical
progress entries below record the implementation; final audit is at end.

## Stronger quantitative survivor

For an admitted centered source, the exact truncation identity gives

    ||T_N||_2 <= (sqrt2+1)||F||_2,
    (sqrt2-1)||F*1_(0,1/N]||_2
      <= ||T_N-A||_2 <= (sqrt2+1)||F*1_(0,1/N]||_2.

The first bound holds at every positive integer cutoff, so no finite-head
patching is needed. The second gives an exact two-sided classification of
the error by the actual source's initial L2 mass. These are consequences
of the audited generic dyadic bounds, once the endpoint-atom identity is
proved. The condition epsilon>0 is essential when obtaining centered
admission from actual-source admission: the reciprocal zeta definition
at epsilon=0 uses its assigned pole value and is not the positive-density
limit. Do not extrapolate the positive-damping classification to zero.

- Search1088 (`centered remainder clipped cutoff endpoint Haar atom
  correction strong approximation`, deep): all20 candidate/all20 source
  statements and both proposed ingredient steps reviewed. Existing Haar
  cutoff identities supply the exact box difference. Other clipped Abel,
  spectral cutoff, Bernoulli-tail and endpoint-correction sources use
  different carriers. No exact corrected PM family returned. Generated
  endpoint quadrature bound is irrelevant to the identity. Partial=true,
  unfinished semantic_retrieval; 63931 files; index1175442,
  coverage/current1175450; semantic coverage unmeasured and background
  refresh incomplete. The available applicable Haar identities suffice
  to begin the paper-proved exact correction; no exhaustive novelty claim.
- Scratch1089 now contains exact initial-box/Haar correspondence,
  corrected-prefix definition, finite admission, exact truncated primitive
  and error identities, pointwise stabilization, quantitative energy/error
  bounds, full-integer-cutoff convergence under actual admission, and
  equivalence with a full-sequence energy budget. It imports the preceding
  cutoff-trace leaf, whose audit is still running. This new scratch has
  not been compiled; its statements remain uncertified.

- Preceding cutoff-trace leaf fully audited; its card moved to formalized.
  Scratch1089 first compiler check is next.
- First scratch1089 check found dependent-ite rewriting and explicit
  indicator-set inference issues, plus an unspecified cutoff in one
  MemLp indicator lemma. Replaced iff rewrites by simp and supplied exact
  Ioi membership/set arguments. All later quantitative/convergence/iff
  proofs passed that check; clean recheck running before promotion.
- Search1090 supplies no damped predictable-drift bound for this family;
  its complete statement/chain audit is recorded on the producer card.
  Removing the exact endpoint packet is not evidence that the entire
  predictable drift is controlled.
- Clean scratch1089 passed with empty diagnostics. Promoted and wired
  `PMPowerDampedMobiusEndpointHaar` (215 lines /17 declarations). Targeted
  old build and exhaustive audits running. The exact corrected family is
  the dyadic difference of the zero-truncated centered source; both its
  energy bound and its two-sided error comparison are proved under
  actual admission. Full-sequence convergence and the exact full-budget
  admission criterion are included. The actual small-positive budget is
  still the unproved arithmetic producer.
- Exact-body, all-name/API, unique-import and proof-debt audits passed for
  the 215-line /17-declaration endpoint leaf. Targeted build still running;
  final actual leaf and standard-axiom audit remain. Global lint has twelve
  unrelated unwired leaves (now including WeilConeWindowRigidity and
  WeilFullConeAtomExtraction), with no owned/proof-debt finding.
- Targeted old build294s passed. Final actual leaf audit now running;
  all-declaration standard-axiom audit follows it. No changes to the
  successful scratch body were needed after promotion.
- Final actual leaf passed with empty diagnostics. All17 declaration
  axiom reports are checking. Next arithmetic calibration has its own
  paper card: [divisor second-moment density](../1-in-progress/pm-divisor-second-moment-density.md).
  It seeks the exact centered diagonal's logarithmic coefficient and the
  cross cancellation required by admission, not an unsupported transfer
  from stationary variance to the anchored energy.

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
