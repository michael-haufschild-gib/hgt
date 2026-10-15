# TG: original source admission and cubic endpoint

Status: IN PROGRESS. RH remains unproved. Scope: route TG only.

## Contract

Unconditional Lean proof of `RiemannHypothesis`; no added axioms or unproved
premises. Corpus-first conjecture/attack/proof/formalization loop. No numerical
experiments, external searches, old research markdown reads, full builds, or
heartbeat increases. Final audits use `lake env lean`; targeted prerequisites
only, with `lake build --old` where needed. Wire completed modules into umbrella.

## Plan

1. Locate TG's live source-level obstruction. DONE, from Lean sources.
2. State and attack a structural conjecture on the original arithmetic source. IN PROGRESS.
3. Complete its paper proof before any Lean implementation.
4. Audit exact Lean statements, dependencies and axioms; continue toward RH.

`update_plan` is not exposed in this session; this card records the plan.
Serena symbol operations reject the ignored Lean tree; source reads are used.

## Source evidence inspected

- `FormationAnchoredCubicEndpoint`: RH iff every strict-right rectangle has an
  anchor with cubic trace norm < 1; equivalently endpoint trace norm tends to 0.
  Existing forward proof assumes a zero-free half-plane. It is not a producer.
- `SoninGammaClockNuclearLimit`: original Gamma cutoff convergence in the
  Schwartz-tested nuclear ideal; explicitly does not admit the joint source.
- `SoninPrimePolarFullResponse`: full native response and ground tail control
  each other with fixed constants.
- `SoninPrimePolarCofinalGroundEnergy`: cofinal strong ground admission iff
  `Summable soninPrimePolarGridEnergy`, with retained terminal square and an
  independently admitted within-cell correction.
- `SoninPrimePolarChronologicalWork`: exact prime jump and continuous polar
  energy work; no dissipativity assertion.
- `SoninPrimePolarJetLcmCovariance`: complete LCM jet decomposition, including
  above-cutoff labels and unequal polar cross terms; no infinite energy bound.
- `SoninGroundGridArithmeticSelection`: universal bounded prime/prime-power
  selection on the unchanged ground grid is impossible.
- `SoninDampedCurrentMeromorphicObstruction`: differentiated two-leg current
  has no fixed-L2 meromorphic continuation through zero damping. This does not
  exclude boundary admission of the logarithmic primitive.

Initial deep search: partial, coverage pending; candidate declarations were
source-only. Read source directly; none of these is being claimed freshly
compiler-audited. A targeted energy/cancellation deep search is running.

## Exact hard target

Write c_n = 1_{prime(n+2)} - original polar cell mass,
A_N = sum_{n<=N} c_n. Native admission requires
sum_N A_N^2 / ((N+2)(N+3)) < infinity.
Its proof must retain prime/polar signs and derive cancellation from actual
arithmetic. Universal selector boundedness and fixed-carrier continuation
are unavailable. No inference from those failures to failure of TG is valid.

## Conjecture interrogation

C1, exact main conjecture: `Summable soninPrimePolarGridEnergy`.
Verdict: SURVIVES PRELIMINARY ATTACK; NOT PROVED.
The proposed mechanism is compensation in the complete signed LCM covariance,
retaining all labels above the chronological cutoff and every polar cross term.
OPEN CORE: derive an arithmetic bound on the complete cumulative energy, not
from a renamed square-root prime-count error premise. Finite LCM identities
alone do not supply it. No theorem assuming C1 will be advertised as a proof.

### Attack on late compensation

Candidate mechanism: sufficiently late signed source interactions could erase
large energy accumulated on earlier annuli. Verdict: FALSE. This is a
restriction on a proposed mechanism, not a reason to abandon C1 or route TG.

Dependency-closed paper argument, using the audited source identities:
put B_n = groundEntry(a, log(n+2)), D_n = B_n-B_(n+1),
A_n = sum_(j<=n) c_j, and G_N = sum_(j<=N) c_j B_j. The exact identity is

    G_N = sum_(n<=N) A_n D_n + A_N B_(N+1).

The D_n are pairwise orthogonal, their squared norms are
2a/((n+2)(n+3)), and each D_n with n<=N is orthogonal to every B_j with j>N.
Consequently, for any v in the closed span of {B_j : j>N},

    ||G_N + v||^2 =
      2a sum_(n<=N) A_n^2/((n+2)(n+3)) + ||A_N B_(N+1)+v||^2.

Orthogonality extends to the closed span because inner products are continuous.
The minimum over that entire future space is attained at v=-A_N B_(N+1).
Thus the displayed accumulated energy is the exact future-repair floor.
No restriction to linear choices of v was used: arbitrary adaptive/nonlinear
selection of a vector in the same future span cannot change this floor.

Positive survivor: exact immutable historical energy and attained endpoint
repair. Internal novelty verdict: REDISCOVERED from the existing orthogonal
decomposition, not a new result. The decomposition, orthogonality and resulting
cofinal criterion are already Lean-proved in `SoninPrimePolarCofinalGroundEnergy`;
no duplicate leaf module was added. The arbitrary-closed-span formulation above
is paper-derived, not separately formalized or claimed as a new Lean theorem.

### Other attack outcomes

- Algebraic jet idempotence cannot be promoted to a universal bounded physical
  prime selector: `SoninGroundGridArithmeticSelection` already disproves it.
  This rejects that proof step, not source-specific compensation.
- A one-sided sign premise is not justified by the source's energy derivative.
  `PrimeCountingLogIntegralNegativeValues` proves two-sided Littlewood
  oscillation for pi-li. Exact transfer to this polar normalization was NOT
  formalized; no new native sign-oscillation theorem is claimed.
- `RegularizedLogZetaAbscissa` identifies subcritical prime-error growth laws
  with zero-free half-planes. Importing such a law would reintroduce the hard
  conclusion as a premise.
- A multiplicative damping/conditional-covariance approach was inspected via
  `RoutePPrimeCovarianceBudget` and `EulerDeletionPrimeCountAmplification`.
  The former bounds covariance by the squared mean head; it does not bound
  that head or identify TG's original source. The latter already disproves
  uniform damping contraction on the literal arithmetic source itself.
  Thus inverse-square noise budgets do not close C1. Any use of the
  prime-count endpoint jet must preserve cancellation at the actual u=1
  endpoint and prove its own uniform source-domain admission.

## Verification and next proof attempt

`lake env lean GaloisForLFunctions/RHTower/SoninPrimePolarCofinalGroundEnergy.lean`
completed with exit 0 and no output on 2026-10-15. This checks the existing
native criterion, not C1 and not RH. Scratch `lake env lean` axiom audit also
passed: `soninPrimePolarGridSource_norm_sq` and
`soninPrimePolarCellSource_cofinal_limit_iff_energy` use only `propext`,
`Classical.choice`, `Quot.sound`.

`scripts/formal_tools.py lint` exited 1: pre-existing size warnings and four
unreachable modules: `EvenSectorAbelAveraging`, `EvenSectorAbelLaplace`,
`EvenSectorFarBumpPoleFreeCombination`,
`WeilPhiDoobArchimedeanJumpAndHalfLineFolding`. No Lean files were changed by
this pass; do not claim the repository-wide lint gate is green. These files
are outside TG's current scope; existing shared umbrella edits were preserved.

Next proof attempt remains C1: use the complete signed LCM incidence formula
to control prefix energy at its creation. Do not discard nonclock/above-cutoff
fibres, replace original primes by an artificial mask, assume RH-dependent
growth, or seek future cancellation of historical annuli. Both signs of the
arithmetic discrepancy must remain admissible.

## Anti-theatre / anti-laziness audit

No new scientific knowledge or RH proof produced in this pass. The useful
output is an audited exact target and elimination of an invalid compensation
mechanism. Do not count the known decomposition as novelty or spend the next
pass formalizing another equivalent gate. No difficulty/effort rationale was
used to retire TG. Main paper proof and its Lean formalization remain open;
the next cycle must work on the actual arithmetic compensation law.

All search jobs and the owned Lean audits completed. Temporary search JSON
and scratch Lean audit are removed after recording their evidence here.
Only this new card was written; existing Lean worktree edits were untouched.

External SOTA/novelty phases omitted by explicit user override. No external
novelty claim. Mathematical identities and known bridges do not count as RH.
