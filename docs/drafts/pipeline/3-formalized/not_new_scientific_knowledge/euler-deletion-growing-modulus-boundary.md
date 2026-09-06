# Growing deletion moduli: exact tail admission boundary

- **Stage:** 3-formalized / not_new_scientific_knowledge
- **Type:** THEOREM (Lean), auxiliary classification; proposed RH mechanism rejected at its first gate
- **RH status:** no new zero-forced relation or RH implication.
- **Novelty status:** elementary periodic Abel summation and a single-jump lower bound; not a qualifying novel RH architecture.

## Question and intended chain

The proposed chain was literal zeta coefficients → simultaneous arithmetic histories at a zero
→ a new cross-modulus compatibility relation → exclusion of off-line zeros. The corpus already
constructs all finite word lengths in one norm limit for each fixed modulus when Re(s)>1/2.
The test here asks whether making the modulus range grow supplies the missing relation.

Write a_q(n)=1-(q+1)[q+1 divides n], so q denotes one less than the actual modulus, and
P_q(s,N)=sum_(1<=n<=N) a_q(n)n^(-s). The existing exact coefficient prefix is N mod (q+1).
Its Abel tail bound is proportional to q(N+1)^(-Re(s)). No zero assumption enters that bound.

## Closed statement and proof

For sigma=Re(s)>0, N>=1 and 1<=A<=N, define the tail oscillation as
sup_(q<=A, K,M>=N) |P_q(s,K)-P_q(s,M)|. It has the two bounds

    A [2(N+1)]^(-sigma)
       <= tail oscillation
       <= 2 A (1+|s|/sigma) (N+1)^(-sigma).

The upper bound applies the existing finite Abel block estimate at min(K,M), whose negative
power is at most (N+1)^(-sigma). No passage to an infinite limit is needed for either bound. For the lower bound choose q=A and the first positive multiple
k of A+1 strictly after N. Then N<k<=N+A+1<=2(N+1). The difference between prefixes k and
k-1 is exactly -A k^(-s), of norm A k^(-sigma).

Consequently, for any integer-valued budget A(N)<=N, uniform tail convergence over q<=A(N)
is equivalent to A(N)(N+1)^(-sigma) tending to zero. This is an ordinary cutoff resource
law, independent of whether zeta(s) vanishes. For sigma<=1, the maximal budget A(N)=N
already fails to converge uniformly; allowing every modulus fails as well.

The critical-strip statement is stronger: for every 0<sigma<=1 and every natural-valued A,
without a growth or monotonicity assumption,

    uniform tails over q<=A(N)  iff  A(N)(N+1)^(-sigma) -> 0.

To remove the budget restriction, uniform tails first force A(N)<N eventually. Otherwise the
sub-budget q<=N has tail oscillation at least 2^(-sigma)/2, since
N(N+1)^(-sigma)>=N/(N+1)>=1/2 for N>=1. Apply the bounded-budget criterion to min(A(N),N),
which then equals A(N) eventually. The reverse direction uses the same upper bound directly.
The bounded-budget theorem holds for all sigma>0; the unrestricted-budget theorem stated here
is limited to 0<sigma<=1. No result for arbitrary budgets at sigma>1 is asserted in this leaf.

## No-go closure

- **Killing mechanism:** a single deletion event prevents modulus-uniform scalar convergence
  throughout 0<Re(s)<=1. A zero cannot remove that event from the literal prefix sequence.
- **Positive survivor:** the exact growing-budget criterion above, including arbitrary budgets in
  the critical strip. It quantifies precisely which restricted uniformity survives.
- **Interpretation:** within the stated domain this convergence demand depends only on Re(s) and
  the budget, so points with the same real part have the same admission criterion. It does not rule out a separate relation between completed histories.
- **Status:** dependency-closed paper proof and ten closed Lean theorems in
  `formal/GaloisForLFunctions/RHTower/EulerDeletionGrowingModulus.lean`, namespace
  `RHTower.DeletionModulusBoundary`. The exact capstone is
  `uniformTails_iff_budget_decay_critical`; the negative corollary is `not_all_moduli_uniform`.
  This positive classification closes the no-go audit; it is not being presented as new
  scientific knowledge or as a qualifying RH architecture.

## Source and scope audit

Current-corpus searches paired with statement/proof inspection: `refinement history`,
`Euler deletion refinement`, `periodic renormalized`, `Euler deletion mean`,
`renormalized shuffle`, `deletion uniform`, `modulus cutoff`, `deletion tail bound`,
`modulus uniform`, `deletion bound`. Searches screen declarations and do not establish novelty.
Read `EulerDeletionWordHistory` (all-depth convergence is only for fixed q),
`EulerDeletionQuasiShuffleSecondConvergence` (explicit q-dependent Abel constant),
`EulerDeletionQuasiShuffleConvergence` (literal coefficient and remainder), and
`DirichletUniformAbel.norm_dirichletSum_sub_partialSum_le`.

No experiment is required: the proposed unrestricted uniformity is decided by exact arithmetic.

## Literature and formal verification

The analytic parent is classical Abel summation. Keith Conrad's
[Dirichlet Series, Theorem 9 and its proof on pages 2–3](https://kconrad.math.uconn.edu/math5121s18/handouts/dirichletseries.pdf)
explicitly derive the bounded-prefix tail estimate. The matching lower bound here uses only the
literal deletion event. No claim of absence from the literature is made for this elementary
combination. The source was opened and its displayed derivation inspected.

- Scratch proof and direct production-file check: `lake env lean <file>` passed.
- Scratch `FinalAudit.lean`: all ten theorem axiom reports contain only `propext`,
  `Classical.choice`, and `Quot.sound`; no numerical certificate or additional postulate.
- Final narrow build:
  `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionGrowingModulus`
  passed; only this leaf was newly built. A pre-existing unused-variable warning was replayed
  from `HTGeometry.PolydiscWeierstrass`. The 8675-job total includes cached dependencies.
- The leaf is wired into `RHTower.lean`; no umbrella or full build was run.
- Scratch directory: `/tmp/hgt-modulus-boundary-RWEMcW`.
- `python3 scripts/formal_tools.py index` regenerated the three formal indexes; the research
  tool retrieves both exact budget criteria from the new module.
- `python3 scripts/formal_tools.py lint` passed, with existing large-file warnings only.
- Owned-file whitespace checks, the umbrella import, promoted-card link, and proof-source gate
  passed. All Lean processes started for this proof and audit are terminal.
