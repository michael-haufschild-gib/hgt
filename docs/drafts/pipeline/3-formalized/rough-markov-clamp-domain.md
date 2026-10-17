# Actual rough Markov clamp and local energy localization

- **ID:** rough-markov-clamp-domain
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** The actual physical L² primitive domain is stable under unit clamping,
  with exact additive energy splitting, firm mixed-graph/form contraction and complete
  compact-source graph equality classification.

## Proven result

For G=c+primitive q and T(a)=min(max(a,0),1), construct

    q_T=(modulusVelocity q c−modulusVelocity q (c−1))/2,
    q_R=q−q_T.

Proved exact anchored primitives T(G), G−T(G), absolute continuity, and
q_T=q*1_{0<G<1} a.e. The residual carries the complementary derivative energy.
Every oriented interval and its weighted logarithmic counterpart satisfy
E(q)=E(q_T)+E(q_R). Every finite edge budget and total mixed congestion have
the same exact split, including infinite total energies.

For the complete diffuse/countable-line graph, J(q_T)+J(q_R)≤J(q). Source mass
satisfies the same firm inequality, hence so does the full admitted compact form.
The removed state's weighted variance is at most sinh(2B)[J(q)−J(q_T)].
Graph energy is unchanged iff f is constant on all nonzero source points or
all those source values lie in [0,1]. Constants outside the band must remain
in the classifier. Zero/disconnected sources and arbitrary atom weights are
included without extra analytic admission premises.

## Proof and boundaries

Paper: `docs/reports/BiScaleUncertainty/RoughMarkovClamp.md`.
Two modulus primitives give the construction; the zero-level derivative law
handles thresholds. Scalar monotonicity and Lipschitz contraction make the
retained/removed jump interaction nonnegative. Compact variance rigidity and
the singleton nonzero fibers of a−T(a) give the equality classifier.
Additive orthogonality does not imply an exact nonlocal jump split. Source-mass
equality is a separate condition. No closed SourceGraph or unitary affine claim.

## Evidence

- `RoughSobolevClamp.lean`: 25 public theorems, 3 definitions.
- `RoughClampGraphControl.lean`: 11 public theorems.
- Both final serial direct `lake --old env lean -o <normal-output> <leaf>` checks
  passed without diagnostics; outputs postdate final sources.
- All 39 public declarations audited with exact name coverage: only `propext`,
  `Classical.choice`, `Quot.sound`. Ten main signatures have no extra analytic premise.
- Both imports, field maps, all 36 theorem names in generated API and whitespace
  checks pass. Global formal lint passes; existing large-file warnings remain.
- No full/umbrella build, numerical experiment, added axiom or heartbeat increase.
- Fresh corpus query completed without partial stages/errors; all 20 candidates
  and 20 source arguments inspected. Snapshot freshness and semantic coverage
  are incomplete, so absence/novelty is not established exhaustively.

One connected contribution, certified **8/100**. All owned processes terminal.
This turn is **progress**. Next conjecture:
`../0-backlog/infinite-coprime-trace-extension.md` (unproved, uncounted).
