# HB diagonal Peierls source-incidence rigidity

- **ID:** HC70
- **Stage:** 3-formalized
- **Type:** THEOREM / LEAN-PROVED GREEN-JUMP RIGIDITY CLASSIFICATION / HARD FRONTIER
- **Routes:** HB, FZZ-P, RBH, PW-B
- **Source:** HC69 full-cokernel realization; target-independent global left-coordinate source
  incidence; canonical BM radial weight
- **Statement:** Among all copy-diagonal symplectic Peierls propagators on the global Xi carrier,
  exact unit BM source incidence forces the diagonal Green-jump weight to equal the canonical BM
  radial weight on every source-active (tilted) fibre. Freedom remains exactly on critical-line
  fibres where the physical source vanishes.

## Corpus-led conjecture

For an arbitrary weight field `w : XiZeroCopy -> C`, construct the associated finite-support
diagonal map and symplectic two-channel propagator. Prove its unit source pairing at `q` is exactly

`w(q) * normSq(BMSourceAmplitude(1,q))`.

Since the BM boundary concomitant is already

`canonicalRadialWeight(n,q) * normSq(BMSourceAmplitude(1,q))`,

prove the premise-free classification

`weighted incidence at q <-> q lies on critical line OR w(q)=canonicalRadialWeight(n,q)`.

Globally, prove universal exact incidence iff `w` agrees with the canonical weight on every tilted
fibre. Equivalently, all diagonal Green jumps realizing literal BM incidence are the canonical jump
plus an arbitrary defect supported on critical-line copies.

## Why this is frontier-level

HC69 supplies one fixed full-cokernel realization but does not show physical response uniqueness.
This conjecture solves the inverse source-incidence problem for the largest natural copy-diagonal
class. It converts a vague Green-operator identification burden into a sharp theorem: source-active
Xi fibres force the BM jump coefficient uniquely, and only source-extinct wall fibres are
unobservable.

The result does not derive that physical Einstein--Teukolsky Green operators are copy-diagonal;
that structural PDE statement remains outside this classification. It does rule out any alternative
diagonal response normalization as an off-line escape.

## Hostile checks

- Weight field arbitrary; do not assume nonzero, reflection symmetry, continuity, or boundedness.
- Work on finite-support global packets; prove linearity and skewness from definitions.
- State classification as an unconditional disjunction/iff, not a theorem with an off-line premise.
- Use literal unit BM sources and exact boundary concomitant.
- Identify full global freedom, including unconstrained critical-line weights.
- Keep frontier map read-only.

## Novelty boundary as of 2026-08-28

Lean-corpus search found canonical weighted incidence and fixed-scalar no-go theorems, but no
classification of arbitrary copy-diagonal Peierls Green-jump weights. Bounded primary-source search
covered conserved QNM bilinear forms and projections (arXiv:2210.15935), causal Green functions and
QNM echoes (arXiv:1909.10382), AIME mode projections (arXiv:2112.11168), and the July 2026
higher-order QNM perturbation framework (arXiv:2607.19492). No audited source states this exact BM
Xi-fibre diagonal Peierls incidence rigidity law. Bounded, not exhaustive, priority claim.

## Gates

- [x] 0 -> 1 in-progress: corpus gap, exact conjecture, hostile proof route, bounded literature audit
- [x] 1 -> 2 fully-proven: dependency-closed paper proof
- [x] 2 -> 3 formalized: closed Lean theorem, target build, axiom/lint audit, umbrella wire
- [ ] 3 -> 4 publication-ready: independent priority audit and standalone exposition

## Log

- 2026-08-28 — Opened after HC69 supplied existence and corpus search exposed missing uniqueness.
  Frontier map left unchanged.
- 2026-08-28 — Proved arbitrary-weight packet diagonal and symplectic propagator infrastructure in
  `ThetaCuspHawkingDiagonalPeierlsSourceIncidenceRigidity.lean`. Every such propagator is
  Peierls-skew; its literal BM source pairing is `w(q)` times source norm-square. Exact unit BM
  incidence holds iff the fibre lies on the critical line or `w(q)` is the canonical BM radial
  weight. Universal incidence is equivalent both to tilted-fibre agreement and to the weight defect
  being supported on critical-line copies. The canonical propagator is recovered exactly.
- 2026-08-28 — Verification: direct `lake env lean` passed; target-only
  `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingDiagonalPeierlsSourceIncidenceRigidity`
  passed (`12010/12010`); all twelve exported theorem axiom audits report only `propext`,
  `Classical.choice`, and `Quot.sound`; umbrella import present; formal lint reports no finding in
  this module (only unrelated unreachable modules).
