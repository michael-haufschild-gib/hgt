# Finite Weil first-coordinate information

Status: formalized and verified, 2026-10-12. Increment complete; corpus research continues.

## Claim

For every finite `r,k` and any two real quadratic tilt triples, first-coordinate
projection preserves both directed KL divergences and Bhattacharyya affinity.
Equivalently, these quantities equal those of the scalar polynomial tilts from
`WeilLogShiftPolynomialMarginalTilt`. No subcriticality or depth schedule is needed.

## Local Lean evidence and duplication check

- `WeilLogShiftPolynomialGraphRecovery`: one polynomial graph reconstructs every
  tilt at fixed `r,k` from its first marginal.
- `ConstitutiveTimeReversalLikelihoodCocycle`: KL invariance under measurable
  embeddings already exists; reuse it.
- `HellingerAffinityFactorization`: affinity is the integral of the geometric
  mean of the two Radon--Nikodym derivatives against their sum.
- Local lexical searches for `first marginal klDiv` in `WeilLogShift` and
  `bhattacharyya embedding` in `HTGeometry` returned no declarations. Exhaustive
  source searches found no matching embedding-affinity or first-marginal
  information theorem. This is a local corpus check, not an external novelty claim.

## Closed paper proof

Write `G(x)=(x,P(x))` for the existing polynomial graph and `p(z)=z(0)`.
Continuity and injectivity make `G` a measurable embedding. For any two finite
scalar measures `u,v`, the existing KL embedding theorem gives
`KL(G_*u,G_*v)=KL(u,v)`.

For affinity, `(G_*u)+(G_*v)=G_*(u+v)`. The two Radon--Nikodym derivatives,
composed with `G`, equal those of `u,v` against `u+v`, almost everywhere with
respect to `u+v`, by `MeasurableEmbedding.rnDeriv_map`. Change variables in the
nonnegative integral. This proves affinity invariance without absolute
continuity between `u` and `v`.

For actual finite tilted laws `M,N`, existing reconstruction proves
`G_*p_*M=M` and `G_*p_*N=N`. Substitute these identities in both embedding
invariance theorems. Reverse the law pair for the second directed KL equality.
The existing first-marginal polynomial-tilt identity then gives scalar-potential
formulas. All finiteness and measurability requirements are discharged by the
concrete probability laws and polynomial graph.

## Lean files

- `HTGeometry/HellingerAffinityEmbedding.lean`: generic embedding invariance.
- `RHTower/WeilLogShiftFirstMarginalInformation.lean`: actual finite-law roots.
- `RHTower/WeilLogShiftScalarTiltInformation.lean`: scalar polynomial-tilt formulas.

## Verification

- Three native leaf builds passed with empty logs and fresh `.olean` files.
- Seven new theorems; root audit passed all seven `#print axioms` checks with
  only `propext`, `Classical.choice`, and `Quot.sound`.
- Eight API checks and the concrete graph-embedding example passed in the same
  final native scratch audit.
- All six direct imports exist and have fresh objects; both umbrellas are wired.
- Source whitespace and umbrella `git diff --check` passed.
- `scripts/formal_tools.py lint`: passed, 367 existing size warnings, no errors.
- Artifacts: `/tmp/hgt-projection-information-final-audit.lean` and `.log`,
  `/tmp/hgt-projection-information-lint.log`, and the three native leaf logs.

## Exact gain

The existing graph reconstruction now yields numerical information identities,
not only equality detection: first-coordinate projection preserves each directed
KL value and the full Bhattacharyya affinity. Both equal the corresponding
quantities for explicitly defined scalar polynomial tilts. These roots hold at
every finite `r,k` and for all six real tilt coefficients, with no helper premise.

## Next local question

The exact power-covariance rank theorem gives only zero versus positive
determinant. Investigate an exact determinant formula at maximal degree using
finite atom weights and the existing Vandermonde machinery. No claim yet.
