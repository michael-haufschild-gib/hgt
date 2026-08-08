# Nomological geometry and dynamics Stage-3 formalization

- **Stage:** 1 — in progress
- **Started:** 2026-08-09
- **Scope:** Every paper-proved theorem in every current card under
  `docs/drafts/pipeline/2-fully-proven/nomological-geometry-and-dynamics/`.
- **Completion gate:** Exact Lean statements, unconditional proofs, umbrella imports, per-file
  elaboration, formal lint, targeted final builds, axiom audits, and card moves to Stage 3.

## Card audit

| Card | Exact mapping | Lean status | Final audit |
|---|---|---|---|
| critical Euler/Mass/Weil/Stokes shadow | mapping | pending | pending |
| Dirichlet Maurer--Cartan Mellin orbit | `DirichletMaurerCartanMellinOrbitLaw` covers Dirichlet derivation, Kähler inverse identity/contraction, Mellin automorphism and derivative, both gauge equations, Julia orbit, pure gauge, one-parameter curvature | partial: universal de Rham Maurer--Cartan assembly remains | pending |
| Euler prime-orbit prolongation/recurrence/polar/cofinal | mapping | pending | pending |
| finite law-relation wall synchronization/phase loss | mapping | pending | pending |
| framed two-boundary phase fibre/history separation | mapping | pending | pending |
| half-density Route-L odd Weil connection weld | mapping | pending | pending |
| Hurwitz monodromy closure/resonance rank | mapping | pending | pending |
| marked half-character duality/soldering/cofinal obstruction | mapping | pending | pending |
| multiple-Gamma period-action three-shadow | mapping | pending | pending |
| multiple-Gamma three-face cofinal wall | mapping | pending | pending |
| native observer descent/effectivity/non-determination | mapping | pending | pending |
| odd Euler comb tempered admission wall | mapping | pending | pending |
| perfect defect motive five-shadow | mapping | pending | pending |
| polarized exactness horizon/relative Connes phase | `ParachainConnesComparisonLaw` covers Theorem 4.1 | partial | pending |
| positive observer covariance/HT/compact resolvent | mapping | pending | pending |
| restricted history completion/polynomial saturation | mapping | pending | pending |
| Route-L odd current/Suzuki/Mass reconstruction | mapping | pending | pending |
| source-normal Hochschild/Maurer--Cartan clock curvature | `SourceNormalClockCurvatureLaw` covers core algebraic identities | partial | pending |
| split-prime Euler class/inverse-monodromy no-go | `ParachainConnesComparisonLaw` covers inverse scalar totalization | partial | pending |
| universal Hausdorff observer rank transmutation | mapping | pending | pending |
| weighted history action/infinite completion boundary | mapping | pending | pending |

## Owned new Lean modules

- `formal/GaloisForLFunctions/HTGeometry/ParachainConnesComparisonLaw.lean`
- `formal/GaloisForLFunctions/HTGeometry/DirichletMaurerCartanMellinOrbitLaw.lean`
- `formal/GaloisForLFunctions/RHTower/SourceNormalClockCurvatureLaw.lean`

## Open core

Map every numbered paper theorem to an existing exact declaration or a genuine missing declaration.
No card may move until every proved assertion is represented and the hostile-boundary statements are
preserved as explicit non-implication/counterexample theorems where the card proves them.
