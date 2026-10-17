# Infinite-grid tail rigidity beyond Trap 5

- **ID:** infinite-grid-tail-rigidity-2026-10-17
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Scope:** Independent BiScaleUncertainty research; no RH objective.
- **Goal:** 100 significant contributions in this research topic, counted by mathematical packages, not helper lemmas.
- **Ledger:** `docs/reports/BiScaleUncertainty/InfiniteGridTailRigidity-FACTS.md`

## First conjecture

For every fixed nonzero compact continuous real source, sufficiently distant polar copies
fail the infinite logarithmic zero grid. A canonical detecting node is
`n(T) = ceil(exp T)`, within `exp(-T)` of the copy center. Conversely, an admissible
family of separated copies must have a full translation-energy defect at that shrinking scale.

## Plan

1. Inspect current corpus and external parent inequalities; distinguish new application from known tools.
2. Prove exact tail sample identity, quantitative node geometry, and fixed-source obstruction on paper.
3. Formalize exact statements, deriving compactness and continuity bounds from source type.
4. Audit leaf with `lake --old env lean`, scratch axiom check, umbrella wiring, formal lint.
5. Pursue the remaining open core: energy-controlled variable sources, multiple-copy interference,
   and polar tail tightness. Continue conjecture/proof/failure cycles toward 100 packages.

## Gates

- [x] Well-posed, source-pure first conjecture; finite-grid parent theorem inspected.
- [x] Dependency-closed paper proof and novelty boundary recorded.
- [x] Exact Lean endpoints compiled and axiom-audited (22 theorems, standard logical axioms only).
- [ ] Energy-controlled families and general polar tails resolved.
- [ ] 100 significant contributions independently supported.

## Stronger paper theorem

The exact tail sample forces a zero at displacement `delta<=exp(-T)`. Weighted integration
of the chord inequality proves `(R-h(delta)) integral_delta^b w <= 4 J(f)`.
For `T>D+1`, local-copy preservation gives this same short zero for the copy itself.
Thus both base and copy satisfy `J/h(0)>=exp(-1/2)T/4` whenever the tail sample vanishes.
This is uniform over changing sources and nonzero coefficients. Complete proofs are in
`docs/reports/BiScaleUncertainty/InfiniteGridTailRigidity.md` (Theorems 1–5).

## Certified frontier

Three significant packages certified:

1. Canonical tail detection and the uniform linear energy barrier for separated two-copy sources,
   including the stronger local-energy inequality (22 theorems).
   Card: `../3-formalized/infinite-grid-two-copy-energy-barrier-2026-10-17.md`.
2. Actual smooth compact polar sources satisfying every infinite-grid zero at arbitrarily large
   logarithmic midpoints, with `exp(-1/2)T/4 <= E <= C+T` (17 theorems).
   Card: `../3-formalized/infinite-grid-polar-recovery-family-2026-10-17.md`.
3. Exact center classification for separated polar copies: existence precisely off-grid,
   and matching-order logarithmic cost in reciprocal nearest-grid distance (15 theorems).
   Card: `../3-formalized/infinite-grid-distance-classification-2026-10-17.md`.

The 100-package objective remains active. Next: extremal-pair detection in finite common-seed
copy trains, then multiple-copy interference and independently varying packet shapes.

## Constraints

No numerical experiments, new axioms, heartbeat changes, full builds, commits, or edits to other
agents' research. One owned foreground Lean process at a time. `update_plan` is unavailable in
this session; this card carries the plan. The attachment explicitly excludes hgtl7.
