# Infinite-grid tail rigidity beyond Trap 5

- **ID:** infinite-grid-tail-rigidity-2026-10-17
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Scope:** Independent BiScaleUncertainty research; no RH objective.
- **Goal:** 100 significant contributions in this research topic, counted by mathematical packages, not helper lemmas.
- **Ledger:** `docs/reports/BiScaleUncertainty/InfiniteGridTailRigidity-FACTS.md`
- **Field guide:** `formal/GaloisForLFunctions/BiScaleUncertainty/README.md` (read-only).
  Keep general signed correlation statements primary; use all-grid constructions as
  sharpness witnesses. Research topic remains infinite-grid tail rigidity beyond Trap 5.

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

Eleven significant packages certified:

1. Canonical tail detection and the uniform linear energy barrier for separated two-copy sources,
   including the stronger local-energy inequality (22 theorems).
   Card: `../3-formalized/infinite-grid-two-copy-energy-barrier-2026-10-17.md`.
2. Actual smooth compact polar sources satisfying every infinite-grid zero at arbitrarily large
   logarithmic midpoints, with `exp(-1/2)T/4 <= E <= C+T` (17 theorems).
   Card: `../3-formalized/infinite-grid-polar-recovery-family-2026-10-17.md`.
3. Exact center classification for separated polar copies: existence precisely off-grid,
   and matching-order logarithmic cost in reciprocal nearest-grid distance (15 theorems).
   Card: `../3-formalized/infinite-grid-distance-classification-2026-10-17.md`.
4. Finite common-seed train rigidity: the unique extremal pair forces nearest-grid energy cost
   and a lower bound proportional to full span despite interior cancellations (15 theorems).
   Card: `../3-formalized/infinite-grid-finite-copy-trains-2026-10-17.md`.
5. Complete active-lag criterion for finite common-seed trains: actual smooth all-grid sources
   exist exactly when every active positive center is off-grid; polar inheritance and energy
   cost at every active lag are certified (12 public theorems).
   Card: `../3-formalized/infinite-grid-active-lag-classification-2026-10-17.md`.
6. Uniform matching-order energy law in the smallest active grid distance, with one upper
   constant independent of packet count, coefficients, and spacing; actual smooth sources
   and polar inheritance included (14 theorems).
   Card: `../3-formalized/infinite-grid-uniform-train-cost-2026-10-17.md`.
7. Shape-independent logarithmic continuity and two-sided infinite-grid tail decay, with
   uniform bounded-energy family quantifiers and window energy decaying as `1/log N`
   (10 public theorems).
   Card: `../3-formalized/infinite-grid-uniform-tail-2026-10-17.md`.
8. Compact closure of bounded-energy normalized all-grid correlations in the global supremum
   norm; uniform subsequence limits retain every finite Gram inequality, grid zero, and
   the energy ceiling, with actual integrability of the limiting singular density
   (17 public theorems).
   Card: `../3-formalized/infinite-grid-correlation-compactness-2026-10-17.md`.
9. Exact energy continuity criterion for uniformly convergent all-grid correlations:
   uniform smallness of origin energy is necessary and sufficient. Every bounded-energy
   source sequence admits a subsequence whose entire energy defect is localized at zero;
   every positive-cutoff energy tail converges (17 theorems).
   Card: `../3-formalized/infinite-grid-origin-energy-2026-10-17.md`.
10. Actual smooth sources with one common short support converge in squared L² distance
    and uniformly in normalized correlation while retaining a fixed positive energy gap.
    General signed-source statement and constructed all-grid witnesses; a subsequence
    realizes strictly positive origin concentration (12 theorems).
    Card: `../3-formalized/infinite-grid-strict-energy-loss-2026-10-17.md`.
11. Exact criterion for bounded-energy correlation compactness: uniform decay of
    general signed logarithmic traces iff uniform continuum tails iff compact closure
    in the global supremum norm. Includes global uniform subsequence extraction
    without grid blindness or a common support bound (17 public theorems).
    Card: `../3-formalized/signed-grid-trace-compactness-2026-10-17.md`.

The 100-package objective remains active. Next: classify distant-copy compactness
and polar continuity by their exact amplitude scales. This preserves the original
tail-rigidity topic and retains general signed samples. Candidate:
`../0-backlog/distant-copy-topology-classification-2026-10-17.md`.
Mixed-energy decoupling and true polar-tail control remain separate open refinements.

## Constraints

No numerical experiments, new axioms, heartbeat changes, full builds, commits, or edits to other
agents' research. One owned foreground Lean process at a time. `update_plan` is unavailable in
this session; this card carries the plan. The attachment explicitly excludes hgtl7.
