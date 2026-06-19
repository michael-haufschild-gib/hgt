# The one missing uniform bound (the no-margin: obstacle or prize?)

- **ID:** no-margin-uniform-bound
- **Stage:** 0-backlog
- **Type:** OPEN CORE
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/bucket-the-no-margin.md (#89 §8, #70 SEED-Q, #92 §3) · 00-status rows #89, #90
- **Statement:** Find the **one missing uniform bound** — the **Kronecker→Liouville height upgrade** =
  uniform-in-order total positivity = the uniform multiplicity/equidistribution estimate — a uniform
  floor `ĥ(ρ) ≥ c(δ) > 0` that **unblocks all four no-margin coordinates at once** (Arakelov height
  excess / Toeplitz first-violated-minor order→∞ / Weil-certificate `dim_min`→∞ / discrepancy
  resolution→∞). **Or** prove no such bound can exist — confirming the no-margin is **irreducibly
  faithfulness** (A2), not an obstacle.

## Goal
The no-margin (`λ_min → 0` everywhere, with the **two-rate signature** `margin ~ δ`, detection-cost
`~ log(1/δ)`) is the field's central recurring phenomenon, and the program's hinge has **two opposite
readings to resolve**:
- **(a) obstacle:** there is no finite certificate — every test's cost diverges as `δ → 0`, so
  finite/positivity methods provably cannot close RH;
- **(b) prize:** the no-margin **IS** faithfulness / criticality / independence (no spectral gap = the
  secret numbers are independent = DSS/A2; #92's reframe). The knife's-edge is the prize wearing the mask
  of an obstacle.

Deciding (a) vs (b), and finding or refuting the uniform bound, is the open core.

## Door passport
- **Door-3:** the missing bound is a **uniform multiplicity/equidistribution estimate on `G_L`** — the
  same native rigidity feeding both faces (`a1-a2-unification-brick.md`), not a renamed classical floor.
- **Door-2:** the per-coordinate no-margin facts (Thm 6, Thm 7) are proved; the **uniform completion** is
  the native content (finite-order TP is a parent; uniform-in-order is the wall).

## Gates
- [ ] 0 → 1  in-progress: the four coordinates' equivalence (one missing bound) restated; the two-rate
  signature pinned; the (a)-obstacle vs (b)-prize dichotomy posed operationally
- [ ] 1 → 2  fully-proven: the uniform bound proved (= RH-grade) OR proved impossible (= no-margin is
  irreducibly faithfulness)
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Approach
Target the **height that separates** — a uniform floor `ĥ(ρ) ≥ c(δ)` (Kronecker currently gives only
`ĥ(ρ) ≈ δ/A → 0`, vanishing on the whole locus). The no-margin = an **exceptional point** (#96:
eigenvalue + eigenvector coalescence, Nyman–Beurling completeness defect `d_N → 0`); RH = PT-unbroken,
pinned at the threshold — so a uniform floor would contradict the exceptional-point structure, evidence
for (b). Tie to `Λ = 0` (the TP-onset time; Rodgers–Tao `Λ ≥ 0` ⟹ RH ⟺ `Λ = 0`).

## Cross-references
- `a1-a2-unification-brick.md` — the no-margin = faithfulness is the unification's hinge (reading (b)).
- `is-lambda-a-period.md` — the no-margin constant `Λ` itself.
- `realization-problem.md` — same integrality lesson: positivity necessary, never sufficient.

## Log
- 2026-06-19 — created in 0-backlog. The no-margin open core: the one missing uniform bound, and the
  obstacle-vs-prize decision.
