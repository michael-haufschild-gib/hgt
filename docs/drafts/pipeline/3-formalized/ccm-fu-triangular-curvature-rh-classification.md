# CCM–FU triangular-curvature RH classification

- **ID:** CCM-FU-TRI-RH
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` routes CCM-FU/CFI/SP-E
- **Statement:** `CCMFUSuzukiTriangularCurvatureTransformBound ↔ RiemannHypothesis`.

## Goal

Kill signed third-grade triangular high-pass as an independent RH producer. Exact chain:
`RH → bounded Suzuki zero series → bounded positive FU mixture → bounded affine mixture → bounded
triangular curvature transform → RH`.

## Gates

- [x] 0 → 1 in-progress: exact source, attack, route consequence, preliminary novelty audit
- [x] 1 → 2 fully-proven: dependency-closed paper proof
- [x] 2 → 3 formalized: Lean capstone, targeted build, axiom audit
- [ ] 3 → 4 publication-ready

## Approach

Under RH, corpus identifies `suzukiPsi` with a nonnegative screw series having summable
reciprocal-square Xi-zero weights, hence a uniform hull bound. Positivity of rectangular-mixture
density and its exact uniformly bounded total mass bound the FU mixture. Existing exact reductions
remove bounded intra-cell curvature, base-affine, and reset channels, leaving precisely the signed
triangular transform. Reverse implication is already formalized.

## Hostile audit

- Corpus: no reverse theorem found; weighted-first-moment shortcut is false under RH and excluded.
- Literature through 2026-08: Suzuki proves boundedness of full screw source iff RH, but exact
  checkpoint/third-grade triangular-curvature classification was not found.
- Verdict: no collision found; classification proved in Lean.

## Log

- 2026-09-01 — proved as
  `RHTower.ccmFUSuzukiTriangularCurvatureTransformBound_iff_riemannHypothesis` in
  `SuzukiTriangularCurvatureRHClassification.lean`; targeted build green; axioms only
  `propext`, `Classical.choice`, `Quot.sound`.
