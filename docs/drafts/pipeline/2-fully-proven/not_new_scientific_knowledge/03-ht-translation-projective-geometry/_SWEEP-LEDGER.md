# Stage-3 sweep ledger — 03-ht-translation-projective-geometry

Goal: formalize every proven theorem of each card unconditionally in Lean 4, then promote the
card to `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/03-ht-translation-projective-geometry/`.

Already promoted (before this sweep): `ht-remote-quartet-compact-open-field-invisibility`,
`hypertranscendental-caustic-divisor-pole-cone`, `jetwise-dense-single-ht-profield-class`.

| # | Card | State | Blocking mathematics |
|---|---|---|---|
| 1 | combination-mode-reducibility-baker-bridge | OPEN | Baker–Wüstholz effective bound; Dirichlet pigeonhole no-go; Hankel support-≤d lemma |
| 2 | da-ht-topological-interlacing-law | OPEN | O(Ω) Fréchet/Baire; DA locus closed+empty interior; Runge density; H²(D) density (Hölder owned) |
| 3 | ht-c28-minimal-handle-collapse | OPEN | per-handle collapse citations (Weierstrass addition, holonomic, integration closure, vdPS, Hardouin–Singer) |
| 4 | ht-da-translation-spectrum-countability | OPEN | meromorphic case + finite-stencil case (entire case already Lean-owned) |
| 5 | ht-exact-da-translation-stabilizer | OPEN | Ostrowski no-finite-basis theorem; tail-gcd; locally cyclic realization |
| 6 | ht-q-residue-spectrum-classification | OPEN | ADH rational-or-HT; Chen–Singer q-discrete residues |
| 7 | hypertranscendental-maximal-finite-horizon-galois-law | OPEN | binomial degree + S_D normal closure transport |
| 8 | indeterminate-moment-fiber-prevalent-translation-ht | OPEN | prevalence, product probe, parametric transversality |
| 9 | laguerre-polya-jensen-profield-blindness | OPEN | LP class, Jensen's theorem, even canonical product, quartet surgery |
| 10 | poincare-constraint-order-recession | OPEN | unit-cost cascade ord_DA(f^[n]) = n; affine invariance; Bergweiler |
| 11 | projective-horizon-hankel-secant-stratification | OPEN | catalecticant/secant identification, codimension 2k-1, Sing(C_k)=C_{k+1} |
| 12 | projective-ht-generic-pv-curvature-core | OPEN | Wilczynski normalization; Picard–Vessiot SL_N; invariant field |
| 13 | random-holomorphic-maximal-translation-ht-law | OPEN | random entire functions, finite-jet absolute continuity, GAF nondegeneracy |

## Shared infrastructure planned
- `HTGeometry/DomainJetRelationLocus.lean` — the (n,d) jet-minor certificate for
  `DifferentiallyAlgebraicOn f Ω` on an arbitrary open preconnected `Ω` (generalizes
  `EntireFamilyDifferentialAlgebraicLocus`).

## Log
- 2026-08-29 — ledger opened; all 13 cards read; corpus survey started.
