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
| 4 | ht-da-translation-spectrum-countability | **PROMOTED 2026-08-29** | — |
| 5 | ht-exact-da-translation-stabilizer | OPEN | Ostrowski no-finite-basis theorem; tail-gcd; locally cyclic realization |
| 6 | ht-q-residue-spectrum-classification | OPEN | ADH rational-or-HT; Chen–Singer q-discrete residues |
| 7 | hypertranscendental-maximal-finite-horizon-galois-law | OPEN | binomial degree + S_D normal closure transport |
| 8 | indeterminate-moment-fiber-prevalent-translation-ht | OPEN | prevalence, product probe, parametric transversality |
| 9 | laguerre-polya-jensen-profield-blindness | OPEN | LP class, Jensen's theorem, even canonical product, quartet surgery |
| 10 | poincare-constraint-order-recession | OPEN | unit-cost cascade ord_DA(f^[n]) = n; affine invariance; Bergweiler |
| 11 | projective-horizon-hankel-secant-stratification | OPEN | catalecticant/secant identification, codimension 2k-1, Sing(C_k)=C_{k+1} |
| 12 | projective-ht-generic-pv-curvature-core | OPEN | Wilczynski normalization; Picard–Vessiot SL_N; invariant field |
| 13 | random-holomorphic-maximal-translation-ht-law | OPEN | random entire functions, finite-jet absolute continuity, GAF nondegeneracy |

## Shared infrastructure built
- `HTGeometry/DomainJetRelationLocus.lean` — the (n,d) jet-minor certificate for
  `DifferentiallyAlgebraicOn f Ω` on an arbitrary open preconnected `Ω` (generalizes
  `EntireFamilyDifferentialAlgebraicLocus`).  **Reusable by every other card in this folder.**
- `HTGeometry/DomainTranslationSlopeMinor.lean` — normalized translation-defect minors on a domain,
  antiderivative closure `differentiallyAlgebraicOn_of_deriv`, uniform branch.
- `HTGeometry/DifferentialAlgebraicOnSum.lean` — constants, binary and finite sums, scalar
  multiples for `DifferentiallyAlgebraicOn` on a domain.
- `HTGeometry/StencilJetExpansion.lean` — local affine chain rule `iteratedDeriv_comp_affine_on`,
  `iteratedDeriv_iteratedDeriv`, stencil moments, `dslopeIterZero` k-fold removable division.
- `HTGeometry/MeromorphicTranslationDefectCountability.lean` — `not_countable_univ_complex`,
  `nonempty_compl_of_countable`, `infinite_compl_of_countable`,
  `isPreconnected_compl_of_countable` (all reusable).

## Known corpus assets located during the sweep (do not rebuild)
- Hölder's theorem is owned: `HTGeometry.WatsonFlatnessDischarge.quantitativeHolder`,
  `hypertranscendental_reciprocalGammaEntire`, and the whole Gamma-HT stack.
- `Bottcher.analyticOnNhd_zeros_countable` — countable zero set on a preconnected open set.
- `HTGeometry.ConvexDiffCountableConnected.isPreconnected_diff_of_countable_of_convex_complex`.
- `HTGeometry.ReflectedDividedDifference.iterate_dslope_self_eq_iteratedDeriv_div_factorial`
  (namespace `HTGeometry`, not `GaloisForLFunctions.HTGeometry`).
- `HTGeometry.DifferentialAlgebraicOnClosure` — `meroField U` differential-field bridge on an
  arbitrary open preconnected nonempty infinite domain; the letI instance stack to copy.
- `HTGeometry.UpperEndPrimeLogJets.analyticOnNhd_iteratedDeriv` — do not redefine this name.
- **NOT in mathlib and not in the corpus:** Runge's theorem / rational approximation with poles off
  a domain (needed by `da-ht-topological-interlacing-law`); the corpus only owns the half-plane
  one-generator case `HTGeometry.HalfPlaneRungeClosure`.

## Log
- 2026-08-29 — ledger opened; all 13 cards read; corpus survey started.
- 2026-08-29 — card 4 `ht-da-translation-spectrum-countability` fully formalized and promoted to
  stage 3: meromorphic (closed-countable-singular-set) countability, bounded-complexity
  accumulation, complexity escape, multiplicative corollary, and the finite-stencil extension in
  both directions.  Eight new Lean modules, all axiom-clean.
