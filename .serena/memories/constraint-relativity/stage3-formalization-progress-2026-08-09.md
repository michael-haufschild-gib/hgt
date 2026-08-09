# constraint-relativity → stage 3 formalization progress (2026-08-09)

Goal: unconditionally formalize every proven theorem in
`docs/drafts/pipeline/2-fully-proven/constraint-relativity` (49 cards at start), wire into
`GaloisForLFunctions.HTGeometry`, issue `<id>-formalized.md` companions, `git mv` each card to
`docs/drafts/pipeline/3-formalized/constraint-relativity/`.

## New Lean area

`formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/` — namespace
`HTGeometry.ConstraintRelativity`. Imports appended at the END of
`formal/GaloisForLFunctions/HTGeometry.lean`. `lake build GaloisForLFunctions.HTGeometry` green
after every batch (~60 s incremental).

## DONE — 16 cards in stage 3, all green, axioms clean

| card | module |
|---|---|
| faithful-reencoding-no-law-promotion | `CloneReencoding` |
| dynamic-question-relation-balance-law | `QuestionRelationBalance` |
| source-word-filtration-and-selection-no-go | `WordFiltrationSelection` |
| fixed-transformation-defect-closure-no-promotion | `DefectClosure` |
| source-norm-support-forgetful-tower-law | `ForgetfulTower` |
| dual-number-static-observer-deformation-erasure-law | `DualNumberErasure` |
| cofinal-observer-conservativity-law | `CofinalConservativity` |
| rank-one-source-naturality-rigidity-and-framing-law | `RankOneFraming` |
| initial-execution-symmetry-inheritance-and-anomaly-necessity | `SymmetryInheritance` |
| prime-infinity-port-capacity-and-root-conormal-law | `PortCapacity` |
| quadratic-law-discriminant-bockstein-controlled-horizon | `QuadraticLawHorizon` |
| monogenic-law-discriminant-observer-shadow-theorem | `MonogenicShadow` |
| radial-affine-torsor-and-cross-prime-flatness-no-go | `RadialAffineTorsor` |
| framed-provenance-curvature-scalar-no-go | `ProvenanceCurvature` |
| heterogeneous-triangle-singular-holonomy-law | `TriangleHolonomy` |
| (infrastructure, no card) | `MonogenicKaehler` |

## Reusable infrastructure built here (NOT in mathlib, NOT previously in corpus)

- `MonogenicKaehler`: `Ω[R[X]/(f) ⁄ R] ≅ R[X]/(f) ⧸ (f'(α))` (`kaehlerEquivMonogenic`),
  `annihilator_kaehler`. Canonical derivation `g(α) ↦ g'(α)` + universal property. Needed by the
  remaining Kähler cards (congruence-order-trace-kahler…, gorenstein-trace-kahler…,
  phase-subdiscriminant-kahler…, prime-radial-excess…).
- `QuestionRelationBalance`: reusable `map_mkQ_inf`, `mapMkQEquivQuotient`,
  `finrank_map_add_finrank_inf_ker`.
- `RankOneFraming`: `quadPoly/quadAlgebra/quadDiscr` + split/dual classification.
- `MonogenicShadow`: conormal presentation, Vandermonde observer, discriminant shadows.

## CORPUS ASSETS FOUND (reuse, do not rebuild)

- `HTGeometry/DifferentialTranscendenceDegree.lean` — `differentialTranscendenceDegree` = cardinal
  matroid rank; `HTGeometry/DifferentialSubfieldTransfer.lean`
  (`differentialTranscendenceDegree_differentialAdjoin_eq`, `adjoinLift`);
  `HTGeometry/DifferentialMatroid.lean` (`differentialMatroid`, `differentialMatroid_ground`,
  `differentialMatroid_indep_iff`, `differentialMatroid_mem_closure_iff_of_indep`,
  `differentialAlgebraicOver_trans_finite_nonempty`).
- `HTGeometry/NormalCrossingCriticalDerivedPhase.lean` — `NormalCrossingKoszulGradeInput`.
- `HTGeometry/DiscriminantPolynomial.lean`, `GenericPolynomialSeparable.lean` — GENERIC-polynomial
  Vandermonde/discriminant only.
- `HTGeometry/UniversalDeRham.lean` — universal exterior derivative.
- mathlib: `Algebra.discr_powerBasis_eq_norm K pb`, `Matrix.det_vandermonde(_ne_zero_iff)`,
  `KaehlerDifferential.polynomialEquiv`, `Derivation.map_aeval`,
  `Matroid.Spanning.cRank_le_cardinalMk`, `exists_nhds_zero_half`, `Real.sin_bound`.

## Lean traps hit (do not rediscover)

- `HasQuotient ↥P (Submodule k ↥P)` FAILS when the ambient is `A ⊗[k] ↥V` (AddCommMonoid/
  AddCommGroup diamond). Use `Submodule.map R.mkQ P` in the ambient quotient.
- `Matrix.fromColumns` absent; `Matrix.inv_smul` takes the matrix first.
- `Polynomial.modByMonic_add_div (p q)` has NO monic hypothesis; `dvd_modByMonic_sub p q`.
- `Ordinal.limitRecOn` cases `zero | add_one | limit`; `Ordinal.pos_iff_ne_zero` gone;
  `le_or_lt` gone → `lt_or_ge`; `Real.exp_eq_one_iff` takes x explicitly;
  `Fin.card_filter_le` absent → `Finset.Ici` + `Fin.card_Ici`.
- `SMulCommClass k A M` derivable from `Algebra k A` + `IsScalarTower k A M`.
- The lint gate treats Lean warnings as errors — clear unused-simp-arg / simpa→simp / unused
  section-variable warnings (`omit [...] in`).
- Two modules `HTGeometry.ConstraintFrameRelativity.*` are unreachable from the umbrella — that is
  ANOTHER session's in-flight work on `constraint-frame-relativity`; do not touch.

## REMAINING (34 cards)

Next planned: `cofinal-ht-to-recurrence-rank-transfer-bound` — needs
`Matroid.Spanning.cRank_le_cardinalMk` plus a proof that `Set.range y` is spanning in
`differentialMatroid F E`; route: take a matroid basis `I` of `range y`, use
`differentialMatroid_mem_closure_iff_of_indep`, then `differentialAlgebraicOver_trans_finite_nonempty`
with base field `differentialAdjoin F I` (instance juggling: `derivationClosedDifferential`).

Then: `simple-horizon-rank-to-depth-transmutation-law` (Koszul + Smith over a DVR + Vandermonde),
`observer-ramification-horizon-exponent-no-go` (mathlib's `Real.sin_bound` gives 4/100·|x|^5, the
card's 19/120 needs the alternating-series bound — build it),
`neutral-fusion-unobstructed-relative-cotangent-law` (`Algebra.FormallySmooth`/`H1Cotangent` for a
localized polynomial algebra), and 30 more.
