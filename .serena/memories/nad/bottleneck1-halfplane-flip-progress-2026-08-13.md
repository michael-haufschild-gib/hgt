# Bottleneck 1 half-plane flip — in-flight state (2026-08-13)

Executing the node-side half-plane flip (nodes lower, Weyl poles upper) per the plan appended to
`docs/drafts/pipeline/2-fully-proven/nad/_FORMALIZATION-LEDGER.md` ("Bottleneck 1 sign repair —
decision taken and execution plan").  Transport alternatives were checked and fail structurally
(real-symmetric entries ⇒ conjugation is identity; leaf negation flips twice; i-rescaling breaks
real ties).  Upper/upper is uninhabitable for EVERY genuine Nevanlinna family (Herglotz forces the
pole below), so in-place flip replaces a vacuous chain.

## Done (compiled)
- `MinimalTypeProjectiveSeparation.lean`: + `exists_lower_ne_zero_of_differentiable_ne_zero`.
- `CompactNoncriticalProjectiveSeparationAtlas.lean`: + `injectiveShiftConfigurations_covered_by_lower_noncriticalProjectiveGoodRows`.
- `PolynomialRelationDetector.lean`: + `finite_complex_family_has_imaginary_upper_bound`.
- `CompactNoncriticalProjectiveRowPacketAtlas.lean`: full rename UpperGood→LowerGood, clauses
  flipped to `(z + shift i).im < 0`, `…Rows_infinite` mirrored (min(-Hshift) B, bddBelow).

## Done (edited, compile pending — background build b3fud5ysm)
- `PacketPlacementAvoidance.lean`: + `exists_translation_avoiding_finite_below`,
  `exists_translation_lower_and_avoiding`, `exists_placed_lower_packet_all_rows_nondegenerate`.
- `PatternRelationConfinement.lean`: node clauses flipped, detector switched to lower,
  `ne_of_gt`→`ne_of_lt`.
- `AnalyticNevanlinnaCarrierBridge.lean`: structure fields `finite_cauchy`/`infinity_cauchy` at
  `z.im ≠ 0`; `integrable_cauchyKernel_(pow_)of_im_pos` → `_of_im_ne_zero`; all eval-node lemmas at
  `z.im ≠ 0`; packet-value theorem nodes `< 0` with `hz.ne`; `_at_I` left as-is (no consumers;
  needs −I treatment when consumed).
- `AnalyticNevanlinnaCarrierConstruction.lean`: fields now proved via `hz` directly (hz : im ≠ 0).
- `CauchyTransformHalfPlane.lean`: passes `hz.ne'` to the two structure fields.
- sed flip `∀ z, 0 < z.im → 0 <` → `∀ z, z.im < 0 → 0 <` in: bridge, RelationFree,
  BoundaryCarrierTranslationFreeness, CarrierHerglotzPresentationFree,
  NevanlinnaBoundaryFaceMaximalTranslation (the `upperMap` FIELD is now lower→upper),
  NevanlinnaNoncriticalProjectiveCompactPatch (+ chart renames), both HTGeometry
  SingularContinuous laws, both RHTower SingularContinuous laws.
- Shared prop defs flipped: `weightedBoundaryCarrierExpandedPatternRelationHolds`,
  `probabilityCarrierExpandedPatternRelationHolds`, `probabilityCarrierExpandedFullRankWitness`
  (packet clause `.im < 0`).
- NEW `NevanlinnaEntryConjugation.lean` (not yet compiled): `secondKindC_conj`, `nevBinf_conj`,
  `nevDinf_conj`, `nevInf_quotient_im_pos_of_im_neg`,
  **`analyticNevCarrierFamily_lowerMap`** — the corrected upperMap field witness for the
  constructed family.  (`monicOrthoC_conj` already existed in `ComplexChristoffelDarboux`.)
  NOT yet wired into umbrella.

## Not yet done
- Compile fallout fixes in: NevanlinnaNoncriticalProjectiveCompactPatch internals,
  RelationFree internals, TranslationFreeness/HerglotzPresentationFree internals, JetTriangular
  modules, ConstrainedCauchyJetControllability, NevanlinnaTranslatedExpandedEvaluationCompactPatch,
  NevanlinnaExpandedEvaluationCompactPatch, Projective(Normalized)CauchyDensityControl,
  ProjectiveNevanlinnaGenericity/PolynomialEscape, CompactNevanlinnaUniformProbe.
- Parallel chains not flipped yet (their own upper defs + atlases): `cauchyUpperGood…`
  (CompactCauchyRowPacketAtlas), `evenCanonicalUpperGood…`, `movingCanonical…`, `herglotz…`,
  `MovingEvenCanonical…` — flip in a later pass before instantiating their capstones.
- Remaining MaximalTranslationInputs fields after the flip: `minimalExponentialType` (M. Riesz —
  needs Hadamard/Weierstrass factorization, NOT in mathlib), `phase_isGδ`, leaf/label covariance.
- Wire NevanlinnaEntryConjugation into umbrella; axiom audit; ledger update.

## Concurrency note
Other Claude sessions build RHTower/Triptic/NomologicalHomotopy modules concurrently — their lake
processes are not ours; do not kill.  Re-read HTGeometry.lean before umbrella edits.
