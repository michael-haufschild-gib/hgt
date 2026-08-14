# Centered intervention, phase reconstruction, Gram response, and support generation -- Lean certification

- **ID:** ULF-GRM-1
- **Paper card:**
  `docs/drafts/pipeline/3-formalized/universal-law-field/generative-response-mechanics/centered-intervention-phase-gram-support-generation-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.GenerativeResponseFusion`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-CERTIFIED] [NO PROJECT AXIOMS] [FOUR-ORGAN FUSION] [NOT RH]

## Certified mechanism

Lean certifies one finite mechanism across four structurally different reporter organs:

1. normalization centers every absolute coefficient intervention and conserves total probability;
2. distinct phase labels make the finite moment reporter injective, reconstructing the centered
   tangent;
3. positivity localizes every Gram-null vector pointwise on occupied support, so first response is
   exactly the off-support birth energy;
4. newborn Gram rank equals the span dimension of newborn analysis features, while the same tangent
   gives leverage conservation, log-determinant response, Hankel-null response, and simple-null
   determinant orientation.

The certified selection equivalence identifies the legal generative tangent cone with conservation
of the zeroth phase moment plus nonnegative first response for every positive Gram null observer.
Every negative crossing therefore exposes an absent source atom with negative tangent coefficient.

The unconditional `generativeResponse_full_capstone` packages Hankel generation, support-birth
matrix equality, newborn-span rank, leverage conservation, log-determinant differentiation, the
diagonal law, and the coordinate-free positive corank-one determinant orientation in one closed
declaration.

## Certified declarations

- `centeredIntervention_sum_eq_zero`;
- `interventionMoment_injective`;
- `positiveNullFace_generation` and `hereditary_supportBirthEnergy_eq_zero`;
- `gramResponseMatrix_eq_supportBirthMatrix`;
- `rank_supportBirthMatrix_eq_finrank_span_birthFeatures`;
- `weighted_featureLeverage_sum_eq_finrank`;
- `hasDerivAt_logdet_perturbedNormalizedGramMatrix`;
- `hankelNull_generation`;
- `hasDerivAt_det_perturbedNormalizedGramMatrix_of_adjugate_certificate`;
- `hasDerivAt_det_perturbedNormalizedGramMatrix_diagonal_simple_null`;
- `positivePseudodeterminant` and
  `exists_uniqueZero_adjugate_eq_pseudodeterminant_eigenvector`;
- `adjugate_eq_positivePseudodeterminant_smul_nullVector`;
- `normalizedGramMatrix_posSemidef` and
  `positivePseudodeterminant_normalizedGramMatrix_pos`;
- `hasDerivAt_det_perturbedNormalizedGramMatrix_positive_corank_one`;
- `generativeTangent_iff_universalNullResponse`;
- `legalCenteredTangent_iff_phaseConservation_and_universalNullResponse`;
- `negativeNullResponse_forces_negative_birth` and `generativeSelection_capstone`;
- `centeredIntervention_fusion_capstone` and `generativeResponse_full_capstone`.

## Formal boundary

Lean now performs the full coordinate-free spectral reduction: positive semidefiniteness and rank
`d - 1` force one zero eigenline, all complementary eigenvalues are positive, orthogonal
conjugation transports the diagonal adjugate, and any unit kernel generator yields
`adj(G₀) = det₊(G₀) aaᵀ`. The exact `(GRM.13)` determinant derivative follows with strictly positive
pseudodeterminant coefficient. No RH selection theorem is claimed.

## Verification

Foreground checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/GenerativeResponseFusion.lean
lake build GaloisForLFunctions.HTGeometry.GenerativeResponseFusion
lake env lean GaloisForLFunctions/HTGeometry/UniversalLawField.lean
```

The targeted module build passes 8,665 jobs. A `/tmp` axiom audit of the spectral, adjugate,
pseudodeterminant, coordinate-free derivative declarations and full capstone reports only
`propext`, `Classical.choice`, and `Quot.sound`. The module uses no `sorry`, `admit`, custom
`axiom`, `opaque`, `unsafe`, or computation certificate.

Repository lint reaches this module without a target error. Its global nonzero exit is caused by
six unrelated unwired `RHTower` modules and stale generated `LEAN_API.md`, `LEAN_GAPS.md`, and
`LEAN_OVERVIEW.md` files.
