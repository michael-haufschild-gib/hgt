# Centered intervention, phase reconstruction, Gram response, and support generation -- Lean certification

- **ID:** ULF-GRM-1
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/generative-response-mechanics/centered-intervention-phase-gram-support-generation-law.md`
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
matrix equality, newborn-span rank, leverage conservation, log-determinant differentiation, and
the diagonal simple-null determinant law in one closed declaration.

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
- `generativeTangent_iff_universalNullResponse`;
- `legalCenteredTangent_iff_phaseConservation_and_universalNullResponse`;
- `negativeNullResponse_forces_negative_birth` and `generativeSelection_capstone`;
- `centeredIntervention_fusion_capstone` and `generativeResponse_full_capstone`.

## Formal boundary

The coordinate-free paper theorem for an arbitrary positive corank-one Gram face reduces by the
spectral theorem to the certified diagonal gauge. Lean separately certifies an arbitrary adjugate
rank-one certificate and the full diagonal simple-null formula, but does not yet contain a single
declaration performing that final spectral reduction. No RH selection theorem is claimed.

## Verification

Foreground checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/GenerativeResponseFusion.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

The final umbrella build passes 11,608 jobs. A `/tmp` axiom audit of all load-bearing declarations
and the full capstone reports only `propext`, `Classical.choice`, and `Quot.sound`. The module uses
no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, or computation certificate.

Repository lint reaches this module without a target error. Its global nonzero exit is caused by
six unrelated unwired `RHTower` modules and stale generated `LEAN_API.md`, `LEAN_GAPS.md`, and
`LEAN_OVERVIEW.md` files.
