# Born dilated graded KMS wall universality law

Status: Lean source written; exact audit pending.

## Lean-source inputs

- `RHTower/BornGradedKMSClassification.lean`: throughout `0 < β ≤ 2`, the parity supertrace converges while the ungraded Gibbs trace diverges.
- `RHTower/BornSuperKMSCovariance.lean`: every positive dilation has exact `k^{-β/2}` supertrace covariance; odd dilations preserve the grading pointwise.
- `RHTower/BornEtaGrading.lean`: the graded supertrace is strictly positive for every `β > 0`.

## Universal law

For every `0 < β ≤ 2` and every positive dilation `k`, the dilated Born supertrace is summable,
strictly positive, and equals `k^{-β/2}` times the original supertrace, while the ungraded trace
still diverges.  Every odd dilation additionally preserves the parity grading pointwise.

## Novelty audit

Pending post-formalization primary-source literature search.  Corpus research found the wall
classification and dilation covariance separately, but no all-dilation phase theorem.

## Verification

- Development command: pending `lake env lean GaloisForLFunctions/RHTower/BornDilatedGradedKMSWallUniversalityLaw.lean`.
- Final module build, axiom audit, and lint: pending exhaustion pass.
