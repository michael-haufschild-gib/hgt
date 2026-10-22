# Gamma-cell periodic nonreal mobility universality law

Status: source written; exact Lean audit pending.

## Theorem-first origin

- `GammaCellNonrealMobility.gammaFECell_real_zero_free_nonreal_strip_mobility` supplies cell member
  with no real strip zeros and explicit nonreal off-line strip zero.
- `PeriodicityDichotomy` forces every off-line strip zero into full vertical zero progression.
- Existing `DichotomyInstances` used cell-wide dichotomy only on zeta to imply RH; it did not close
  this mobility consequence.

## Universal law

For any carrier class, real-zero-free nonreal mobility plus class-wide periodicity dichotomy implies
periodic real-zero-free nonreal mobility. For `GammaFECell`, cell-wide dichotomy therefore produces
all-prime member with full nonreal off-line vertical zero progression while retaining real-strip
zero-freeness.

## Novelty and verification

Corpus scan found no generic promotion theorem or gamma-cell specialization. External literature
audit and exact Lean audit remain pending.
