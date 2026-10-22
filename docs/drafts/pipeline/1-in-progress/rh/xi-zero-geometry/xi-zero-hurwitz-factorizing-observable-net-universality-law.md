# Xi-zero Hurwitz factorizing observable-net universality law

## Status

Fully proven on paper; Lean 4 formalization in progress.

## Theorem-first source

- `xiZeroHurwitz_familyObservableField_le_iff`: observable-field inclusion reconstructs the full
  coordinatewise jet-resolution order.
- `xiZeroHurwitz_familyObservableField_eq_iff`: field equality reconstructs the full resolution
  vector.
- `xiZeroHurwitz_disjoint_familyObservableFields_linearDisjoint`: disjoint resolution supports
  generate linearly disjoint fields.
- `xiZeroHurwitz_disjoint_familyObservableFields_inf_eq_bot`: those fields intersect exactly in the
  rational-function coefficient field.
- `xiZeroHurwitz_disjoint_familyObservableFields_tensor_isDomain`: their tensor product has no zero
  divisors.

All five consume the same finite injective Xi-divisor-labelled Hurwitz family and the same
resolution-to-observable-field map.  Corpus research finds no theorem packaging both its order
faithfulness and its support factorization.

## Universal law

For every finite injective Xi-zero-labelled Hurwitz family, the map from jet-resolution vectors to
differential observable fields is a factorizing order embedding.  It reflects and preserves the
complete resolution order and equality.  Pointwise disjoint supports map to linearly disjoint
fields whose meet is the coefficient field and whose relative tensor product is a domain.

## Paper proof

Apply the two observable-net iff theorems to arbitrary resolution vectors.  For arbitrary vectors
with pointwise disjoint support, apply the three factorization theorems.  All statements use the
same upper-end meromorphic differential-field instances, so their conjunction is literal rather
than an identification across models.

No numerical computation is used; proof is symbolic because task forbids computations.

## Lean formalization

Planned module:
`GaloisForLFunctions.RHTower.XiZeroHurwitzFactorizingObservableNetUniversalityLaw`.

## Novelty audit

Pending literature audit after exact Lean formalization. Corpus audit is negative.
