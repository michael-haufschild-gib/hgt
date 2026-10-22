# Xi deck-charge unit-gauge classifier universality law

## Status

Law 250; paper proof and exact Lean module audit passed. Literature novelty audit pending.

## Corpus sources

- `RHTower/XiDeckCharge.lean`
- `RHTower/DeckChargeInvariant.lean`

## Theorem-first derivation

Xi charge-tower triviality at all hypothetical right-half Xi zeros is equivalent to RH. General
deck-charge theory separately proves invariance under every locally analytic nonvanishing factor
and gives a hypertranscendental/DA pair with identical charge towers. These statements meet on
`deckCharge (xi * u)` for arbitrary analytic units `u`.

## Universal law

For every analytic nowhere-zero unit on the right half-plane, RH is equivalent to triviality of
the full charge tower at every right-half zero of the unit-twisted Xi carrier. Thus the RH
classifier is invariant under the complete analytic-unit gauge. Nevertheless the same invariant
cannot classify differential-algebraic type: any supplied nowhere-zero hypertranscendental carrier
has exactly the constant-one charge tower.

## Paper proof

1. At each right-half point, apply `deckCharge_mul_unit` to identify the charge of `xi * u` with
   the charge of `xi`.
2. Since `u` is nowhere zero, zeros of `xi * u` and zeros of `xi` coincide.
3. Rewrite `xiDeckCharge` as the general `deckCharge xi` and apply `rh_iff_xiDeckCharge` in both
   directions.
4. Apply `deckCharge_blind_to_class` to the nowhere-zero hypertranscendental witness.

No numerical pre-certification applies: proof is local divisor invariance and logical equivalence.

## Lean target

- Module: `GaloisForLFunctions.RHTower.XiDeckChargeUnitGaugeClassifierUniversalityLaw`
- Capstone: `RHTower.xiDeckCharge_unitGaugeRHClassifier_and_classBlindness`
- Exact check: `lake env lean GaloisForLFunctions/RHTower/XiDeckChargeUnitGaugeClassifierUniversalityLaw.lean`

## Novelty

Pending primary-source literature search after corpus discovery reaches exhaustion.
