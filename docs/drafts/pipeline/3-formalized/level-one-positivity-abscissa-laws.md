# Level-one positivity gives the abscissa laws

- **ID:** A107
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Dressed positivity at level one for all sufficiently large prime moduli
  implies AAL, the strict-half-plane implication to RH, and `RH ∨ Θ=1`; indeed `Θ=1/2`.

## Proof

The diagonal Bochner bound gives RH from level-one positivity, by
`RHTower.riemannHypothesis_iff_exists_jasDressedPSDAbove_one`.
RH gives AAL and `Θ=1/2`; the requested implication and disjunction follow.
Thus no edge exception is needed under this positivity premise.

## Lean

`GaloisForLFunctions.SelectiveArithmetic.levelOne_abscissa_laws` in
`SelectiveArithmetic/LevelOnePositivityAndTheAbscissaLaws.lean`.
Direct `lake --old env lean` check passed; transitive axioms:
`propext`, `Classical.choice`, `Quot.sound`. Imported by `SelectiveArithmetic.lean`.
