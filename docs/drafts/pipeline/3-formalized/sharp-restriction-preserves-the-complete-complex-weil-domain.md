# Sharp restriction preserves the complete complex Weil domain

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Every literal enclosed interval cut of a complete complex Weil source lies in the enclosing complete form domain. The old interval and two sharp collars give an exact three-piece decomposition.

## Proof

Decompose the physical complex source into two real arithmetic graph sources.
Apply `sharpIntervalGraph` to each. Its proved exact support admission gives
two graph vectors in the target aperture. Transfer them through
`apertureGraphWeilEquiv` and recombine with coefficients `1` and `i`.
The source identities identify the result with literal sharp restriction;
the choice of open or closed right endpoint is null for Lebesgue measure.

The bounded Gamma crossing operator supplies sharp graph admission. No
unproved boundary regularity is used. The logarithmic/Weil domain identity
then transfers the conclusion to the literal logarithmic Fourier energy.
The complementary collar is the difference from the original vector.
Arbitrary `Ico` cuts satisfy the same support argument. Partitioning the
larger interval into its old interval and two collars, then using injectivity
of the physical embedding, gives the exact complete-domain decomposition.

## Lean

`CanonicalSystemOfTheWindowTower/SharpRestrictionPreservesTheCompleteComplexWeilDomain.lean`:

- `exists_ccm_form_of_sharpInterval`: exact complex restriction in the target domain.
- `hasLogarithmicEnergy_sharpInterval`: restricted source has finite logarithmic energy.
- `hasLogarithmicEnergy_sharpComplement`: complementary collar has finite energy.
- `exists_ccm_form_of_intervalRestriction`: every enclosed interval cut belongs to the complete domain.
- `hasLogarithmicEnergy_intervalRestriction`: arbitrary enclosed cuts retain finite logarithmic energy.
- `exists_ccm_interval_decomposition`: exact old interval and two-collar decomposition.

Plain Lean audit passes without warnings. All six printed declarations use only `propext`,
`Classical.choice`, and `Quot.sound`. The module is wired into its umbrella.
Exact support splitting alone does not prove the Riesz-kernel variation law.
