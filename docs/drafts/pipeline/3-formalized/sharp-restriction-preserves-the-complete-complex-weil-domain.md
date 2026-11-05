# Sharp restriction preserves the complete complex Weil domain

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Restricting any complete aperture form vector to any centered interval gives a vector in that exact interval's complete form domain, without a smoothing collar or positivity assumption.

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

## Lean

`CanonicalSystemOfTheWindowTower/SharpRestrictionPreservesTheCompleteComplexWeilDomain.lean`:

- `exists_ccm_form_of_sharpInterval`: exact complex restriction in the target domain.
- `hasLogarithmicEnergy_sharpInterval`: restricted source has finite logarithmic energy.
- `hasLogarithmicEnergy_sharpComplement`: complementary collar has finite energy.

Plain Lean audit passes. All three declarations use only `propext`,
`Classical.choice`, and `Quot.sound`. The module is wired into its umbrella.
Exact support splitting alone does not prove the Riesz-kernel variation law.
