# Split-star formation positive-profile neutrality -- Lean formalization certificate

- **Source card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/constitutive-reflection-space-mechanics/split-star-formation-positive-profile-and-functional-fixedness-neutrality-law.md`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/ConstitutivePositiveProfileFormation.lean`
- **Stage:** 3-formalized
- **Date:** 2026-08-14

## Certified declarations

1. `SplitStarFormation` packages a complex star-algebra formation, a complex star-algebra
   recovery, and the left-inverse law.
2. `starReceiverProfile` records all values of one element under all star-algebra maps into a fixed
   receiver.
3. `StarReceiverInvisible` is the corresponding receiver-relative representational radical.
4. `SplitStarFormation.form_injective` proves exact reconstruction implies injective formation.
5. `starReceiverProfile_map_subset` proves arbitrary star-algebra formation can only shrink a
   receiver profile.
6. `SplitStarFormation.starReceiverProfile_form` proves split recovery upgrades that inclusion to
   exact profile equality.
7. `SplitStarFormation.starReceiverInvisible_form_iff` proves exact receiver-radical pullback.
8. `FunctionalSplitStarFormation` packages source and formed involutions plus equivariance.
9. `FunctionalSplitStarFormation.formed_fixed_iff_source_fixed` proves functional-equation
   fixedness is exactly conserved on the formed image.
10. `FunctionalSplitStarFormation.profile_radical_fixedness_neutral` is the joint capstone:
    profile equality, radical equality, and fixed-locus equality hold under one split formation.
11. `starAlgHom_kills_formed_starIsotropic` proves every direct star-algebra formation of a
    star-isotropic source element remains invisible in every positive C-star receiver.

## Exact scope

Lean certifies an unconditional universal theorem for every packaged split-star formation and a
stronger direct-formation no-go for star-isotropic elements. It does not assume RH, an `Xi` zero,
or a route endpoint. It does not construct the constitutive transmutation now required before a
positive conservative divisor realization.

The theorem's receiver is fixed but arbitrary. Quantifying the certified equality over any chosen
family of receivers gives the paper card's global radical-pullback statement.

## Audit

- Direct module check:
  `lake env lean GaloisForLFunctions/HTGeometry/ConstitutivePositiveProfileFormation.lean`
- Final module build:
  `lake build GaloisForLFunctions.HTGeometry.ConstitutivePositiveProfileFormation`
- Umbrella direct check:
  `lake env lean GaloisForLFunctions/HTGeometry/UniversalLawField.lean`
- Standard-only axiom audit for all seven theorem declarations:
  `propext`, `Classical.choice`, `Quot.sound`
- Umbrella import:
  `GaloisForLFunctions.HTGeometry.UniversalLawField`
