# Summable-compensator essential phase and reciprocal selection law — formalized

- **Paper source:** `docs/drafts/pipeline/2-fully-proven/universal-law-field/essential-formation-mechanics/summable-compensator-essential-phase-and-reciprocal-selection-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveEssentialFormationMechanics`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-PROVED] [NO SORRY] [NO PROJECT-ADDED AXIOMS]

## Certified declarations

- `essentialFormationEquivalent_refl`
- `essentialFormationEquivalent_symm`
- `essentialFormationEquivalent_trans`
- `summable_iff_of_essentialFormationEquivalent`
- `essentialFormationEquivalent_of_finiteSupport`
- `primeInteractionEssentialReflection_iff`
- `not_primeInteractionEssentialReflection_of_ne`
- `no_summable_compensator_primeInteractionReflection`
- `essentialFormationSelection_of_sourceBridge`

Lean certifies that summable-work equivalence is an equivalence relation, preserves the global
formation phase, erases every finite-support correction, and identifies the prime interaction
formation with its reciprocal reflection exactly at exponent one.  Off criticality, no summable
formation compensator can repair the mismatch.
The global bridge consumer further proves that source-to-prime shadow errors and source-duality
error need only be summable; composing those three essential bridges already forces exponent one.

## Verification

- direct foreground elaboration passed;
- leaf build passed: 2,351 jobs;
- ULF umbrella build passed: 11,832 jobs;
- axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

The global essential-duality producer theorem and its landing on Xi spectral states remain open and
are not represented by this certificate.
