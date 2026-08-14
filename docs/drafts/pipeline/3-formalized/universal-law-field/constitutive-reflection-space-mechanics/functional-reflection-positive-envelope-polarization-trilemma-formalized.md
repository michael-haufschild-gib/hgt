# Functional-reflection positive envelope -- Lean formalization certificate

- **Source card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/constitutive-reflection-space-mechanics/functional-reflection-positive-envelope-polarization-trilemma.md`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/ConstitutiveFunctionalReflectionPositiveEnvelope.lean`
- **Stage:** 3-formalized
- **Date:** 2026-08-14

## Certified declarations

1. `FunctionalReflection` packages an involution on a finite source set.
2. `ReflectedFunction` carries the twisted adjoint
   `star f x = star (f (r.act x))`, with closed `InvolutiveStar`, `StarRing`, and `StarModule`
   instances.
3. `star_atom` and `star_atom_mul_self` prove every nonfixed atom is star-isotropic.
4. `restrictFixed` is the star-algebra restriction to `FixedPoint r`; `extendFixed` and
   `restrictFixed_surjective` prove surjectivity, including the empty fixed-locus case.
5. `receiver_kills_restrictKernel` proves every star-algebra map into an arbitrary positive
   `CStarRing` kills the full fixed-restriction kernel.
6. `factorReceiver`, `factorReceiver_comp_restrictFixed`, `factorReceiver_unique`, and
   `receiver_factors_uniquely` prove the fixed-locus receiver is universal.
7. `positiveCharacter_unique_fixedPoint` proves every positive character is evaluation at one
   unique fixed point. Its existence therefore also forces a nonempty fixed locus.
8. `invisible_fixedReceiver_iff` identifies the exact positive radical with the restriction
   kernel.
9. `injective_receiver_forces_fixed` and `faithful_positive_receiver_iff` prove a faithful
   positive receiver exists exactly when the functional reflection is trivial.
10. `standardReflection` and `standardReflection_atom` prove positive-dagger untwisting retains
    every atom and moves reflection into a separate involutive star-algebra automorphism.

## Exact field consequence

Common recovery and functional-equation lifting are information-neutral, but identifying the
functional equation with the physical adjoint is not: positivity then performs the universal
quotient to the fixed locus.  The missing selection mechanism must therefore generate and
transport an admissible polarization; it cannot be another direct recovered packet lift.

## Audit

- Direct check:
  `lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveFunctionalReflectionPositiveEnvelope.lean`
- Final umbrella build:
  `lake build GaloisForLFunctions.HTGeometry.UniversalLawField`
- Build result: `11891` jobs completed successfully.
- Axiom audit on factorization, character classification, radical, faithfulness, and untwisting:
  `propext`, `Classical.choice`, `Quot.sound` only.
- Formal lint: passed with no output.
- Umbrella import:
  `GaloisForLFunctions.HTGeometry.UniversalLawField`
