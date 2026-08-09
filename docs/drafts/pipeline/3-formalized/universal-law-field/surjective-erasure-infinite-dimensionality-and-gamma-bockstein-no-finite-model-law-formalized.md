# Surjective erasure and Gamma-Bockstein no-finite-model law — Lean certification

- **ID:** ULF-REG-SEID-1
- **Paper card:**
  `surjective-erasure-infinite-dimensionality-and-gamma-bockstein-no-finite-model-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveSurjectiveErasure`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified declarations

### `constitutiveSurjectiveErasure_not_finiteDimensional`

A surjective linear endomorphism of one carrier that kills a nonzero vector forces failure of
finite dimensionality.

### `constitutiveGammaCorona_not_finiteDimensional_of_bockstein_death`

Every genuine fixed-corona Gamma-Bockstein death event forces the literal corona carrier to be
infinite-dimensional.

### `constitutiveGammaCorona_not_finiteDimensional`

The fixed prime corona supporting the certified Gamma-Bockstein lifetime is not finite-dimensional.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveSurjectiveErasure.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveSurjectiveErasure
```

Targeted build completed successfully. `#print axioms` lists only `propext`, `Classical.choice`, and
`Quot.sound`. The module is imported by the dedicated universal-law-field umbrella. No computation
proof or project postulate is used.

## Exact field consequence

Finite-dimensional exactifications cannot preserve both same-carrier surjectivity and nonzero
Gamma-Bockstein class death. Any faithful universal realization must retain an infinite carrier or
change the admission/topological doctrine at the death wall.
