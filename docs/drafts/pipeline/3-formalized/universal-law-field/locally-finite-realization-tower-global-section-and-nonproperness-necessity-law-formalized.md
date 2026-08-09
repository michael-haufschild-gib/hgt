# Locally finite realization tower — Lean certification

- **ID:** ULF-REG-KONIG-1
- **Paper card:**
  `locally-finite-realization-tower-global-section-and-nonproperness-necessity-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveRealizationKonig`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified declarations

### `constitutiveLocallyFiniteRealizationTower_hasGlobalSection`

For a coherent inverse tower of nonempty realization types, finiteness of the root type and every
one-step extension fibre forces a compatible global section.

### `constitutiveFiniteRealizationTower_hasGlobalSection`

Every coherent inverse tower of nonempty finite realization types has a compatible global section.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveRealizationKonig.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveRealizationKonig
```

Targeted build completed successfully. `#print axioms` lists only `propext`, `Classical.choice`, and
`Quot.sound`. Targeted prohibited-token scan is clean. The later repo-wide lint invocation reached
only unrelated concurrently created unwired modules
`RHTower.BurnolReflectedRawSource`,
`HTGeometry.InterfinityGeometry.MultiTimeRegions`, and
`HTGeometry.InterfinityGeometry.ParametricSmoothness`; this module is wired into its theorem-area
umbrella and contains no computation proof or project postulate.

## Exact field consequence

A coherent locally finite total realization tower cannot witness finite-stage existence with no
set-theoretic global end. Any such law gap must use noncoherence/partiality, nonproperness, or an
additional admission condition not preserved by inverse limits.
