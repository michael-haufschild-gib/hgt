# Formation-reporter conservation — Lean certification

- **ID:** ULF-LSM-4
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveFormationReporter`
- **Source:**
  `formal/GaloisForLFunctions/HTGeometry/ConstitutiveFormationReporter.lean`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified declarations

- `FormationReporterInvariant`;
- `FormationReporterCoframeSeparates`;
- `formationReporter_conserved_along_word`;
- `changedJointReporter_forces_infiniteHorizon`;
- `separatingCoframe_forces_identity`;
- `nontrivialFormation_hasReporterResponse`;
- `constitutiveFormationReporterMechanism_closed`.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveFormationReporter.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveFormationReporter
```

Both passed in foreground. `#print axioms` on every significant theorem reports only `propext`,
`Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, project axiom, opaque theorem, unsafe
declaration, or computation proof occurs.

## Field consequence

Finite formation conserves every primitive-natural reporter. Changed saturation charge therefore
certifies non-finite reachability or failed naturality. A complete coframe cannot hide a nontrivial
formation. This is a law of transformation and response, not an inventory of state components.
