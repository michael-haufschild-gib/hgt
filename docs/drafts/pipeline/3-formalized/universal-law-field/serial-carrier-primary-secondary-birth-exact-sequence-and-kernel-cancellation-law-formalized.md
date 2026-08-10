# Serial-carrier primary--secondary birth exact sequence and kernel-cancellation law — formalized

- **ID:** ULF-PSB-1
- **Stage:** 3-formalized
- **Paper:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/serial-carrier-primary-secondary-birth-exact-sequence-and-kernel-cancellation-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveCarrierComposition`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-CERTIFIED] [FORMAL-LINT PASS] [UMBRELLA-BUILT] [AXIOM-AUDITED]

## Certified declarations

| paper clause | Lean declaration |
|---|---|
| primary and composite zero criteria | `outerCarrierObstruction_eq_zero_iff`, `compositeCarrierObstruction_eq_zero_iff` |
| canonical secondary obstruction | `secondaryCarrierObstruction`, `secondaryCarrierObstruction_eq_zero_iff` |
| composite birth iff secondary vanishing | `compositeCarrierObstruction_eq_zero_iff_secondary` |
| independence of chosen outer lift | `secondaryCarrierObstruction_independent` |
| exclusive primary/completed/secondary phases | `serialCarrierBirth_phase_trichotomy` |
| canonical injection | `secondaryToComposite`, `secondaryToComposite_injective` |
| exactness in the middle | `range_secondaryToComposite_eq_ker_compositeToOuter` |
| quotient-transition surjectivity | `compositeToOuter_surjective` |
| short exact sequence | `carrierComposition_short_exact` |
| outer-kernel cancellation laboratory | `sumCarrier_kernel_cancels_vertical`, `sumCarrier_secondary_obstruction_zero` |
| genuine secondary failure laboratory | `secondCarrier_primary_obstruction_zero`, `secondCarrier_secondary_obstruction_nonzero` |
| dual-laboratory capstone | `serialCarrierBirthMechanism_closed` |

## Verification

Commands run in foreground, one process at a time:

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveCarrierComposition.lean
python3 scripts/formal_tools.py lint
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Final build: `11,542` jobs, success. New module builds cleanly. Build log contains only pre-existing
warnings in unrelated modules.

Source-level axiom audit:

```text
compositeCarrierObstruction_eq_zero_iff_secondary
secondaryCarrierObstruction_independent
carrierComposition_short_exact
serialCarrierBirth_phase_trichotomy
serialCarrierBirthMechanism_closed
```

Each reports only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, `axiom`,
`opaque`, `unsafe`, or computation-backed proof is used.
