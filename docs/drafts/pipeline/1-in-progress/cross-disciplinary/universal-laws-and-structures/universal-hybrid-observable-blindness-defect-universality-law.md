# Universal hybrid observable-blindness defect universality law

## Status

In progress — paper proof and Lean formalization complete; literature novelty audit pending.

## Theorem-first provenance

- `HTGeometry/UniversalOrientedObservableGaugeBlindness.lean`
  - `universalFacetOrbitOrientedSource_familyObservableField_eq`
  - `universalOrientationIndex_sameObservableField_while_Herglotz_iff_zero`
- `HTGeometry/UniversalPrimeObservableDephasingGeometry.lean`
  - `universalFacetOrbitPrimeOrientedSource_familyObservableField_eq`
  - `universalPrimeChamber_sameObservableField_while_Herglotz_iff_energy_zero`
- `HTGeometry/UniversalPrimeKreinHamming.lean`
  - `primeChamberDephasingMasterEnergy_eq_hamming`
  - `primeChamberDephasingMasterEnergy_eq_zero_iff`

## Universal law

One finite differential observable field is simultaneously blind to an integer orientation chamber
and a finite prime-residue chamber. Their joint nonnegative defect is the real orientation index
plus prime-chamber Hamming distance. It vanishes exactly when both analytic Herglotz channels are
positive, so one scalar restores the all-positive chamber lost by the common field.

## Lean status

Formalized in
`formal/GaloisForLFunctions/HTGeometry/UniversalHybridObservableBlindnessDefectUniversalityLaw.lean`.

Exact check:

```text
lake env lean GaloisForLFunctions/HTGeometry/UniversalHybridObservableBlindnessDefectUniversalityLaw.lean
```

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only.
