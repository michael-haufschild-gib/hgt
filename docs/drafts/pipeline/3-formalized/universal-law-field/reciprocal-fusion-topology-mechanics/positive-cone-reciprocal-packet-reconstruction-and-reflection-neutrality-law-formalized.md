# Positive-cone reciprocal packet reconstruction and reflection neutrality — Lean certification

- **ID:** ULF-RFTM-3A-CERT
- **Paper card:**
  `reciprocal-fusion-topology-mechanics/positive-cone-reciprocal-packet-reconstruction-and-reflection-neutrality-law.md`
- **Lean modules:**
  `GaloisForLFunctions.HTGeometry.ConstitutivePositiveConeMidpointRecovery` and
  `GaloisForLFunctions.HTGeometry.ConstitutivePositiveFormationReflection`
- **Universal-law umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-PROVED] [GLOBAL RECONSTRUCTION] [REFLECTION INFORMATION-NEUTRAL]`
  `[NO RH PREMISE]`

## Certified theorem surface

Lean proves over every finite matrix dimension and every `RCLike` scalar field:

1. `positiveMatrixGeometricMean_posDef` — CFC geometric mean is positive definite.
2. `positiveMatrixGeometricMean_riccati` — it solves `S * X⁻¹ * S = Y`.
3. `positiveMatrixGeometricMean_unique` — it is the unique positive-definite Riccati solution.
4. `positiveFormationPacket_midpoint` — direct/reflected formation has midpoint `R * R`.
5. `positiveFormationRecovery_direct` and `positiveFormationRecovery_reflected` — recovered
   coordinates reconstruct arbitrary positive packet legs exactly.
6. `positiveFormationRecoveryR_formation` and `positiveFormationRecoveryQ_formation` — recovery
   returns both original formation parameters.
7. `positiveMatrixGeometricMean_comm` — packet midpoint is symmetric.
8. `positiveFormationRecoveryR_swap` and `positiveFormationRecoveryQ_swap` — packet exchange fixes
   recovered formation and inverts recovered relative law.
9. `positiveFormationPacketDirect_inverse` and `positiveFormationPacketReflected_inverse` —
   parameter reflection exchanges packet legs.
10. `positiveFormationReflection_informationNeutral` — capstone conjunction certifying exact
    conjugacy of packet exchange and relative-law inversion with no recoverable-coordinate loss.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutivePositiveConeMidpointRecovery.lean
lake env lean GaloisForLFunctions/HTGeometry/ConstitutivePositiveFormationReflection.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutivePositiveConeMidpointRecovery
lake build GaloisForLFunctions.HTGeometry.ConstitutivePositiveFormationReflection
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

All commands passed.  Axiom audit of Riccati uniqueness, midpoint recovery, both packet
reconstruction laws, symmetry, swapped recovery, and capstone reports only `propext`,
`Classical.choice`, and `Quot.sound`.  Scoped forbidden-declaration scan found no `sorry`, `admit`,
`axiom`, `opaque`, or `unsafe`.  No Lean process remained after verification.

The umbrella build replayed unrelated pre-existing lint warnings but built all 11,844 jobs
successfully; neither new module emitted a warning.

## Exact scope

This certificate proves finite-dimensional positive-cone reconstruction and reflection neutrality.
It does not prove real-analyticity of the chart, affine-invariant distance formulas, amplified-orbit
properness, a cofinal infinite-dimensional extension, or RH.  Those claims remain outside this
certificate.
