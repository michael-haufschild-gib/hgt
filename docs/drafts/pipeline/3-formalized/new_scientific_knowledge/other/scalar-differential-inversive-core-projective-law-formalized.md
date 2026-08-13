# Scalar differential inversive-core projective law — formalization certificate

- **ID:** `scalar-differential-inversive-core-projective-law`
- **Stage:** 3-formalized
- **Paper proof:**
  `scalar-differential-inversive-core-projective-law.md`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/ScalarDifferentialInversiveCoreProjectiveLaw.lean`
- **Umbrella:** `formal/GaloisForLFunctions/HTGeometry.lean`
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NOT RH]`

## Formalized theorem

For every derivation-preserving endomorphism of the canonical scalar free differential rational
field over a characteristic-zero constant field, Lean proves an exclusive dichotomy:

1. its stable range core is exactly the base field; or
2. the stable core has a hypertranscendental generator `u`, the endomorphism acts on `u` by a
   nondegenerate fractional-linear transformation over the base, and every other nondegenerate
   coefficient quadruple for that action is the same quadruple multiplied by one nonzero scalar.

Capstones:

```text
GaloisForLFunctions.HTGeometry.map_stableRangeCore_self
GaloisForLFunctions.HTGeometry.scalarDifferentialInversiveCore_projectiveLaw
GaloisForLFunctions.HTGeometry.freeScalarDifferentialInversiveCore_projectiveLaw
```

The closed canonical capstone has only the endomorphism and its defining derivation-compatibility
law as inputs.  Constant-base behavior, differential independence of the source, and generation of
the whole free field are constructed internally from `JetField`.  The general assembly theorem
uses the unrestricted differential Lüroth theorem already proved in
`DifferentialLurothSingleGenerator`, stable-core surjectivity from `StableDifferentialCore`, and
mutual-generator projective rigidity from `MutualGeneratorMobius`.

## Verification

- Direct `lake env lean` check passes for the owning module.
- Targeted final build passes:
  `lake build GaloisForLFunctions.HTGeometry.ScalarDifferentialInversiveCoreProjectiveLaw`.
- Scratch `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for all three
  capstones.
- Module is imported by the `HTGeometry` umbrella.
- Targeted audit finds no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
