# Charged scalar core fixed-current torsor — formalization certificate

- **ID:** `charged-scalar-core-fixed-current-torsor`
- **Stage:** 3-formalized
- **Paper proof:**
  `../../2-fully-proven/new_scientific_knowledge/other/charged-scalar-core-fixed-current-torsor.md`
- **Umbrella:** `formal/GaloisForLFunctions/HTGeometry.lean`
- **Status:** `[UNCONDITIONAL LEAN] [NOT RH]`

## Formalized theorem

Lean proves that the logarithmic current of a hypertranscendental charged scalar is itself
hypertranscendental, reconstructs the full differential field from one amplitude over its current
field, identifies the differential automorphism group with the scalar multiplicative group, and
computes finite- and infinite-holonomy fixed fields.  Over the positive finite cover it identifies
the differential Galois group with the corresponding roots-of-unity group.

## Source modules and capstones

```text
formal/GaloisForLFunctions/HTGeometry/StableCoreFunctoriality.lean
formal/GaloisForLFunctions/HTGeometry/ScalarLogCurrentReconstruction.lean
formal/GaloisForLFunctions/HTGeometry/RatFuncScaleFixedField.lean
formal/GaloisForLFunctions/HTGeometry/ScalarDifferentialTorsor.lean
formal/GaloisForLFunctions/HTGeometry/ScalarFiniteDifferentialTorsor.lean

logDeriv_hypertranscendentalOver
differentialAdjoin_eq_logCurrentOrdinaryExtension
scalarDifferentialGaloisGroupEquiv
fixedField_zpowers_derivationPreservingAut_of_finite_order
fixedField_zpowers_derivationPreservingAut_of_infinite_order
scalarFiniteDifferentialGaloisGroupEquiv
```

## Verification and boundary

Serialized direct checks and the `HTGeometry` umbrella build pass.  Combined scratch
`#print axioms` audits use only `propext`, `Classical.choice`, and `Quot.sound`.  No placeholder
axiom or conditional wrapper is used.  The result is the exact scalar differential-torsor theorem;
it is a structural compatibility criterion and makes no RH claim.
