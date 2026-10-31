# Positive unipotent loops are the exact Borel torus kernel

- **Stage:** 3-formalized
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** The positive unipotent subgroup is exactly the kernel of
  both intrinsic Borel torus coordinates. Coefficient-field maps preserve
  and reflect this subgroup.

## Proof

Unique Borel factors are a central unit and an Iwahori matrix. The torus
coordinates are the central unit and the constant upper-left Iwahori entry.
Both are one exactly when the central factor is trivial and the Iwahori
matrix is positive unipotent, by the proved finite-coordinate kernel law.

A field map preserves the three defining unipotent constant entries.
For reflection, first reflect Borel membership. Naturality of its two
torus coordinates and injectivity of the coefficient-field map then reflect
their equality to one. The kernel characterization finishes the proof.

## Lean

`HTGeometry/LoopEisenstein/PositiveUnipotentFieldMap.lean`:
`borelTorusHom_eq_one_iff`, `fieldMap_mem_positiveUnipotent_iff`.
Direct Lean check passed; both axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
