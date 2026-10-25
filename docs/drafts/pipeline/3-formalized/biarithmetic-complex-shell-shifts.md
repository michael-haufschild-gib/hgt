# Complex shell shifts are an isometric semigroup

- **ID:** biarithmetic-complex-shell-shifts
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Intrinsic golden module](../1-in-progress/biarithmetic-intrinsic-golden-module.md)
- **Statement:** Inserting any finite number of initial zero coordinates defines a continuous complex-linear isometry on normalized shell `ell2`. These shifts compose by addition and the zero shift is the identity.

Remove the finite zero prefix from the squared-norm sum. The remaining
tail is exactly the original sum, proving norm preservation. Explicit
coordinate formulas give linearity and composition, including every
initial boundary case. No bound on an unconstructed operator is assumed.

Lean: `BiarithmeticGeometry/ComplexShellShift.lean`.
Audited declarations: `norm_complexShellShiftVector`,
`norm_complexShellShift_le`, `complexShellShift_comp`, and `complexShellShift_zero`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/ComplexShellShift.lean`.
- [x] All four transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Default proof limits; umbrella import wired; umbrella not compiled.
