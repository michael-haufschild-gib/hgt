# The canonical geometric shell module is the complex line

- **ID:** biarithmetic-geometric-shell-hilbert-module
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Intrinsic golden module](../1-in-progress/biarithmetic-intrinsic-golden-module.md)
- **Statement:** The canonical Hilbert completion of the geometric kernel `K(r,s)=a^(-(r+s))` is isometrically the complex line. Its norm-lattice shift by `r` is multiplication by `a^(-r)`, with exact vector norm and semigroup laws.

The scalar features `e_r=a^(-r)` have the required Gram and `e_0=1`,
so they span the entire scalar line. The corpus's total-feature Gram
isometry identifies the actual kernel completion with that line.
Transporting scalar multiplication supplies the bounded shift, which
sends the canonical vector at `s` to the vector at `r+s`.

Lean: `BiarithmeticGeometry/GeometricShellHilbert.lean`.
Audited declarations: `geometricShellKernel_eq`,
`geometricShellTangentIsometry`, `finrank_geometricShellTangentSpace`,
`geometricShellTangentShift_vector`, `norm_geometricShellTangentShift`,
and `geometricShellTangentShift_comp`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/GeometricShellHilbert.lean`.
- [x] All six transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Umbrella import wired; umbrella not compiled.

The algebraic kernel is defined for every real `a`, using Lean's inverse
convention at zero. Its identification with actual intrinsic golden source
tangents still requires the separate source limit theorem.
