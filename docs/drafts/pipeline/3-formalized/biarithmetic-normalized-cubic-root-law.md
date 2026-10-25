# Reciprocal-root cubing and purity of every arithmetic survivor

- **ID:** biarithmetic-normalized-cubic-root-law
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Fixed-determinant cubic amplification](biarithmetic-fixed-determinant-cube-amplification.md)
- **Statement:** The operation `z -> z^3/p` preserves a reciprocal pair's product, cubes its normalized roots, and has trace `(T^3-3pT)/p`. For prime `p`, integral traces before and after cubing, and nonnegative second point counts before and after, both original complex roots have norm `sqrt(p)`.

Newton identities give the exact trace and point-count dictionary. The
checked integral classification supplies `T^2<=4p`. For roots `x+iy` and
`z-iy`, reality of their product gives `y(z-x)=0`. A nonzero imaginary
part forces `x=z`; when it vanishes the trace bound forces the same
equality. Both norm squares consequently equal `p`.

Lean: `BiarithmeticGeometry/NormalizedCubicRootLaw.lean`.
Eight audited declarations: `normalizedCubicRoot_product`,
`normalizedCubicRoot_trace`, `normalizedCubicRoot_scaled`,
`normalizedCubicTraceCondition_iff_rootPointCounts`,
`secondPointCount_complex_integral_trace`,
`normalizedCubicTraceCondition_iff_complexRootPointCounts`,
`complex_reciprocal_norm_sq_of_trace_bound`, and
`normalizedCubicRoot_survivor_pure`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/NormalizedCubicRootLaw.lean`.
- [x] Transitive audits use only `propext`, `Classical.choice`, `Quot.sound`; the trace identity needs only `propext`, `Quot.sound`.
- [x] Umbrella import wired; umbrella not compiled.

This closes the specified normalized-cube classification and its positive
survivor. The general bounded-conductor amplification question remains open.
