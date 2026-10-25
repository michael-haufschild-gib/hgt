# Integral traces surviving normalized cubic amplification

- **ID:** biarithmetic-normalized-cubic-trace
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Fixed-determinant cubic amplification](../1-in-progress/biarithmetic-fixed-determinant-cube-amplification.md)
- **Statement:** For a prime `p`, integral traces satisfying `pU=T^3-3pT` and both bounds `T^2,U^2<=(p+1)^2` have `T=U=0` when `p>=5`. The remaining nonzero cases are `(p,T,U)=(2,2,-2),(2,-2,2),(3,3,0),(3,-3,0)`.

Prime divisibility first gives `p|T`. The first square bound reduces
the trace to `0,p,-p`; the second excludes the nonzero choices above
prime three. Every surviving trace satisfies `T^2<=4p`, and the
transformed integral trace is unique.

Lean: `BiarithmeticGeometry/NormalizedCubicTrace.lean`.
Audited declarations: `prime_dvd_of_integral_normalizedCube`,
`normalizedCubicTrace_eq_zero_of_five_le`, `exists_normalizedCubicTrace_iff`,
`normalizedCubicTrace_pure_bound`, and `normalizedCubicTrace_unique`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/NormalizedCubicTrace.lean`.
- [x] All five transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`; uniqueness uses only `propext`.
- [x] Umbrella import wired; umbrella not compiled.

The general complex-root comparison and the forced purity of the
surviving roots are separate pending obligations. Fixed determinant
does not define analytic conductor.
