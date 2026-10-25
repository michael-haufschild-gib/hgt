# Uniform energy of centered intrinsic point kernels

- **ID:** biarithmetic-intrinsic-point-kernel-energy
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Intrinsic golden module](../1-in-progress/biarithmetic-intrinsic-golden-module.md)
- **Statement:** The centered actual intrinsic point response at norm `5^r` has an exact affine tail and finite weighted square energy, with total energy at most `6·5^(-r)`.

Centering cancels the exponential counting term. The remaining tail is
bounded by `s+1`; its square is dominated by `4^s`, giving a geometric
tail-energy bound. The finite head contributes at most `5^(-r)/4`.

Lean: `BiarithmeticGeometry/IntrinsicPointKernelEnergy.lean`.
Audited declarations: `goldenIntrinsicPointReceiver_tail`,
`abs_goldenIntrinsicPointReceiver_tail_le`,
`summable_goldenIntrinsicPointReceiver_energy`, and
`tsum_goldenIntrinsicPointReceiver_energy_le`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/IntrinsicPointKernelEnergy.lean`.
- [x] All four transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Default proof limits; umbrella import wired; umbrella not compiled.

Wiener synthesis and the complete intrinsic paid-domain classification
remain separate formalization obligations.
