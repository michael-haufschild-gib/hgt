# Suzuki projective affine-secant tensor lift — Lean certificate

- **ID:** `suzuki-projective-affine-secant-tensor-lift-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-projective-affine-secant-tensor-lift.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/HTGeometry/StokesCartanLorentzCapacity.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiAffineSecantSpectralSum.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiProjectiveAffineSecantTensor.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.HTGeometry.StokesCartanLorentzCapacity`:

```text
GaloisForLFunctions.IrregularStokes.FiniteQuadratic.sum_mul_sum
```

`GaloisForLFunctions.RHTower.Suzuki.SuzukiAffineSecantSpectralSum`:

```text
RHTower.offDiag_sum_eq_sub_diag
RHTower.sum_sum_eq_diag_add_offDiag
RHTower.suzukiProjectiveAffineSecant_finite_spectral_sum
```

`GaloisForLFunctions.RHTower.Suzuki.SuzukiProjectiveAffineSecantTensor`:

```text
RHTower.suzukiProjectiveAffineSecantTensor_gauge_covariance
RHTower.suzukiProjectiveAffineSecant_cross_identity
RHTower.suzukiProjectiveAffineSecant_oppositeShift_pair_is_symmetric
RHTower.suzukiProjectiveAffineSecant_quotient_identity
RHTower.suzukiProjectiveAffineSecant_rankOne_recovers_intercept
RHTower.suzukiProjectiveAffineSecant_twoMode_pair_decomposition
RHTower.suzukiProjectiveMinor_affineGauge_invariant
RHTower.suzukiProjectiveMinor_same_affineTensor_different
RHTower.suzukiProjectiveResponse_affineGauge_shift
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 13 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.

## Open gates carried by the paper card

- 3 → 4 publication-ready: standalone note and priority audit

These are research frontier items, not formalization debt.
