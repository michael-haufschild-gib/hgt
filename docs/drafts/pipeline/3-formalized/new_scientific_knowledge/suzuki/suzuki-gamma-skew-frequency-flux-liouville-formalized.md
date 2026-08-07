# Exact Gamma-skew frequency flux excludes \(L^2\) homogeneous Suzuki seam coronas — Lean certificate

- **ID:** `suzuki-gamma-skew-frequency-flux-liouville-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-gamma-skew-frequency-flux-liouville.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/HTGeometry/SkewFrequencyCurrent.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.HTGeometry.SkewFrequencyCurrent`:

```text
GaloisForLFunctions.HTGeometry.eq_zero_of_integrable_radialCurrent
GaloisForLFunctions.HTGeometry.hasDerivAt_normSq_path
GaloisForLFunctions.HTGeometry.hasDerivAt_radialCurrent
GaloisForLFunctions.HTGeometry.inner_self_im_eq_zero_of_isSelfAdjoint
GaloisForLFunctions.HTGeometry.radialCurrent_const_Ioi
GaloisForLFunctions.HTGeometry.radialCurrent_const_of_hasDerivAt
GaloisForLFunctions.HTGeometry.re_inner_I_smul_isSelfAdjoint_eq_zero
GaloisForLFunctions.HTGeometry.re_inner_real_smul_I_smul_isSelfAdjoint_eq_zero
GaloisForLFunctions.HTGeometry.re_inner_real_smul_self
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 9 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.

## Open gates carried by the paper card

- construct literal completed self-adjoint valuation seam carrier
- prove trace-zero homogeneous component is \(L^2(dL;X)\)
- prove forced Gamma-strip decay \(e^{-\sigma L}\), \(\sigma>1/2\)
- conclude `SUZUKI-TRACE-ZERO-H1`
- prove corona no-return
- prove raw Evans positivity
- RH

These are research frontier items, not formalization debt.
