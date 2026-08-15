# Real-axis kernel positivity nonselector — Lean certificate

- **ID:** `real-axis-kernel-positivity-nonselector-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `real-axis-kernel-positivity-nonselector.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Lean module

`GaloisForLFunctions.HTGeometry.RealAxisKernelPositivityNonselector`
(umbrella: `GaloisForLFunctions.HTGeometry`).

## Exact certificate

`realAxisKernelPositivityNonselectorCertificate` packages the literal real
Hermitian inverse form `H`, its inverse `G`, negative index `2`, and the
identity

```text
e(t)^* H⁻¹ e(t) = 1 + t² + t⁴ > 0
```

for every real `t`.  `realAxisKernel_hidden_negative_quadratic` simultaneously
exhibits the off-curve vector with quadratic value `-1/3`.  Thus positivity on
the whole real evaluation curve is proved without assuming positivity of the
form.

## Verification

- Direct source check: `lake env lean GaloisForLFunctions/HTGeometry/RealAxisKernelPositivityNonselector.lean`.
- Targeted leaf build: `lake build GaloisForLFunctions.HTGeometry.RealAxisKernelPositivityNonselector`.
- Axiom audit: `[propext, Classical.choice, Quot.sound]` only.
