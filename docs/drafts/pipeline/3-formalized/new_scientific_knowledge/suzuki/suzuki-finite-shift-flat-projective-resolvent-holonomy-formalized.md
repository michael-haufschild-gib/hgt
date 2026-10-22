# Suzuki finite shifts carry a flat projective resolvent holonomy — Lean certificate

- **ID:** `suzuki-finite-shift-flat-projective-resolvent-holonomy-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-finite-shift-flat-projective-resolvent-holonomy.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/HTGeometry/CompactFourierEntire.lean`
- `formal/GaloisForLFunctions/HTGeometry/CompactFourierSineKernel.lean`
- `formal/GaloisForLFunctions/HTGeometry/ResolventFamilyJet.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiFiniteShiftProjectiveHolonomy.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiDonoghueHerglotzTransform.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.HTGeometry.CompactFourierEntire`:

```text
GaloisForLFunctions.HTGeometry.hasDerivAt_compactFourier
```

`GaloisForLFunctions.HTGeometry.CompactFourierSineKernel`:

```text
GaloisForLFunctions.HTGeometry.abs_le_of_mem_uIoc_symm
GaloisForLFunctions.HTGeometry.continuous_mul_fourierKernel
GaloisForLFunctions.HTGeometry.hasDerivAt_compactFourier_of_amplitude
GaloisForLFunctions.HTGeometry.hasDerivAt_mul_fourierKernel
GaloisForLFunctions.HTGeometry.intervalIntegrable_mul_fourierKernel
GaloisForLFunctions.HTGeometry.norm_fourierKernel
GaloisForLFunctions.HTGeometry.norm_fourierKernel_le
GaloisForLFunctions.HTGeometry.norm_mul_fourierKernel_le
```

`GaloisForLFunctions.HTGeometry.ResolventFamilyJet`:

```text
GaloisForLFunctions.HTGeometry.IsResolventFamilyOn
GaloisForLFunctions.HTGeometry.IsResolventFamilyOn.continuousAt
GaloisForLFunctions.HTGeometry.IsResolventFamilyOn.eventually_small_of_nhds
GaloisForLFunctions.HTGeometry.IsResolventFamilyOn.hasDerivAt
GaloisForLFunctions.HTGeometry.IsResolventFamilyOn.hasDerivAt_jet
GaloisForLFunctions.HTGeometry.IsResolventFamilyOn.norm_le_two_mul
GaloisForLFunctions.HTGeometry.IsResolventFamilyOn.norm_pow_le_of_small
GaloisForLFunctions.HTGeometry.IsResolventFamilyOn.norm_sq_le_four_mul
GaloisForLFunctions.HTGeometry.IsResolventFamilyOn.norm_sub_le
GaloisForLFunctions.HTGeometry.aeval_eq_resolventShiftJet_sum
GaloisForLFunctions.HTGeometry.hasDerivAt_resolventShiftJet
GaloisForLFunctions.HTGeometry.resolventShiftJet
```

`GaloisForLFunctions.RHTower.Suzuki.SuzukiFiniteShiftProjectiveHolonomy`:

```text
GaloisForLFunctions.RHTower.conj_suzukiLogarithmicSourceGenerator_eq_neg
GaloisForLFunctions.RHTower.hasDerivAt_reflectedQuotientCarrier
GaloisForLFunctions.RHTower.suzukiClarkTransport_im_eq_zero
GaloisForLFunctions.RHTower.suzukiFiniteShiftSource
GaloisForLFunctions.RHTower.suzukiFiniteShiftSource_cross
GaloisForLFunctions.RHTower.suzukiFourierLivsic_eq_transport_mul
GaloisForLFunctions.RHTower.suzukiFourierLivsic_finiteShift_sub
GaloisForLFunctions.RHTower.suzukiImplicitPoleVelocity_eq_clarkTransport
GaloisForLFunctions.RHTower.suzukiLogarithmicSourceGenerator
GaloisForLFunctions.RHTower.suzukiLogarithmicSourceGenerator_eq_neg_reflectionTangent
GaloisForLFunctions.RHTower.suzukiLogarithmicSourceGenerator_re_eq_zero
GaloisForLFunctions.RHTower.suzukiProjectiveSourceTransport
GaloisForLFunctions.RHTower.suzukiProjectiveSourceTransport_comp
GaloisForLFunctions.RHTower.suzukiProjectiveSourceTransport_finiteShift_sub_one
GaloisForLFunctions.RHTower.suzukiProjectiveSourceTransport_path_independent
GaloisForLFunctions.RHTower.suzukiProjectiveSourceTransport_self
GaloisForLFunctions.RHTower.suzukiReflectedQuotientDifference_eq_crossWronskian
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 38 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.

---

## Earlier certificate (merged from the flat stage-3 companion)

# Formal core of Suzuki's flat finite-shift projective resolvent holonomy

- **ID:** `suzuki-finite-shift-flat-projective-resolvent-holonomy-formal`
- **Status:** formalized and audited
- **Paper theorem:**
  `./suzuki-finite-shift-flat-projective-resolvent-holonomy.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiFiniteShiftProjectiveHolonomy.lean`
- **RH used:** no
- **Computation used:** no

## Formalized content

The module defines the reflected endpoint transport

```text
suzukiProjectiveSourceTransport F1 F0 z
 =F1(z)F0(-z)/(F1(-z)F0(z))
```

and proves:

- identity transport and exact composition through every nonvanishing intermediate source;
- equality of holonomy along two different finite source paths with common endpoints;
- exact factorization of a finite update's reflected cross determinant;
- exact transport and finite divided-difference laws for Suzuki's Fourier--Livšic carrier;
- identification of the logarithmic source generator with the normalized reflected tangent;
- anti-reality of that generator for real reflected Fourier sources;
- equality between implicit simple-pole velocity and Clark-atom transport, including reality.

## Source-specific capstones

```text
suzukiProjectiveSourceTransport_comp
suzukiProjectiveSourceTransport_path_independent
suzukiFiniteShiftSource_cross
suzukiProjectiveSourceTransport_finiteShift_sub_one
suzukiFourierLivsic_eq_transport_mul
suzukiFourierLivsic_finiteShift_sub
suzukiFourierLivsic_finiteShift_dividedDifference
suzukiLogarithmicSourceGenerator_eq_neg_reflectionTangent
conj_suzukiLogarithmicSourceGenerator_eq_neg
suzukiImplicitPoleVelocity_eq_clarkTransport
suzukiClarkTransport_im_eq_zero
```

## Boundary of the formal layer

The formal module consumes the exact transform update `F_s=F_r+delta J` as algebraic data.  The
second resolvent identity for Suzuki's unbounded Friedrichs operator, Fourier transformation of
its two-resolvent source, and differentiability in the shift remain paper-level because the
concrete operator is not yet represented in Lean.

## Audit

- [x] direct `lake env lean` source check
- [x] exact `lake build GaloisForLFunctions.RHTower.Suzuki.SuzukiFiniteShiftProjectiveHolonomy`
- [x] global formal lint
- [x] `#print axioms` capstone audit: only `propext`, `Classical.choice`, `Quot.sound`
- [x] `git diff --check`
