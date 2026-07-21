# Formal core of Suzuki's flat finite-shift projective resolvent holonomy

- **ID:** `suzuki-finite-shift-flat-projective-resolvent-holonomy-formal`
- **Status:** formalized and audited
- **Paper theorem:**
  `../../2-fully-proven/new_scientific_knowledge/suzuki-finite-shift-flat-projective-resolvent-holonomy.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/SuzukiFiniteShiftProjectiveHolonomy.lean`
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
- [x] exact `lake build GaloisForLFunctions.RHTower.SuzukiFiniteShiftProjectiveHolonomy`
- [x] global formal lint
- [x] `#print axioms` capstone audit: only `propext`, `Classical.choice`, `Quot.sound`
- [x] `git diff --check`
