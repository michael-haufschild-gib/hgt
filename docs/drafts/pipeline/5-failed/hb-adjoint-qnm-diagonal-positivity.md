# HB adjoint-QNM diagonal positivity route

- **ID:** HB-ADJOINT-QNM-DIAGONAL-POSITIVITY
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Statement:** Derive the missing nonnegative HB full-cokernel sign from positivity of a diagonal adjoint-QNM period.

## Exact killing theorem/mechanism

Killed as an exhaustive diagonal dichotomy.

- For the physical complex-bilinear Teukolsky/QNM adjoint form, `B(zx,zx)=z²B(x,x)`.  In particular `B(Ix,Ix)=-B(x,x)`, so a diagonal value invariant under common source phase is zero.  Any fixed nonzero calibration making all diagonal values real and nonnegative annihilates every diagonal; symmetry annihilates the whole form.
- Replacing the pairing by a Hermitian/KMS diagonal restores phase invariance but falls under the existing finite-KMS polarity theorem: it produces the already-known nonpositive HB orbit, while the needed opposite sign is pointwise criticality and globally RH.

Lean certificate: `d4HBAdjointQNMDiagonalPositivityRouteKilled` in `ThetaCuspHawkingHBAdjointQNMComplexBilinearPositivityNoGo.lean`.

## Strongest positive survivor

Exact weight-two covariance `B(zx,zx)=z²B(x,x)`.  A nonzero adjoint-QNM period must remain a charged object, or be polarized off diagonal with independently transforming source and left-QNM legs.  It cannot be interpreted as a positive scalar energy on the projective source ray.

## Consequence for RH chain

The discarded chain was

`diagonal adjoint-period positivity -> nonnegative full-cokernel orbit -> orbit extinction -> source-FE unit-clock covariance -> RH`.

For the actual HB orbit, existence of projectively descended complex-bilinear diagonal landing is now proved equivalent to the critical wall fibrewise and to RH globally.  It is a receiver, not an independent producer.  Remaining HB work must derive a genuinely off-diagonal phase-sensitive Einstein--Teukolsky/source law.

## Verification

- Direct `lake env lean` check: PASS.
- Targeted `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingHBAdjointQNMComplexBilinearPositivityNoGo`: PASS.
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella wired.  Global lint reports only unrelated concurrently unwired modules; this module is reachable.
