# Boolean clock-holonomy universality law

## Status

Formalized in Lean and wired into the HTGeometry umbrella. Kept in progress until global
exhaustion and final audit complete.

## Lean sources

- `GaloisForLFunctions.HTGeometry.CoherenceFlatness`
- `GaloisForLFunctions.HTGeometry.ClockCalibrationHolonomy`

## Conjecture

Encode a Boolean edge label as the multiplicative form of its class in `ZMod 2`. Then:

1. multiplicative clock transport along every walk is exactly encoded XOR holonomy;
2. symmetry of the Boolean edge field is exactly enough for reversible clock transport;
3. Boolean flatness is equivalent to group-valued clock flatness; and
4. on a connected graph, Boolean flatness, existence of a Boolean vertex orientation, and
   existence of a global `ZMod 2` clock potential are equivalent.

This identifies projective Boolean coherence as the order-two sector of universal clock
integrability without replacing either existing theory.

## Corpus gap

Search found the Boolean XOR criterion and general group-valued clock criterion but no encoding or
equivalence theorem between them.

## Proof plan

1. Define the injective map `Bool → Multiplicative (ZMod 2)`.
2. Prove it sends XOR to multiplication and `false` to the unit.
3. Induct on walks to identify both holonomies.
4. Transfer reversibility and flatness.
5. Combine the two existing connected-graph exactness criteria.

No numerical experiments or computational evidence are used.

## Lean result

`formal/GaloisForLFunctions/HTGeometry/BooleanClockHolonomyUniversalityLaw.lean` proves:

- `booleanClockValue_xor`;
- `clockWalkTransport_booleanClockCalibration`;
- `booleanClockCalibration_reversible`;
- `booleanEdgeFieldFlat_iff_clockCalibrationFlat`;
- `clockCalibrationExact_booleanClockCalibration_iff_flat`;
- `exists_booleanOrientation_iff_clockCalibrationExact`.

Exact check passed without warnings:

`lake env lean GaloisForLFunctions/HTGeometry/BooleanClockHolonomyUniversalityLaw.lean`

## Novelty status

Post-proof searches found the classical `Z/2` graph cycle-space/coboundary viewpoint and general
clock-model language. Therefore no novelty is claimed for the underlying mathematics. The narrow
corpus-level contribution is the exact Lean connector identifying the repository's Boolean XOR
walk formalism with its multiplicative `ZMod 2` clock-holonomy formalism, including both connected
exactness criteria.
