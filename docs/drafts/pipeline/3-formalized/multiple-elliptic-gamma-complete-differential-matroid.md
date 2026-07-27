# Complete differential matroid of the generic multiple elliptic gamma hierarchy

- **ID:** `multiple-elliptic-gamma-complete-differential-matroid`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** `all-order-multiple-elliptic-gamma-structural-differential-matroid`
- **Status:** unconditional

## Checked statement

Under upper-half-plane periods, integral independence of `1` and every period, and at least two
periods:

1. all external packets of all faces retaining at least two periods are jointly differentially
   independent;
2. a packet coordinate is differentially algebraic over the embedded rational-coordinate field iff
   its face retains fewer than two periods;
3. every finite constant-coefficient differential-operator output family has differential matroid
   and numerical rank equal to its localized operator-row matroid and row-span dimension.

## Modules

- `formal/GaloisForLFunctions/HTGeometry/MultipleEllipticGammaFacePacketDisjointness.lean`
- `formal/GaloisForLFunctions/HTGeometry/MultipleEllipticGammaAllFaceIndependence.lean`
- `formal/GaloisForLFunctions/HTGeometry/MultipleEllipticGammaCompleteDifferentialMatroid.lean`

## Principal theorems

```text
multipleEllipticGammaFace_translate_ne_of_ne
multipleEllipticGammaProperFacePackets_diffIndepOn
multipleEllipticGammaSelectedFaces_differentialIndependent_rationalBase
multipleEllipticGammaFacePacket_differentialAlgebraic_iff
multipleEllipticGammaCompleteDifferentialMatroid_rationalBase
multipleEllipticGammaCompleteDifferentialRank_rationalBase
```

## Axiom policy

No project axiom, `sorry`, `admit`, `opaque`, or `unsafe` declaration is used in these modules.
