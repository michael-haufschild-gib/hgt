# Cesàro iterated-log frontier

- **ID:** cesaro-iterated-log-frontier
- **Stage:** 3-formalized
- **Type:** BOUNDARY THEOREM (paper + Lean)
- **Source:** `squarefree-convolution-half-cesaro-source-criterion.md`
- **Status:** `[PROVED HERE] [LEAN-PROVED] [NOT RH] [BOUNDEDNESS OPEN]`

## Statement

The canonical cofinal `iteratedLogarithmicCayleySchedule` does not satisfy
`CesaroPoleScheduleFast`. Therefore the general fast-schedule no-go cannot refute its scheduled
Cesàro family. If that family is locally bounded on `rightHalf`, then `RHLadder 1` follows.

## Proof boundary

The existing schedule estimate makes every fixed-base amplification eventually at most
`N^(6/11)`. If fastness held, the same amplification would dominate `N/B`. Standard domination of
`N^(6/11)` by `N` then yields `2N≤N` for a positive natural cutoff, contradiction.

This theorem proves only separation from a no-go class. It supplies no bound on the Cesàro family.

## Lean formalization

Module:
`formal/GaloisForLFunctions/RHTower/SquarefreeConvolutionHalfCesaroIteratedLogFrontier.lean`.

Main theorems:

- `not_cesaroPoleScheduleFast_iteratedLogarithmicCayleySchedule`;
- `rhLadder_one_of_iteratedLogarithmicCesaroSchedule_locallyBounded`.

Verification on 2026-09-04: direct check pass; targeted build `13041/13041`; axiom audits only
`propext`, `Classical.choice`, `Quot.sound`; umbrella import wired.

## Exact open obligation

Prove or refute `PoleClearedFirstTraceCesaroScheduledLocallyBounded
iteratedLogarithmicCayleySchedule`. Pointwise boundedness would not prove the positive direction;
one-point unboundedness would prove the negative direction.
