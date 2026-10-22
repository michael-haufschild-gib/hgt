# Prime-support resolution-threshold universality law

## Status

Exact Lean check passed with
`lake env lean GaloisForLFunctions/RHTower/PrimeSupportResolutionThresholdUniversalityLaw.lean`.

## Lean-generated inputs

- `PrimeWordClawFreeConflictNoGo.lean`: support centers of cardinality at most two are claw-free;
  the rank-three word `[0,1,2]` realizes an induced claw.
- `PrimeWordYoungShapeNoGo.lean`: `[0,0,0,1]` and `[0,0,1,1]` have the same two-letter support and
  the same complete scalar boundary germ, but Young shapes `[3,1]` and `[2,2]`.

## Survivor

Prime support has a sharp resolution filtration. Rank two universally suppresses induced claws but
already discards multiplicity under every support-only statistic and the complete scalar boundary
germ. Rank three is the first possible and realized claw threshold. Conflict resolution and Young
multiplicity resolution are therefore independent.

## Formal target

`GaloisForLFunctions.RHTower.PrimeSupportResolutionThresholdUniversalityLaw`

## Novelty audit

Pending post-formalization literature search.
