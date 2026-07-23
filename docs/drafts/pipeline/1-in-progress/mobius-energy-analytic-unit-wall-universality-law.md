# Möbius energy/analytic-unit wall universality law

## Status

Lean-formalized; exact file audit passed. Literature novelty audit pending.

## Corpus sources

- `RHTower/MobiusLaplaceMellinPlancherelBridge.lean`
- `RHTower/MobiusLiouvilleSquareDilationWall.lean`
- `RHTower/MobiusLaplaceCriterionFrontier.lean`

## Theorem-first derivation

Strict-right logarithmic energy constructs the canonical Möbius Mellin wall. A separate theorem
shows that multiplication by any analytic nowhere-zero target factor preserves that wall. Their
composition supplies every analytic-unit twisted wall from the same energy source.

## Universal law

Every strict-right energy certificate produces every analytic-unit twisted wall. This specializes
to the Liouville square-dilation unit `ζ(2s)` and propagates further from cofinal energy. Under the
classical RH-to-strict-half-power-decay converse, energy is equivalent to every such twisted wall.

## Lean status

- Module: `GaloisForLFunctions.RHTower.MobiusEnergyAnalyticUnitWallUniversalityLaw`
- Capstone: `RHTower.mobiusLaplaceStrictRightEnergyFinite_iff_liouvilleSquareDilationWall_of_decay`
- Exact check: `lake env lean GaloisForLFunctions/RHTower/MobiusEnergyAnalyticUnitWallUniversalityLaw.lean`

## Novelty

Pending primary-source literature search after corpus discovery reaches exhaustion.
