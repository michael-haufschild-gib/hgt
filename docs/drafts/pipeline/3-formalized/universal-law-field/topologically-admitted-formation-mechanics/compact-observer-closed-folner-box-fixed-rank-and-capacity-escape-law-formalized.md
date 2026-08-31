# Compact observer-closed Følner boxes, fixed-rank selection, and capacity escape -- Lean certification

- **Paper theorem:** ULF-TAFM-11
- **Lean module:** `GaloisForLFunctions.HTGeometry.CompactFormationFolnerRankEscape`
- **Status:** formalized

## Certified content

The module proves:

1. simultaneous cofinally large compact return for every coordinate of a fixed finite phase
   palette, using one common width;
2. exact inverse-rank lower bound on local edge-current capacity from the box current law;
3. beyond every threshold, an observer-closed box whose capacity pays at least
   `n * |chi| / (2*d)`; and
4. fixed-rank compact-phase box formation with one uniform local capacity forces zero bulk
   character.

The fusion is generic. No Xi zero, RH hypothesis, dense orbit, continuous potential, common gauge,
or arithmetic packet is assumed.

## Verification

- Scratch elaboration -- pass.
- Project-path elaboration -- pass.
- Final targeted leaf audit:
  `lake build GaloisForLFunctions.HTGeometry.CompactFormationFolnerRankEscape` -- pass
  (`1676/1676`).
- Batched scratch `#print axioms` on all four significant declarations reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Module is imported by `HTGeometry.UniversalLawField`; umbrella is not built.

No full project, theorem-area, or umbrella build was run.

## Selection boundary

Compact recurrence automatically supplies observer closure for every fixed finite palette. Hence a
nonzero bulk grade cannot survive fixed rank, local Stokes formation, and bounded elementary
current simultaneously. Survival requires rank at width scale, cofinal linear capacity escape,
nonlocal production, or failure of legal box formation. Literal divisor-independent arithmetic
packets and the rank/capacity comparison remain the RH-bearing producer.
